//! The operational semantics: a small-step interpreter over a store.
//!
//! A configuration is a store `S` and a term `e`. The store maps locations
//! `ℓ` to a value and a *loan state*: not lent, lent shared, or lent mutably.
//! Every step that touches memory checks a guard on the loan state. A step
//! whose guard fails leaves the machine **stuck**: that is what "going wrong"
//! means for this calculus, and what the type system rules out.

use std::collections::BTreeMap;
use std::fmt;

use crate::syntax::{BorrowKind, Ptr, Term};

// ANCHOR: store
/// The loan state of a location.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Loan {
    /// Not borrowed: the owner may be borrowed, dropped or moved.
    None,
    /// Lent through a shared borrow: readable through `shr ℓ`.
    Shared,
    /// Lent through a mutable borrow: writable through `uniq ℓ`.
    Mut,
}

/// One store location: its value and its loan state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cell {
    pub value: Term,
    pub loan: Loan,
}

/// The store: a finite map from locations to cells.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Store {
    cells: BTreeMap<usize, Cell>,
    next: usize,
}
// ANCHOR_END: store

/// Why the machine cannot take a step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stuck {
    /// The term the machine was trying to reduce.
    pub redex: String,
    pub reason: String,
}

impl fmt::Display for Stuck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "stuck at `{}`:\n  {}", self.redex, self.reason)
    }
}

impl Store {
    fn alloc(&mut self, value: Term) -> usize {
        let l = self.next;
        self.next += 1;
        self.cells.insert(
            l,
            Cell {
                value,
                loan: Loan::None,
            },
        );
        l
    }

    /// The cell at `ℓ`, or the use-after-free that accessing it would be.
    fn cell(&mut self, l: usize, redex: &Term) -> Result<&mut Cell, Stuck> {
        self.cells.get_mut(&l).ok_or_else(|| Stuck {
            redex: redex.summary(),
            reason: format!("ℓ{l} has been freed (use after free)"),
        })
    }

    /// Free everything a value owns: the locations of its `own ℓ` pointers,
    /// and recursively what they contain. Guard: none of them is lent.
    fn free(&mut self, v: &Term, redex: &Term) -> Result<(), Stuck> {
        match v {
            Term::Pair(a, b) => {
                self.free(a, redex)?;
                self.free(b, redex)
            }
            Term::Ptr(Ptr::Own, l) => {
                let Some(cell) = self.cells.remove(l) else {
                    let reason = format!("ℓ{l} has already been freed (double free)");
                    return Err(Stuck {
                        redex: redex.summary(),
                        reason,
                    });
                };
                if cell.loan != Loan::None {
                    let reason =
                        format!("ℓ{l} is still lent ({}): cannot free it", cell.loan);
                    return Err(Stuck {
                        redex: redex.summary(),
                        reason,
                    });
                }
                self.free(&cell.value, redex)
            }
            _ => Ok(()),
        }
    }
}

impl fmt::Display for Loan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Loan::None => write!(f, "not lent"),
            Loan::Shared => write!(f, "lent shared"),
            Loan::Mut => write!(f, "lent mut"),
        }
    }
}

impl fmt::Display for Store {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.cells.is_empty() {
            return write!(f, "∅");
        }
        for (i, (l, cell)) in self.cells.iter().enumerate() {
            let sep = if i == 0 { "" } else { ", " };
            let loan = match cell.loan {
                Loan::None => "",
                Loan::Shared => " [shared]",
                Loan::Mut => " [mut]",
            };
            write!(f, "{sep}ℓ{l} ↦ {}{loan}", cell.value)?;
        }
        Ok(())
    }
}

/// Substitute the closed value `v` for the free occurrences of `x` in `e`.
/// Values contain no variables, so no variable capture can happen.
pub fn subst(e: &Term, x: &str, v: &Term) -> Term {
    let go = |t: &Term| Box::new(subst(t, x, v));
    match e {
        Term::Var(y) if y == x => v.clone(),
        Term::Var(_) | Term::Lit(_) | Term::Unit | Term::Ptr(..) => e.clone(),
        Term::Pair(a, b) => Term::Pair(go(a), go(b)),
        Term::Assign(a, b) => Term::Assign(go(a), go(b)),
        Term::Restore(a, b) => Term::Restore(go(a), go(b)),
        Term::New(a) => Term::New(go(a)),
        Term::Drop(a) => Term::Drop(go(a)),
        Term::Deref(a) => Term::Deref(go(a)),
        Term::Let(y, e1, e2) => {
            let e2 = if y == x { e2.clone() } else { go(e2) };
            Term::Let(y.clone(), go(e1), e2)
        }
        Term::LetPair(y, z, e1, e2) => {
            let e2 = if y == x || z == x { e2.clone() } else { go(e2) };
            Term::LetPair(y.clone(), z.clone(), go(e1), e2)
        }
        Term::Borrow {
            kind,
            lifetime,
            var,
            owner,
            body,
        } => Term::Borrow {
            kind: *kind,
            lifetime: lifetime.clone(),
            var: var.clone(),
            owner: go(owner),
            body: if var == x { body.clone() } else { go(body) },
        },
    }
}

/// The abstract machine. Its state between steps is the store; the term is
/// passed from step to step.
#[derive(Clone, Debug, Default)]
pub struct Machine {
    pub store: Store,
}

/// The result of running a program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Value(Term),
    Stuck(Stuck),
    OutOfFuel,
}

/// One line of a trace: the rule applied, and the store after the step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    pub rule: &'static str,
    pub store: String,
}

fn ill_formed(e: &Term, what: &str) -> Stuck {
    Stuck {
        redex: e.summary(),
        reason: format!("ill-formed: {what}"),
    }
}

impl Machine {
    // ANCHOR: step
    /// Take one step from a term that is not a value. Returns the new term
    /// and the name of the reduction rule that was applied.
    pub fn step(&mut self, e: Term) -> Result<(Term, &'static str), Stuck> {
        // The guards `if !x.is_value()` pick the leftmost subterm that is not
        // a value yet; `inside` takes the step there (congruence).
        let whole = e.clone();
        match e {
            Term::Pair(a, b) if !a.is_value() => self.inside(a, |a| Term::Pair(a, b)),
            Term::Pair(a, b) => self.inside(b, |b| Term::Pair(a, b)),
            Term::Let(x, e1, e2) if !e1.is_value() => {
                self.inside(e1, |e1| Term::Let(x, e1, e2))
            }
            Term::Let(x, v, e2) => Ok((subst(&e2, &x, &v), "E-Let")),
            Term::LetPair(x, y, e1, e2) if !e1.is_value() => {
                self.inside(e1, |e1| Term::LetPair(x, y, e1, e2))
            }
            Term::LetPair(x, y, v, e2) => match *v {
                Term::Pair(v1, v2) => {
                    Ok((subst(&subst(&e2, &x, &v1), &y, &v2), "E-LetPair"))
                }
                _ => Err(ill_formed(&whole, "not a pair")),
            },
            Term::New(e1) if !e1.is_value() => self.inside(e1, Term::New),
            Term::New(v) => {
                let l = self.store.alloc(*v);
                Ok((Term::Ptr(Ptr::Own, l), "E-New"))
            }
            Term::Drop(e1) if !e1.is_value() => self.inside(e1, Term::Drop),
            Term::Drop(v) => {
                self.store.free(&v, &whole)?;
                Ok((Term::Unit, "E-Drop"))
            }
            Term::Deref(e1) if !e1.is_value() => self.inside(e1, Term::Deref),
            Term::Deref(v) => match *v {
                Term::Ptr(Ptr::Shr, l) => {
                    // Guard: ℓ is allocated and lent shared.
                    let cell = self.store.cell(l, &whole)?;
                    if cell.loan != Loan::Shared {
                        let reason = format!("ℓ{l} is {}, not lent shared", cell.loan);
                        return Err(Stuck {
                            redex: whole.summary(),
                            reason,
                        });
                    }
                    Ok((cell.value.clone(), "E-Deref"))
                }
                _ => Err(ill_formed(&whole, "not a shared reference")),
            },
            Term::Assign(t, v) if !t.is_value() => {
                self.inside(t, |t| Term::Assign(t, v))
            }
            Term::Assign(t, v) if !v.is_value() => {
                self.inside(v, |v| Term::Assign(t, v))
            }
            Term::Assign(t, v) => match *t {
                Term::Ptr(Ptr::Uniq, l) => {
                    // Guard: ℓ is allocated and lent mutably.
                    let cell = self.store.cell(l, &whole)?;
                    if cell.loan != Loan::Mut {
                        let reason = format!("ℓ{l} is {}, not lent mut", cell.loan);
                        return Err(Stuck {
                            redex: whole.summary(),
                            reason,
                        });
                    }
                    let old = std::mem::replace(&mut cell.value, *v);
                    // The old value is dropped, as Rust's `*r = v` does.
                    self.store.free(&old, &whole)?;
                    Ok((Term::Unit, "E-Assign"))
                }
                _ => Err(ill_formed(&whole, "not a mutable reference")),
            },
            Term::Borrow {
                kind,
                lifetime,
                var,
                owner,
                body,
            } if !owner.is_value() => self.inside(owner, |owner| Term::Borrow {
                kind,
                lifetime,
                var,
                owner,
                body,
            }),
            Term::Borrow {
                kind,
                var,
                owner,
                body,
                ..
            } => self.borrow(kind, &var, *owner, &body, &whole),
            Term::Restore(w, e1) if !e1.is_value() => {
                self.inside(e1, |e1| Term::Restore(w, e1))
            }
            Term::Restore(w, v) => {
                if let Term::Ptr(Ptr::Own, l) = *w {
                    // The borrow is over: the location is no longer lent.
                    self.store.cell(l, &whole)?.loan = Loan::None;
                    return Ok((Term::Pair(w, v), "E-EndBorrow"));
                }
                Ok((Term::Pair(w, v), "E-EndReborrow"))
            }
            Term::Var(x) => Err(ill_formed(&whole, &format!("unbound variable `{x}`"))),
            Term::Lit(_) | Term::Unit | Term::Ptr(..) => {
                Err(ill_formed(&whole, "a value cannot step"))
            }
        }
    }
    // ANCHOR_END: step

    /// Congruence: take a step inside the subterm `sub`, then rebuild the
    /// surrounding term around the result.
    fn inside(
        &mut self,
        sub: Box<Term>,
        rebuild: impl FnOnce(Box<Term>) -> Term,
    ) -> Result<(Term, &'static str), Stuck> {
        let (t, rule) = self.step(*sub)?;
        Ok((rebuild(Box::new(t)), rule))
    }

    // ANCHOR: borrow_step
    /// The three borrow rules. A borrow lends the location (guard: it is not
    /// lent already), substitutes a reference for `y` in the body, and wraps
    /// the body in a frame that gives the owner back at the end.
    fn borrow(
        &mut self,
        kind: BorrowKind,
        y: &str,
        owner: Term,
        body: &Term,
        whole: &Term,
    ) -> Result<(Term, &'static str), Stuck> {
        let (l, needs, lend_as, reference, rule) = match (kind, &owner) {
            (BorrowKind::Shared, Term::Ptr(Ptr::Own, l)) => {
                (*l, Loan::None, Loan::Shared, Ptr::Shr, "E-Borrow")
            }
            (BorrowKind::Mut, Term::Ptr(Ptr::Own, l)) => {
                (*l, Loan::None, Loan::Mut, Ptr::Uniq, "E-BorrowMut")
            }
            (BorrowKind::Reborrow, Term::Ptr(Ptr::Uniq, l)) => {
                (*l, Loan::Mut, Loan::Mut, Ptr::Uniq, "E-Reborrow")
            }
            _ => return Err(ill_formed(whole, "cannot borrow this value")),
        };
        let cell = self.store.cell(l, whole)?;
        if cell.loan != needs {
            let reason = format!("ℓ{l} is {}, so it cannot be {}", cell.loan, lend_as);
            return Err(Stuck {
                redex: whole.summary(),
                reason,
            });
        }
        cell.loan = lend_as;
        let body = subst(body, y, &Term::Ptr(reference, l));
        Ok((Term::Restore(Box::new(owner), Box::new(body)), rule))
    }
    // ANCHOR_END: borrow_step

    /// Run `e` to a value, recording each step, for at most `fuel` steps.
    pub fn run(&mut self, mut e: Term, fuel: usize) -> (Vec<TraceStep>, Outcome) {
        let mut trace = Vec::new();
        for _ in 0..fuel {
            if e.is_value() {
                return (trace, Outcome::Value(e));
            }
            match self.step(e) {
                Ok((next, rule)) => {
                    trace.push(TraceStep {
                        rule,
                        store: self.store.to_string(),
                    });
                    e = next;
                }
                Err(stuck) => return (trace, Outcome::Stuck(stuck)),
            }
        }
        if e.is_value() {
            (trace, Outcome::Value(e))
        } else {
            (trace, Outcome::OutOfFuel)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_term;

    fn run(src: &str) -> (Vec<TraceStep>, Outcome, Store) {
        let mut m = Machine::default();
        let (trace, outcome) = m.run(parse_term(src).unwrap(), 1000);
        (trace, outcome, m.store)
    }

    #[test]
    fn borrow_and_give_back() {
        let (_, out, store) = run("let b = new 0 in
             let (b, u) = (borrow r = &'a mut b in *r := 7) in
             let (b, n) = (borrow s = &'a b in *s) in
             let u = drop b in n");
        assert_eq!(out, Outcome::Value(Term::Lit(7)));
        assert_eq!(store.to_string(), "∅");
    }

    #[test]
    fn reborrows_keep_the_loan() {
        let (trace, out, _) = run("let b = new 0 in
             borrow r = &'a mut b in
               let (r1, u1) = (borrow y = &'b mut *r in *y := 1) in
               let (r2, u2) = (borrow y = &'c mut *r1 in *y := 2) in ()");
        assert!(matches!(out, Outcome::Value(_)));
        let reborrows = trace.iter().filter(|s| s.rule == "E-Reborrow").count();
        assert_eq!(reborrows, 2);
    }

    #[test]
    fn dangling_reference_gets_stuck() {
        let (_, out, _) = run("let b = new 5 in
             let (b, r) = (borrow y = &'a b in y) in
             let u = drop b in *r");
        let Outcome::Stuck(s) = out else {
            panic!("expected stuck")
        };
        assert!(s.reason.contains("use after free"));
    }

    #[test]
    fn mutable_borrow_during_shared_borrow_gets_stuck() {
        let (_, out, _) = run("let v = new 1 in
             borrow f = &'a v in
               let (v2, u) = (borrow m = &'b mut v in *m := 4) in *f");
        let Outcome::Stuck(s) = out else {
            panic!("expected stuck")
        };
        assert!(s.reason.contains("lent shared"));
    }

    #[test]
    fn double_free_gets_stuck() {
        let (_, out, _) = run("let b = new 1 in let c = b in let u = drop b in drop c");
        let Outcome::Stuck(s) = out else {
            panic!("expected stuck")
        };
        assert!(s.reason.contains("double free"));
    }

    #[test]
    fn assignment_drops_the_old_value() {
        let (_, out, store) = run("let b = new (new 1) in
             let (b, u) = (borrow r = &'a mut b in *r := new 2) in b");
        // The inner box is allocated first (ℓ0), then the outer one (ℓ1).
        assert_eq!(out, Outcome::Value(Term::Ptr(Ptr::Own, 1)));
        // The assignment freed the old inner box ℓ0; ℓ1 now holds ℓ2.
        assert_eq!(store.to_string(), "ℓ1 ↦ own ℓ2, ℓ2 ↦ 2");
    }
}
