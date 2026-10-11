//! A bidirectional type checker: `infer` synthesizes a type (`Γ ⊢ e ⇒ τ`),
//! `check` checks a term against a given type (`Γ ⊢ e ⇐ τ`).

use crate::syntax::{Term, Ty, fun, prod};
use std::fmt;

// ANCHOR: type_error
/// Why a term is rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    /// A variable that is not in the context.
    Unbound(String),
    /// The term synthesized `found`, but `expected` was required.
    Mismatch { term: Term, expected: Ty, found: Ty },
    /// The function part of an application does not have a function type.
    NotAFunction { term: Term, found: Ty },
    /// `fst` or `snd` applied to something that is not a pair.
    NotAPair { term: Term, found: Ty },
    /// `case` on something that is not a sum.
    NotASum { term: Term, found: Ty },
    /// An introduction form checked against a type of the wrong shape, such
    /// as a `λ` checked against `Nat`.
    WrongShape {
        term: Term,
        expected: Ty,
        form: &'static str,
    },
    /// A term that can be checked but not synthesized: a `λ` without an
    /// annotation, `inl e`, `inr e`.
    CannotSynthesize { term: Term, form: &'static str },
}
// ANCHOR_END: type_error

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TypeError::*;
        match self {
            Unbound(x) => write!(f, "unbound variable `{x}`"),
            Mismatch {
                term,
                expected,
                found,
            } => write!(f, "`{term}` has type {found}, but {expected} was expected"),
            NotAFunction { term, found } => {
                write!(f, "`{term}` has type {found}; it is not a function")
            }
            NotAPair { term, found } => {
                write!(f, "`{term}` has type {found}; it is not a pair")
            }
            NotASum { term, found } => {
                write!(f, "`{term}` has type {found}; it is not a sum")
            }
            WrongShape {
                term,
                expected,
                form,
            } => write!(f, "`{term}` is {form}, but {expected} was expected"),
            CannotSynthesize { term, form } => write!(
                f,
                "cannot synthesize a type for `{term}` ({form} can only be checked)"
            ),
        }
    }
}

impl std::error::Error for TypeError {}

/// A typing context `Γ`: a list of assumptions `x: τ`, searched from the right
/// so that inner bindings shadow outer ones.
pub type Ctx = Vec<(String, Ty)>;

/// The checker's state: the context and, optionally, a trace of the
/// judgments it visits.
struct Checker {
    ctx: Ctx,
    trace: Option<Vec<String>>,
    depth: usize,
}

impl Checker {
    fn lookup(&self, x: &str) -> Result<Ty, TypeError> {
        self.ctx
            .iter()
            .rev()
            .find(|(y, _)| y == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| TypeError::Unbound(x.to_string()))
    }

    /// Runs `f` with the extra assumption `x: ty`.
    fn under<T>(&mut self, x: &str, ty: Ty, f: impl FnOnce(&mut Self) -> T) -> T {
        self.ctx.push((x.to_string(), ty));
        let result = f(self);
        self.ctx.pop();
        result
    }

    fn judgment(&self, e: &Term, arrow: &str, ty: &str) -> String {
        let ctx: Vec<String> =
            self.ctx.iter().map(|(x, t)| format!("{x}: {t}")).collect();
        let ctx = if ctx.is_empty() {
            String::new()
        } else {
            ctx.join(", ") + " "
        };
        format!("{}{ctx}⊢ {e} {arrow} {ty}", "  ".repeat(self.depth))
    }

    /// Synthesis, `Γ ⊢ e ⇒ τ`, with the bookkeeping for the trace.
    fn infer(&mut self, e: &Term) -> Result<Ty, TypeError> {
        let line = self.trace.as_mut().map(|t| {
            t.push(String::new());
            t.len() - 1
        });
        self.depth += 1;
        let result = self.infer_inner(e);
        self.depth -= 1;
        if let (Some(i), Ok(ty)) = (line, &result) {
            let text = self.judgment(e, "⇒", &ty.to_string());
            self.trace.as_mut().unwrap()[i] = text;
        } else if let Some(i) = line {
            let text = self.judgment(e, "⇒", "✗");
            self.trace.as_mut().unwrap()[i] = text;
        }
        result
    }

    // ANCHOR: infer
    /// The synthesis rules, `Γ ⊢ e ⇒ τ`: compute the type of `e` from `e`
    /// itself. The type is an output.
    fn infer_inner(&mut self, e: &Term) -> Result<Ty, TypeError> {
        use Term::*;
        match e {
            // ANCHOR: infer_core
            Var(x) => self.lookup(x),
            // An annotation switches to checking mode.
            Ann(e, ty) => {
                self.check(e, ty)?;
                Ok(ty.clone())
            }
            // Elimination of →: synthesize the function's type, then check
            // the argument against its domain.
            App(f, a) => match self.infer(f)? {
                Ty::Fun(dom, cod) => {
                    self.check(a, &dom)?;
                    Ok(*cod)
                }
                found => Err(TypeError::NotAFunction {
                    term: (**f).clone(),
                    found,
                }),
            },
            // A λ with an annotated parameter can synthesize...
            Lam(x, Some(dom), body) => {
                let cod = self.under(x, dom.clone(), |c| c.infer(body))?;
                Ok(fun(dom.clone(), cod))
            }
            // ...but without one it cannot: what is the type of x?
            Lam(_, None, _) => Err(TypeError::CannotSynthesize {
                term: e.clone(),
                form: "an unannotated λ",
            }),
            // ANCHOR_END: infer_core
            Let(x, e1, e2) => {
                let ty1 = self.infer(e1)?;
                self.under(x, ty1, |c| c.infer(e2))
            }
            Unit => Ok(Ty::Unit),
            Bool(_) => Ok(Ty::Bool),
            Nat(_) => Ok(Ty::Nat),
            Succ(n) => {
                self.check(n, &Ty::Nat)?;
                Ok(Ty::Nat)
            }
            If(c, a, b) => {
                self.check(c, &Ty::Bool)?;
                let ty = self.infer(a)?;
                self.check(b, &ty)?;
                Ok(ty)
            }
            Iter(n, z, s) => {
                self.check(n, &Ty::Nat)?;
                let ty = self.infer(z)?;
                self.check(s, &fun(ty.clone(), ty.clone()))?;
                Ok(ty)
            }
            Pair(a, b) => Ok(prod(self.infer(a)?, self.infer(b)?)),
            Fst(p) | Snd(p) => match self.infer(p)? {
                Ty::Prod(a, b) => Ok(if matches!(e, Fst(_)) { *a } else { *b }),
                found => Err(TypeError::NotAPair {
                    term: (**p).clone(),
                    found,
                }),
            },
            Inl(_) | Inr(_) => Err(TypeError::CannotSynthesize {
                term: e.clone(),
                form: "an injection into a sum",
            }),
            Case(scrut, x, l, y, r) => {
                let (left, right) = self.infer_sum(scrut)?;
                let ty = self.under(x, left, |c| c.infer(l))?;
                self.under(y, right, |c| c.check(r, &ty))?;
                Ok(ty)
            }
        }
    }
    // ANCHOR_END: infer

    fn infer_sum(&mut self, scrut: &Term) -> Result<(Ty, Ty), TypeError> {
        match self.infer(scrut)? {
            Ty::Sum(a, b) => Ok((*a, *b)),
            found => Err(TypeError::NotASum {
                term: scrut.clone(),
                found,
            }),
        }
    }

    /// Checking, `Γ ⊢ e ⇐ τ`, with the bookkeeping for the trace.
    fn check(&mut self, e: &Term, ty: &Ty) -> Result<(), TypeError> {
        if self.trace.is_some() {
            let line = self.judgment(e, "⇐", &ty.to_string());
            self.trace.as_mut().unwrap().push(line);
        }
        self.depth += 1;
        let result = self.check_inner(e, ty);
        self.depth -= 1;
        result
    }

    // ANCHOR: check
    /// The checking rules, `Γ ⊢ e ⇐ τ`: does `e` have the given type `τ`? The
    /// type is an input.
    fn check_inner(&mut self, e: &Term, ty: &Ty) -> Result<(), TypeError> {
        use Term::*;
        let wrong_shape = |form| TypeError::WrongShape {
            term: e.clone(),
            expected: ty.clone(),
            form,
        };
        match (e, ty) {
            // Introduction of →: the expected type tells us the type of x.
            (Lam(x, ann, body), Ty::Fun(dom, cod)) => {
                if let Some(ann) = ann
                    && ann != &**dom
                {
                    return Err(TypeError::Mismatch {
                        term: e.clone(),
                        expected: ty.clone(),
                        found: fun(ann.clone(), (**cod).clone()),
                    });
                }
                self.under(x, (**dom).clone(), |c| c.check(body, cod))
            }
            (Lam(..), _) => Err(wrong_shape("a function")),
            (Pair(a, b), Ty::Prod(ta, tb)) => {
                self.check(a, ta)?;
                self.check(b, tb)
            }
            (Pair(..), _) => Err(wrong_shape("a pair")),
            (Inl(a), Ty::Sum(left, _)) => self.check(a, left),
            (Inr(b), Ty::Sum(_, right)) => self.check(b, right),
            (Inl(_) | Inr(_), _) => Err(wrong_shape("an injection into a sum")),
            (If(c, a, b), _) => {
                self.check(c, &Ty::Bool)?;
                self.check(a, ty)?;
                self.check(b, ty)
            }
            (Let(x, e1, e2), _) => {
                let ty1 = self.infer(e1)?;
                self.under(x, ty1, |c| c.check(e2, ty))
            }
            (Case(scrut, x, l, y, r), _) => {
                let (left, right) = self.infer_sum(scrut)?;
                self.under(x, left, |c| c.check(l, ty))?;
                self.under(y, right, |c| c.check(r, ty))
            }
            (Iter(n, z, s), _) => {
                self.check(n, &Ty::Nat)?;
                self.check(z, ty)?;
                self.check(s, &fun(ty.clone(), ty.clone()))
            }
            // Everything else: synthesize a type and compare (rule Switch).
            _ => {
                let found = self.infer(e)?;
                if &found == ty {
                    Ok(())
                } else {
                    Err(TypeError::Mismatch {
                        term: e.clone(),
                        expected: ty.clone(),
                        found,
                    })
                }
            }
        }
    }
    // ANCHOR_END: check
}

// ANCHOR: api
/// Synthesizes the type of a closed term.
pub fn infer(e: &Term) -> Result<Ty, TypeError> {
    infer_in(&Vec::new(), e)
}

/// Synthesizes the type of a term in a context.
pub fn infer_in(ctx: &Ctx, e: &Term) -> Result<Ty, TypeError> {
    let mut c = Checker {
        ctx: ctx.clone(),
        trace: None,
        depth: 0,
    };
    c.infer(e)
}

/// Checks a closed term against a type.
pub fn check(e: &Term, ty: &Ty) -> Result<(), TypeError> {
    let mut c = Checker {
        ctx: Vec::new(),
        trace: None,
        depth: 0,
    };
    c.check(e, ty)
}
// ANCHOR_END: api

/// Checks a closed term against a type and returns the judgments visited, one
/// per line, indented by depth: `⇐` lines are checking goals, `⇒` lines are
/// synthesized results.
pub fn check_with_trace(e: &Term, ty: &Ty) -> (Result<(), TypeError>, Vec<String>) {
    let mut c = Checker {
        ctx: Vec::new(),
        trace: Some(Vec::new()),
        depth: 0,
    };
    let result = c.check(e, ty);
    (result, c.trace.unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{parse_term, parse_type};

    fn ty_of(src: &str) -> Result<Ty, TypeError> {
        infer(&parse_term(src).unwrap())
    }

    fn t(src: &str) -> Ty {
        parse_type(src).unwrap()
    }

    #[test]
    fn synthesis() {
        assert_eq!(ty_of("λx: Nat. succ x"), Ok(t("Nat → Nat")));
        assert_eq!(
            ty_of("λf: Nat → Nat. λx: Nat. f (f x)"),
            Ok(t("(Nat → Nat) → Nat → Nat"))
        );
        assert_eq!(ty_of("(1, true)"), Ok(t("Nat × Bool")));
        assert_eq!(ty_of("snd (1, true)"), Ok(t("Bool")));
        assert_eq!(ty_of("let x = 3 in succ x"), Ok(t("Nat")));
        assert_eq!(ty_of("iter 3 0 (λn. succ n)"), Ok(t("Nat")));
    }

    #[test]
    fn checking_supplies_parameter_types() {
        let twice = parse_term("λf. λx. f (f x)").unwrap();
        assert!(check(&twice, &t("(Nat → Nat) → Nat → Nat")).is_ok());
        assert!(check(&twice, &t("(Bool → Bool) → Bool → Bool")).is_ok());
        // Through an annotation, the same term synthesizes.
        assert_eq!(
            ty_of("(λf. λx. f (f x) : (Nat → Nat) → Nat → Nat)"),
            Ok(t("(Nat → Nat) → Nat → Nat"))
        );
    }

    #[test]
    fn lambdas_and_injections_do_not_synthesize() {
        assert!(matches!(
            ty_of("λx. x"),
            Err(TypeError::CannotSynthesize { .. })
        ));
        assert!(matches!(
            ty_of("inl 3"),
            Err(TypeError::CannotSynthesize { .. })
        ));
        assert_eq!(ty_of("(inl 3 : Nat + Bool)"), Ok(t("Nat + Bool")));
    }

    #[test]
    fn sums() {
        let src = "λs: Nat + Bool. case s of inl n => n | inr b => if b then 1 else 0";
        assert_eq!(ty_of(src), Ok(t("Nat + Bool → Nat")));
    }

    #[test]
    fn errors() {
        assert_eq!(ty_of("y"), Err(TypeError::Unbound("y".into())));
        assert!(matches!(ty_of("3 4"), Err(TypeError::NotAFunction { .. })));
        assert!(matches!(ty_of("fst 3"), Err(TypeError::NotAPair { .. })));
        assert!(matches!(
            ty_of("if true then 1 else false"),
            Err(TypeError::Mismatch { .. })
        ));
        assert!(matches!(
            check(&parse_term("λx. x").unwrap(), &Ty::Nat),
            Err(TypeError::WrongShape { .. })
        ));
        // Self-application has no type, whatever the annotation.
        assert!(matches!(
            ty_of("λx: Nat → Nat. x x"),
            Err(TypeError::Mismatch { .. })
        ));
    }

    #[test]
    fn shadowing() {
        assert_eq!(ty_of("λx: Nat. λx: Bool. x"), Ok(t("Nat → Bool → Bool")));
    }

    #[test]
    fn trace_shows_modes() {
        let (result, lines) = check_with_trace(
            &parse_term("λf. λx. f (f x)").unwrap(),
            &t("(Nat → Nat) → Nat → Nat"),
        );
        assert!(result.is_ok());
        assert_eq!(lines[0], "⊢ λf. λx. f (f x) ⇐ (Nat → Nat) → Nat → Nat");
        assert!(lines.iter().any(|l| l.contains("⊢ f ⇒ Nat → Nat")));
    }
}
