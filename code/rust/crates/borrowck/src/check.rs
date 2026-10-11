//! The type checker: it builds a derivation of `Δ; Γ ⊢ e : τ`, or explains
//! which premise of which rule cannot be satisfied.
//!
//! The rules are syntax-directed (one rule per kind of term), so checking is a
//! single recursive pass. The only real decision is how to split a context
//! between two premises, and the checker makes it by looking at which
//! variables each premise mentions: a variable goes where it is used, and a
//! variable used on both sides must have a `Copy` type.

use std::fmt;

use crate::parse::Program;
use crate::syntax::{BorrowKind, Lifetime, Term, Ty};

/// A typing context `Γ`, in the order in which the variables were bound.
pub type Ctx = Vec<(String, Ty)>;

// ANCHOR: derivation
/// A judgment `Δ; Γ ⊢ e : τ`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Judgment {
    pub lifetimes: Vec<Lifetime>,
    pub ctx: Ctx,
    pub term: Term,
    pub ty: Ty,
}

/// A derivation tree: the rule used at the root, its conclusion, the side
/// conditions it checked, and the derivations of its premises.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Derivation {
    pub rule: &'static str,
    pub conclusion: Judgment,
    pub side_conditions: Vec<String>,
    pub premises: Vec<Derivation>,
}
// ANCHOR_END: derivation

// ANCHOR: type_error
/// Why no derivation exists. Each variant names the rule whose premise fails.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    /// T-Var: the variable is not in the context.
    Unbound { var: String },
    /// A context split: a non-`Copy` variable is needed by both premises.
    UsedTwice {
        var: String,
        ty: Ty,
        site: Site,
        term: Term,
    },
    /// A premise has the wrong type.
    Mismatch {
        rule: &'static str,
        expected: String,
        found: Ty,
        term: Term,
    },
    /// T-Deref: reading would duplicate a value that is not `Copy`.
    NotCopy { ty: Ty, term: Term },
    /// T-Assign: writing through a shared reference.
    AssignThroughShared { ty: Ty, term: Term },
    /// The escape check `α ∉ flv(σ)` of a borrow rule.
    Escape {
        lifetime: Lifetime,
        ty: Ty,
        rule: &'static str,
        term: Term,
    },
    /// The freshness condition `α ∉ Δ` of a borrow rule.
    LifetimeInScope {
        lifetime: Lifetime,
        rule: &'static str,
        term: Term,
    },
    /// A pattern `(x, x)` or a repeated parameter.
    DuplicateVar { var: String, term: Term },
    /// A parameter type mentions a lifetime that is not declared.
    UndeclaredLifetime { lifetime: Lifetime, var: String },
    /// `own ℓ`, `restore ... after ...`: run-time forms are not checked.
    RuntimeForm { term: Term },
}
// ANCHOR_END: type_error

/// The constructs whose rule splits the context, and what their two premises
/// are called in error messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    Pair,
    Let,
    Assign,
    Borrow(BorrowKind),
}

impl Site {
    pub fn rule(self) -> &'static str {
        match self {
            Site::Pair => "T-Pair",
            Site::Let => "T-Let",
            Site::Assign => "T-Assign",
            Site::Borrow(kind) => borrow_rule(kind),
        }
    }

    fn premises(self) -> (&'static str, &'static str) {
        match self {
            Site::Pair => ("the first component", "the second"),
            Site::Let => ("the right-hand side of the `let`", "its body"),
            Site::Assign => ("the reference", "the assigned value"),
            Site::Borrow(BorrowKind::Reborrow) => {
                ("the reborrowed reference", "the body")
            }
            Site::Borrow(_) => ("the borrowed owner", "the body of the borrow"),
        }
    }
}

fn borrow_rule(kind: BorrowKind) -> &'static str {
    match kind {
        BorrowKind::Shared => "T-Borrow",
        BorrowKind::Mut => "T-BorrowMut",
        BorrowKind::Reborrow => "T-Reborrow",
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Unbound { var } => {
                write!(f, "error: cannot find `{var}` in the context (T-Var)")
            }
            TypeError::UsedTwice {
                var,
                ty,
                site,
                term,
            } => {
                let headline = match site {
                    Site::Borrow(_) => format!("`{var}` is used while it is borrowed"),
                    Site::Let => format!("use of moved value: `{var}`"),
                    Site::Pair | Site::Assign => format!("`{var}` is used twice"),
                };
                let (first, second) = site.premises();
                writeln!(f, "error: {headline}")?;
                writeln!(f, "  in: {}", term.summary())?;
                writeln!(f, "  `{var}` is needed by {first} and by {second},")?;
                writeln!(
                    f,
                    "  but `{var}: {ty}` is not Copy, so the split Γ = Γ₁ ⊎ Γ₂"
                )?;
                write!(f, "  of {} can give it to only one of them", site.rule())
            }
            TypeError::Mismatch {
                rule,
                expected,
                found,
                term,
            } => {
                writeln!(f, "error: mismatched types")?;
                writeln!(f, "  in: {}", term.summary())?;
                write!(f, "  {rule} expects {expected}, found {found}")
            }
            TypeError::NotCopy { ty, term } => {
                writeln!(f, "error: cannot move out of a shared reference")?;
                writeln!(f, "  in: {}", term.summary())?;
                write!(
                    f,
                    "  reading would duplicate a value of type {ty}, which is not Copy"
                )?;
                write!(f, " (T-Deref)")
            }
            TypeError::AssignThroughShared { ty, term } => {
                writeln!(f, "error: cannot assign through a shared reference")?;
                writeln!(f, "  in: {}", term.summary())?;
                write!(
                    f,
                    "  the target has type {ty}; T-Assign needs a mutable reference"
                )
            }
            TypeError::Escape {
                lifetime,
                ty,
                rule,
                term,
            } => {
                writeln!(f, "error: borrowed value does not live long enough")?;
                writeln!(f, "  in: {}", term.summary())?;
                writeln!(f, "  the body has type {ty}, which mentions '{lifetime}:")?;
                write!(
                    f,
                    "  the escape check '{lifetime} ∉ flv({ty}) of {rule} fails"
                )
            }
            TypeError::LifetimeInScope {
                lifetime,
                rule,
                term,
            } => {
                writeln!(f, "error: lifetime '{lifetime} is already in scope")?;
                writeln!(f, "  in: {}", term.summary())?;
                write!(f, "  {rule} needs a fresh lifetime ('{lifetime} ∉ Δ)")
            }
            TypeError::DuplicateVar { var, term } => {
                writeln!(f, "error: `{var}` is bound twice")?;
                write!(f, "  in: {}", term.summary())
            }
            TypeError::UndeclaredLifetime { lifetime, var } => {
                write!(
                    f,
                    "error: the type of parameter `{var}` uses undeclared '{lifetime}"
                )
            }
            TypeError::RuntimeForm { term } => {
                write!(f, "error: `{}` only exists at run time", term.summary())
            }
        }
    }
}

impl std::error::Error for TypeError {}

impl TypeError {
    /// The first line of the message, for example
    /// "error: use of moved value: `b`".
    pub fn headline(&self) -> String {
        self.to_string()
            .lines()
            .next()
            .unwrap_or_default()
            .to_string()
    }
}

/// Check a program: its lifetime parameters are `Δ`, its parameters `Γ`.
pub fn check_program(p: &Program) -> Result<Derivation, TypeError> {
    for (i, (x, t)) in p.params.iter().enumerate() {
        if p.params[..i].iter().any(|(y, _)| y == x) {
            let term = p.body.clone();
            return Err(TypeError::DuplicateVar {
                var: x.clone(),
                term,
            });
        }
        if let Some(k) = t.lifetimes().into_iter().find(|k| !p.lifetimes.contains(k)) {
            return Err(TypeError::UndeclaredLifetime {
                lifetime: k,
                var: x.clone(),
            });
        }
    }
    check(&p.lifetimes, &p.params, &p.body)
}

fn lookup<'c>(ctx: &'c Ctx, x: &str) -> Option<&'c Ty> {
    ctx.iter().rev().find(|(y, _)| y == x).map(|(_, t)| t)
}

/// A rule with no premises.
fn leaf(
    rule: &'static str,
    delta: &[Lifetime],
    ctx: &Ctx,
    e: &Term,
    ty: Ty,
) -> Derivation {
    let conclusion = Judgment {
        lifetimes: delta.to_vec(),
        ctx: ctx.clone(),
        term: e.clone(),
        ty,
    };
    Derivation {
        rule,
        conclusion,
        side_conditions: vec![],
        premises: vec![],
    }
}

fn node(
    rule: &'static str,
    delta: &[Lifetime],
    ctx: &Ctx,
    e: &Term,
    ty: Ty,
    side_conditions: Vec<String>,
    premises: Vec<Derivation>,
) -> Derivation {
    let conclusion = Judgment {
        lifetimes: delta.to_vec(),
        ctx: ctx.clone(),
        term: e.clone(),
        ty,
    };
    Derivation {
        rule,
        conclusion,
        side_conditions,
        premises,
    }
}

// ANCHOR: split
/// Split `Γ` between a first premise `e1` and a second premise `e2` (in which
/// the variables `bound` are about to be bound). A variable goes where it is
/// used; a variable used by both premises must be `Copy`. Unused variables go
/// to the second premise, unless their name is about to be rebound there.
fn split(
    ctx: &Ctx,
    e1: &Term,
    e2: &Term,
    bound: &[&str],
    site: Site,
    whole: &Term,
) -> Result<(Ctx, Ctx), TypeError> {
    let (mut left, mut right) = (Ctx::new(), Ctx::new());
    for (x, ty) in ctx {
        let in_first = e1.occurs(x);
        let rebound = bound.contains(&x.as_str());
        let in_second = !rebound && e2.occurs(x);
        match (in_first, in_second) {
            (true, true) if ty.is_copy() => {
                left.push((x.clone(), ty.clone()));
                right.push((x.clone(), ty.clone()));
            }
            (true, true) => {
                return Err(TypeError::UsedTwice {
                    var: x.clone(),
                    ty: ty.clone(),
                    site,
                    term: whole.clone(),
                });
            }
            (true, false) => left.push((x.clone(), ty.clone())),
            (false, true) => right.push((x.clone(), ty.clone())),
            (false, false) if rebound => left.push((x.clone(), ty.clone())),
            (false, false) => right.push((x.clone(), ty.clone())),
        }
    }
    Ok((left, right))
}
// ANCHOR_END: split

/// How a split is shown in a derivation: `Γ₁ = r | Γ₂ = u1`.
fn split_note(left: &Ctx, right: &Ctx) -> String {
    let names = |c: &Ctx| {
        if c.is_empty() {
            "·".to_string()
        } else {
            c.iter()
                .map(|(x, _)| x.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        }
    };
    format!("split: Γ₁ = {} | Γ₂ = {}", names(left), names(right))
}

/// Build a derivation of `Δ; Γ ⊢ e : τ` for some `τ`, or explain why there is
/// none.
pub fn check(delta: &[Lifetime], ctx: &Ctx, e: &Term) -> Result<Derivation, TypeError> {
    match e {
        Term::Var(x) => match lookup(ctx, x) {
            Some(ty) => Ok(leaf("T-Var", delta, ctx, e, ty.clone())),
            None => Err(TypeError::Unbound { var: x.clone() }),
        },
        Term::Lit(_) => Ok(leaf("T-Int", delta, ctx, e, Ty::Int)),
        Term::Unit => Ok(leaf("T-Unit", delta, ctx, e, Ty::Unit)),
        Term::Pair(a, b) => {
            let (c1, c2) = split(ctx, a, b, &[], Site::Pair, e)?;
            let d1 = check(delta, &c1, a)?;
            let d2 = check(delta, &c2, b)?;
            let ty = Ty::pair(d1.conclusion.ty.clone(), d2.conclusion.ty.clone());
            let notes = vec![split_note(&c1, &c2)];
            Ok(node("T-Pair", delta, ctx, e, ty, notes, vec![d1, d2]))
        }
        Term::Let(x, e1, e2) => {
            let (c1, mut c2) = split(ctx, e1, e2, &[x], Site::Let, e)?;
            let d1 = check(delta, &c1, e1)?;
            let notes = vec![split_note(&c1, &c2)];
            c2.push((x.clone(), d1.conclusion.ty.clone()));
            let d2 = check(delta, &c2, e2)?;
            let ty = d2.conclusion.ty.clone();
            Ok(node("T-Let", delta, ctx, e, ty, notes, vec![d1, d2]))
        }
        Term::LetPair(x, y, e1, e2) => {
            if x == y {
                return Err(TypeError::DuplicateVar {
                    var: x.clone(),
                    term: e.clone(),
                });
            }
            let (c1, mut c2) = split(ctx, e1, e2, &[x, y], Site::Let, e)?;
            let d1 = check(delta, &c1, e1)?;
            let Ty::Pair(t1, t2) = d1.conclusion.ty.clone() else {
                return Err(TypeError::Mismatch {
                    rule: "T-LetPair",
                    expected: "a pair τ₁ ⊗ τ₂".into(),
                    found: d1.conclusion.ty,
                    term: e.clone(),
                });
            };
            let notes = vec![split_note(&c1, &c2)];
            c2.push((x.clone(), *t1));
            c2.push((y.clone(), *t2));
            let d2 = check(delta, &c2, e2)?;
            let ty = d2.conclusion.ty.clone();
            Ok(node("T-LetPair", delta, ctx, e, ty, notes, vec![d1, d2]))
        }
        Term::New(e1) => {
            let d = check(delta, ctx, e1)?;
            let ty = Ty::boxed(d.conclusion.ty.clone());
            Ok(node("T-New", delta, ctx, e, ty, vec![], vec![d]))
        }
        Term::Drop(e1) => {
            let d = check(delta, ctx, e1)?;
            Ok(node("T-Drop", delta, ctx, e, Ty::Unit, vec![], vec![d]))
        }
        Term::Deref(e1) => {
            let d = check(delta, ctx, e1)?;
            match d.conclusion.ty.clone() {
                Ty::Ref(_, t) if t.is_copy() => {
                    let note = vec![format!("Copy({t})")];
                    Ok(node("T-Deref", delta, ctx, e, *t, note, vec![d]))
                }
                Ty::Ref(_, t) => Err(TypeError::NotCopy {
                    ty: *t,
                    term: e.clone(),
                }),
                found => Err(TypeError::Mismatch {
                    rule: "T-Deref",
                    expected: "a shared reference &'κ τ".into(),
                    found,
                    term: e.clone(),
                }),
            }
        }
        Term::Assign(target, value) => {
            let (c1, c2) = split(ctx, target, value, &[], Site::Assign, e)?;
            let d1 = check(delta, &c1, target)?;
            let t = match d1.conclusion.ty.clone() {
                Ty::RefMut(_, t) => *t,
                ty @ Ty::Ref(..) => {
                    return Err(TypeError::AssignThroughShared {
                        ty,
                        term: e.clone(),
                    });
                }
                found => {
                    return Err(TypeError::Mismatch {
                        rule: "T-Assign",
                        expected: "a mutable reference &'κ mut τ".into(),
                        found,
                        term: e.clone(),
                    });
                }
            };
            let d2 = check(delta, &c2, value)?;
            if d2.conclusion.ty != t {
                return Err(TypeError::Mismatch {
                    rule: "T-Assign",
                    expected: format!("a value of type {t}"),
                    found: d2.conclusion.ty,
                    term: e.clone(),
                });
            }
            let notes = vec![split_note(&c1, &c2)];
            Ok(node(
                "T-Assign",
                delta,
                ctx,
                e,
                Ty::Unit,
                notes,
                vec![d1, d2],
            ))
        }
        Term::Borrow {
            kind,
            lifetime,
            var,
            owner,
            body,
        } => check_borrow(delta, ctx, e, *kind, lifetime, var, owner, body),
        Term::Ptr(..) | Term::Restore(..) => {
            Err(TypeError::RuntimeForm { term: e.clone() })
        }
    }
}

// ANCHOR: check_borrow
/// Rules T-Borrow, T-BorrowMut and T-Reborrow.
fn check_borrow(
    delta: &[Lifetime],
    ctx: &Ctx,
    e: &Term,
    kind: BorrowKind,
    alpha: &Lifetime,
    y: &str,
    owner: &Term,
    body: &Term,
) -> Result<Derivation, TypeError> {
    let rule = borrow_rule(kind);
    // Freshness: α ∉ Δ.
    if delta.contains(alpha) {
        return Err(TypeError::LifetimeInScope {
            lifetime: alpha.clone(),
            rule,
            term: e.clone(),
        });
    }
    // Γ = Γ₁ ⊎ Γ₂: the owner (or the reborrowed reference) gets Γ₁.
    let (c1, mut c2) = split(ctx, owner, body, &[y], Site::Borrow(kind), e)?;
    let d1 = check(delta, &c1, owner)?;
    // What the body receives (y's type), and what comes back afterwards.
    let (y_ty, returned) = match (kind, d1.conclusion.ty.clone()) {
        (BorrowKind::Shared, Ty::Box(t)) => {
            (Ty::Ref(alpha.clone(), t.clone()), Ty::Box(t))
        }
        (BorrowKind::Mut, Ty::Box(t)) => {
            (Ty::RefMut(alpha.clone(), t.clone()), Ty::Box(t))
        }
        (BorrowKind::Reborrow, Ty::RefMut(k, t)) => {
            (Ty::RefMut(alpha.clone(), t.clone()), Ty::RefMut(k, t))
        }
        (kind, found) => {
            let expected = match kind {
                BorrowKind::Reborrow => "a mutable reference &'κ mut τ",
                _ => "an owner Box τ",
            };
            return Err(TypeError::Mismatch {
                rule,
                expected: expected.into(),
                found,
                term: e.clone(),
            });
        }
    };
    // The body is checked with α in scope and y bound to the new reference.
    let mut delta2 = delta.to_vec();
    delta2.push(alpha.clone());
    let mut notes = vec![
        split_note(&c1, &c2),
        format!("fresh: '{alpha} ∉ Δ = {{{}}}", quoted(delta)),
    ];
    c2.push((y.to_string(), y_ty));
    let d2 = check(&delta2, &c2, body)?;
    // The escape check: α ∉ flv(σ).
    let sigma = d2.conclusion.ty.clone();
    if sigma.mentions(alpha) {
        return Err(TypeError::Escape {
            lifetime: alpha.clone(),
            ty: sigma,
            rule,
            term: e.clone(),
        });
    }
    notes.push(format!("escape check: '{alpha} ∉ flv({sigma})"));
    let ty = Ty::pair(returned, sigma);
    Ok(node(rule, delta, ctx, e, ty, notes, vec![d1, d2]))
}
// ANCHOR_END: check_borrow

fn quoted(delta: &[Lifetime]) -> String {
    delta
        .iter()
        .map(|k| format!("'{k}"))
        .collect::<Vec<_>>()
        .join(", ")
}

impl fmt::Display for Judgment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.ctx.is_empty() {
            write!(f, "·")?;
        }
        for (i, (x, t)) in self.ctx.iter().enumerate() {
            let sep = if i == 0 { "" } else { ", " };
            write!(f, "{sep}{x}: {t}")?;
        }
        write!(f, " ⊢ {} : {}", self.term.summary(), self.ty)
    }
}

impl Derivation {
    fn render(&self, first: &str, rest: &str, out: &mut Vec<String>) {
        out.push(format!("{first}{}  {}", self.rule, self.conclusion));
        let bar = if self.premises.is_empty() {
            "  "
        } else {
            "│ "
        };
        for note in &self.side_conditions {
            out.push(format!("{rest}{bar}{note}"));
        }
        let n = self.premises.len();
        for (i, p) in self.premises.iter().enumerate() {
            let last = i + 1 == n;
            let (branch, cont) = if last {
                ("└─ ", "   ")
            } else {
                ("├─ ", "│  ")
            };
            p.render(&format!("{rest}{branch}"), &format!("{rest}{cont}"), out);
        }
    }

    /// The number of rule applications in the tree.
    pub fn size(&self) -> usize {
        1 + self.premises.iter().map(Derivation::size).sum::<usize>()
    }
}

// ANCHOR: display_derivation
impl fmt::Display for Derivation {
    /// The tree, root first, one rule per line, premises indented below their
    /// conclusion; side conditions are listed under the rule that checks them.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut lines = Vec::new();
        self.render("", "", &mut lines);
        write!(f, "{}", lines.join("\n"))
    }
}
// ANCHOR_END: display_derivation

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::{parse_program, parse_term};

    fn check_src(ctx: &[(&str, &str)], src: &str) -> Result<Ty, TypeError> {
        let ctx: Ctx = ctx
            .iter()
            .map(|(x, t)| (x.to_string(), crate::parse::parse_ty(t).unwrap()))
            .collect();
        let delta = vec!["a".to_string()];
        check(&delta, &ctx, &parse_term(src).unwrap()).map(|d| d.conclusion.ty)
    }

    #[test]
    fn reborrow_twice() {
        let p = parse_program(
            "fn twice<'a>(r: &'a mut Int) {
               let (r1, u1) = (borrow y1 = &'b1 mut *r in *y1 := 1) in
               let (r2, u2) = (borrow y2 = &'b2 mut *r1 in *y2 := 2) in
               ()
             }",
        )
        .unwrap();
        let d = check_program(&p).unwrap();
        assert_eq!(d.conclusion.ty, Ty::Unit);
        assert_eq!(d.rule, "T-LetPair");
        assert_eq!(d.size(), 13);
    }

    #[test]
    fn aliasing_bug_is_a_failed_split() {
        let err = check_src(
            &[("v", "Box Int")],
            "borrow f = &'b v in
               let (v2, u) = (borrow m = &'c mut v in *m := 4) in *f",
        )
        .unwrap_err();
        assert!(matches!(
            err,
            TypeError::UsedTwice { ref var, site: Site::Borrow(BorrowKind::Shared), .. }
                if var == "v"
        ));
    }

    #[test]
    fn escape_check() {
        let err = check_src(&[("b", "Box Int")], "borrow y = &'b b in y").unwrap_err();
        assert!(matches!(err, TypeError::Escape { .. }));
        // Returning a copy of the integer instead is fine.
        let ok = check_src(&[("b", "Box Int")], "borrow y = &'b b in *y").unwrap();
        assert_eq!(ok, Ty::pair(Ty::boxed(Ty::Int), Ty::Int));
    }

    #[test]
    fn copy_decides_sharing() {
        assert!(check_src(&[("s", "&'a Int")], "(s, s)").is_ok());
        let err = check_src(&[("r", "&'a mut Int")], "(r, r)").unwrap_err();
        assert!(matches!(
            err,
            TypeError::UsedTwice {
                site: Site::Pair,
                ..
            }
        ));
        let err = check_src(&[("b", "Box Int")], "let c = b in (b, c)").unwrap_err();
        assert!(matches!(
            err,
            TypeError::UsedTwice {
                site: Site::Let,
                ..
            }
        ));
    }

    #[test]
    fn freshness_and_permissions() {
        let err = check_src(&[("b", "Box Int")], "borrow y = &'a b in ()").unwrap_err();
        assert!(matches!(err, TypeError::LifetimeInScope { .. }));
        let err = check_src(&[("s", "&'a Int")], "*s := 1").unwrap_err();
        assert!(matches!(err, TypeError::AssignThroughShared { .. }));
        let err = check_src(&[("s", "&'a Box Int")], "*s").unwrap_err();
        assert!(matches!(err, TypeError::NotCopy { .. }));
        let err = check_src(&[("r", "&'a mut Int")], "*r").unwrap_err();
        assert!(matches!(
            err,
            TypeError::Mismatch {
                rule: "T-Deref",
                ..
            }
        ));
    }

    #[test]
    fn owner_comes_back() {
        // After the borrow, `b` is rebound and can be dropped.
        let ty = check_src(
            &[("b", "Box Int")],
            "let (b, n) = (borrow y = &'b b in *y) in let u = drop b in n",
        )
        .unwrap();
        assert_eq!(ty, Ty::Int);
    }
}
