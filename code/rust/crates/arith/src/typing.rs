//! The typing judgment Γ ⊢ e : τ, its derivations, and a type checker that
//! builds them.
//!
//! The rules (Chapter 3 writes them as fractions):
//!
//! ```text
//! T-Num   Γ ⊢ n : Nat
//! T-Bool  Γ ⊢ true : Bool        Γ ⊢ false : Bool
//! T-Var   Γ ⊢ x : τ                       if (x : τ) ∈ Γ
//! T-Add   Γ ⊢ e1 + e2 : Nat               if Γ ⊢ e1 : Nat and Γ ⊢ e2 : Nat
//! T-Eq    Γ ⊢ e1 == e2 : Bool             if Γ ⊢ e1 : τ and Γ ⊢ e2 : τ
//! T-If    Γ ⊢ if c then e1 else e2 : τ    if Γ ⊢ c : Bool, Γ ⊢ e1 : τ, Γ ⊢ e2 : τ
//! T-Let   Γ ⊢ let x = e1 in e2 : τ2       if Γ ⊢ e1 : τ1 and Γ, x : τ1 ⊢ e2 : τ2
//! ```

use crate::syntax::{Expr, Ty};
use std::fmt;

// ANCHOR: ctx
/// A typing context Γ = x1 : τ1, ..., xn : τn. Bindings are kept in order,
/// most recent last, so that a new binding for `x` shadows older ones.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Ctx {
    bindings: Vec<(String, Ty)>,
}

impl Ctx {
    /// The empty context.
    pub fn new() -> Self {
        Ctx::default()
    }

    /// Γ, x : τ — a new context; `self` is left unchanged.
    pub fn extend(&self, x: &str, ty: Ty) -> Ctx {
        let mut bindings = self.bindings.clone();
        bindings.push((x.to_string(), ty));
        Ctx { bindings }
    }

    /// The type of the most recent binding of `x`, if there is one.
    pub fn lookup(&self, x: &str) -> Option<Ty> {
        self.bindings
            .iter()
            .rev()
            .find(|(name, _)| name == x)
            .map(|(_, ty)| *ty)
    }
}
// ANCHOR_END: ctx

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let parts: Vec<String> = self
            .bindings
            .iter()
            .map(|(x, ty)| format!("{x} : {ty}"))
            .collect();
        write!(f, "{}", parts.join(", "))
    }
}

// ANCHOR: derivation
/// The names of the typing rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    Num,
    Bool,
    Var,
    Add,
    Eq,
    If,
    Let,
}

/// A judgment Γ ⊢ e : τ.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Judgment {
    pub ctx: Ctx,
    pub expr: Expr,
    pub ty: Ty,
}

/// A derivation: a tree of rule instances. The root's conclusion is the
/// judgment being derived; the children derive the rule's premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Derivation {
    pub rule: Rule,
    pub conclusion: Judgment,
    pub premises: Vec<Derivation>,
}
// ANCHOR_END: derivation

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Rule::Num => "T-Num",
            Rule::Bool => "T-Bool",
            Rule::Var => "T-Var",
            Rule::Add => "T-Add",
            Rule::Eq => "T-Eq",
            Rule::If => "T-If",
            Rule::Let => "T-Let",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for Judgment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ctx = self.ctx.to_string();
        let gap = if ctx.is_empty() { "" } else { " " };
        write!(f, "{ctx}{gap}⊢ {} : {}", self.expr, self.ty)
    }
}

impl Derivation {
    /// The type in the conclusion.
    pub fn ty(&self) -> Ty {
        self.conclusion.ty
    }

    /// The number of rule instances in the tree.
    pub fn size(&self) -> usize {
        1 + self.premises.iter().map(Derivation::size).sum::<usize>()
    }

    /// The length of the longest path from the root to a leaf.
    pub fn height(&self) -> usize {
        1 + self
            .premises
            .iter()
            .map(Derivation::height)
            .max()
            .unwrap_or(0)
    }

    // ANCHOR: render
    /// The tree as indented text: the conclusion first, each premise below
    /// it and indented one level further.
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(0, &mut out);
        out
    }

    fn render_into(&self, depth: usize, out: &mut String) {
        let indent = "  ".repeat(depth);
        out.push_str(&format!("{indent}{}   [{}]\n", self.conclusion, self.rule));
        for premise in &self.premises {
            premise.render_into(depth + 1, out);
        }
    }
    // ANCHOR_END: render

    // ANCHOR: verify
    /// Check that every node is a correct instance of its rule. This does not
    /// search for anything: it only compares the judgments that are already
    /// written in the tree, which is why checking a derivation is much easier
    /// than finding one.
    pub fn verify(&self) -> bool {
        let Judgment { ctx, expr, ty } = &self.conclusion;
        let p = &self.premises;
        let at = |i: usize, e: &Expr, t: Ty, c: &Ctx| {
            let j = &p[i].conclusion;
            j.expr == *e && j.ty == t && j.ctx == *c
        };
        let shape_ok = match (self.rule, expr) {
            (Rule::Num, Expr::Num(_)) => p.is_empty() && *ty == Ty::Nat,
            (Rule::Bool, Expr::Bool(_)) => p.is_empty() && *ty == Ty::Bool,
            (Rule::Var, Expr::Var(x)) => p.is_empty() && ctx.lookup(x) == Some(*ty),
            (Rule::Add, Expr::Add(a, b)) => {
                p.len() == 2
                    && *ty == Ty::Nat
                    && at(0, a, Ty::Nat, ctx)
                    && at(1, b, Ty::Nat, ctx)
            }
            (Rule::Eq, Expr::Eq(a, b)) => {
                p.len() == 2
                    && *ty == Ty::Bool
                    && at(0, a, p[0].ty(), ctx)
                    && at(1, b, p[0].ty(), ctx)
            }
            (Rule::If, Expr::If(c, a, b)) => {
                p.len() == 3
                    && at(0, c, Ty::Bool, ctx)
                    && at(1, a, *ty, ctx)
                    && at(2, b, *ty, ctx)
            }
            (Rule::Let, Expr::Let(x, a, b)) => {
                p.len() == 2
                    && at(0, a, p[0].ty(), ctx)
                    && at(1, b, *ty, &ctx.extend(x, p[0].ty()))
            }
            _ => false,
        };
        shape_ok && p.iter().all(Derivation::verify)
    }
    // ANCHOR_END: verify
}

// ANCHOR: type_error
/// Why no derivation exists: the place where the search got stuck.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// T-Var does not apply: the variable is not in the context.
    Unbound { var: String },
    /// A premise asks for one type and the sub-expression has another.
    Expected {
        rule: Rule,
        expr: Expr,
        expected: Ty,
        found: Ty,
    },
    /// A rule asks for two sub-expressions of the same type, and they differ.
    Disagree {
        rule: Rule,
        left: (Expr, Ty),
        right: (Expr, Ty),
    },
}
// ANCHOR_END: type_error

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Unbound { var } => {
                write!(f, "T-Var: `{var}` is not in the context")
            }
            TypeError::Expected {
                rule,
                expr,
                expected,
                found,
            } => write!(
                f,
                "{rule}: `{expr}` should have type {expected}, but has type {found}"
            ),
            TypeError::Disagree { rule, left, right } => write!(
                f,
                "{rule}: `{}` : {} and `{}` : {} should have the same type",
                left.0, left.1, right.0, right.1
            ),
        }
    }
}

fn leaf(rule: Rule, ctx: &Ctx, expr: &Expr, ty: Ty) -> Derivation {
    node(rule, ctx, expr, ty, Vec::new())
}

fn node(
    rule: Rule,
    ctx: &Ctx,
    expr: &Expr,
    ty: Ty,
    premises: Vec<Derivation>,
) -> Derivation {
    Derivation {
        rule,
        conclusion: Judgment {
            ctx: ctx.clone(),
            expr: expr.clone(),
            ty,
        },
        premises,
    }
}

/// Demand that a premise derived type `want`.
fn expect(rule: Rule, expr: &Expr, d: &Derivation, want: Ty) -> Result<(), TypeError> {
    if d.ty() == want {
        Ok(())
    } else {
        Err(TypeError::Expected {
            rule,
            expr: expr.clone(),
            expected: want,
            found: d.ty(),
        })
    }
}

/// Demand that two premises derived the same type.
fn agree(
    rule: Rule,
    (a, da): (&Expr, &Derivation),
    (b, db): (&Expr, &Derivation),
) -> Result<(), TypeError> {
    if da.ty() == db.ty() {
        Ok(())
    } else {
        Err(TypeError::Disagree {
            rule,
            left: (a.clone(), da.ty()),
            right: (b.clone(), db.ty()),
        })
    }
}

// ANCHOR: check
/// Search for a derivation of Γ ⊢ e : τ, for some τ. The search is guided by
/// the shape of `e`: for each kind of expression exactly one rule can apply,
/// so the checker never has to guess or backtrack.
pub fn check(ctx: &Ctx, e: &Expr) -> Result<Derivation, TypeError> {
    match e {
        Expr::Num(_) => Ok(leaf(Rule::Num, ctx, e, Ty::Nat)),
        Expr::Bool(_) => Ok(leaf(Rule::Bool, ctx, e, Ty::Bool)),
        Expr::Var(x) => match ctx.lookup(x) {
            Some(ty) => Ok(leaf(Rule::Var, ctx, e, ty)),
            None => Err(TypeError::Unbound { var: x.clone() }),
        },
        Expr::Add(a, b) => {
            let da = check(ctx, a)?;
            expect(Rule::Add, a, &da, Ty::Nat)?;
            let db = check(ctx, b)?;
            expect(Rule::Add, b, &db, Ty::Nat)?;
            Ok(node(Rule::Add, ctx, e, Ty::Nat, vec![da, db]))
        }
        Expr::Eq(a, b) => {
            let da = check(ctx, a)?;
            let db = check(ctx, b)?;
            agree(Rule::Eq, (a, &da), (b, &db))?;
            Ok(node(Rule::Eq, ctx, e, Ty::Bool, vec![da, db]))
        }
        Expr::If(c, a, b) => {
            let dc = check(ctx, c)?;
            expect(Rule::If, c, &dc, Ty::Bool)?;
            let da = check(ctx, a)?;
            let db = check(ctx, b)?;
            agree(Rule::If, (a, &da), (b, &db))?;
            let ty = da.ty();
            Ok(node(Rule::If, ctx, e, ty, vec![dc, da, db]))
        }
        Expr::Let(x, a, b) => {
            let da = check(ctx, a)?;
            // The body is checked in the extended context Γ, x : τ1.
            let db = check(&ctx.extend(x, da.ty()), b)?;
            let ty = db.ty();
            Ok(node(Rule::Let, ctx, e, ty, vec![da, db]))
        }
    }
}
// ANCHOR_END: check

/// Just the type, when the derivation itself is not needed.
pub fn type_of(ctx: &Ctx, e: &Expr) -> Result<Ty, TypeError> {
    check(ctx, e).map(|d| d.ty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn ty(src: &str) -> Result<Ty, TypeError> {
        type_of(&Ctx::new(), &parse(src).unwrap())
    }

    #[test]
    fn each_rule_on_a_well_typed_program() {
        assert_eq!(ty("42"), Ok(Ty::Nat));
        assert_eq!(ty("false"), Ok(Ty::Bool));
        assert_eq!(ty("1 + 2"), Ok(Ty::Nat));
        assert_eq!(ty("1 == 2"), Ok(Ty::Bool));
        assert_eq!(ty("true == false"), Ok(Ty::Bool));
        assert_eq!(ty("if true then 1 else 2"), Ok(Ty::Nat));
        assert_eq!(ty("let x = 1 in x + x"), Ok(Ty::Nat));
        assert_eq!(ty("let b = 1 == 1 in if b then b else false"), Ok(Ty::Bool));
    }

    #[test]
    fn shadowing_uses_the_innermost_binding() {
        assert_eq!(ty("let x = true in let x = 5 in x + 1"), Ok(Ty::Nat));
        assert_eq!(ty("let x = 5 in let x = true in x"), Ok(Ty::Bool));
    }

    #[test]
    fn errors_name_the_rule_that_failed() {
        assert!(matches!(ty("y"), Err(TypeError::Unbound { .. })));
        assert!(matches!(
            ty("1 + true"),
            Err(TypeError::Expected {
                rule: Rule::Add,
                ..
            })
        ));
        assert!(matches!(
            ty("1 == true"),
            Err(TypeError::Disagree { rule: Rule::Eq, .. })
        ));
        assert!(matches!(
            ty("if 1 then 2 else 3"),
            Err(TypeError::Expected { rule: Rule::If, .. })
        ));
        assert!(matches!(
            ty("if true then 1 else false"),
            Err(TypeError::Disagree { rule: Rule::If, .. })
        ));
        // The variable is only in scope in the body of the `let`.
        assert!(matches!(
            ty("(let x = 1 in x) + x"),
            Err(TypeError::Unbound { .. })
        ));
    }

    #[test]
    fn the_running_example_has_the_expected_derivation() {
        let e = parse("let x = 3 in if x == 3 then x + 1 else 0").unwrap();
        let d = check(&Ctx::new(), &e).unwrap();
        assert_eq!(d.ty(), Ty::Nat);
        assert_eq!(d.rule, Rule::Let);
        assert_eq!(d.size(), 10);
        assert_eq!(d.height(), 4);
        assert!(d.verify());
    }

    #[test]
    fn tampered_derivations_are_rejected() {
        let e = parse("1 + 2").unwrap();
        let good = check(&Ctx::new(), &e).unwrap();
        assert!(good.verify());

        // Claim the wrong type in the conclusion.
        let mut bad = good.clone();
        bad.conclusion.ty = Ty::Bool;
        assert!(!bad.verify());

        // Use the wrong rule at the root.
        let mut bad = good.clone();
        bad.rule = Rule::Eq;
        assert!(!bad.verify());

        // Drop a premise.
        let mut bad = good;
        bad.premises.pop();
        assert!(!bad.verify());
    }
}
