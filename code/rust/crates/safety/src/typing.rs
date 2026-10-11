//! The type checker: one case per typing rule, as in `typeOf` in
//! `code/lean/Book/Ch09/Typing.lean`. It can also run with a deliberately
//! broken rule for `if`, so that the property tests have a bug to find.

use crate::syntax::{Term, Ty};
use std::fmt;

/// Which set of typing rules to use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rules {
    /// The rules of the chapter (and of `HasType` in Lean).
    Sound,
    /// The same rules, except that `if` takes the type of its `then` branch
    /// and ignores the `else` branch (`BadHasType` in Lean).
    BrokenIf,
}

/// Why a term has no type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(usize),
    NotAFunction(Ty),
    Mismatch {
        place: &'static str,
        expected: Ty,
        found: Ty,
    },
    BranchesDiffer(Ty, Ty),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(i) => write!(f, "unbound variable #{i}"),
            TypeError::NotAFunction(ty) => {
                write!(f, "applying a non-function of type {ty}")
            }
            TypeError::Mismatch {
                place,
                expected,
                found,
            } => write!(f, "{place} should be {expected}, found {found}"),
            TypeError::BranchesDiffer(a, b) => {
                write!(f, "the branches of `if` differ: {a} and {b}")
            }
        }
    }
}

/// The type of `t` in context `ctx` (entry `i` is the type of `Var(i)`),
/// under the chapter's rules.
pub fn type_of(ctx: &[Ty], t: &Term) -> Result<Ty, TypeError> {
    type_of_with(Rules::Sound, ctx, t)
}

// ANCHOR: type_of
/// The type of `t` in context `ctx`, under the given rules.
pub fn type_of_with(rules: Rules, ctx: &[Ty], t: &Term) -> Result<Ty, TypeError> {
    let expect = |place, u: &Term, expected: Ty| -> Result<(), TypeError> {
        let found = type_of_with(rules, ctx, u)?;
        if found == expected {
            Ok(())
        } else {
            Err(TypeError::Mismatch {
                place,
                expected,
                found,
            })
        }
    };
    match t {
        // T-Var: look the variable up in the context.
        Term::Var(i) => ctx.get(*i).cloned().ok_or(TypeError::UnboundVariable(*i)),
        // T-Lam: check the body in the context extended with the parameter.
        Term::Lam(param, body) => {
            let mut inner = vec![param.clone()];
            inner.extend_from_slice(ctx);
            let result = type_of_with(rules, &inner, body)?;
            Ok(Ty::arrow(param.clone(), result))
        }
        // T-App: a function of type σ → τ applied to an argument of type σ.
        Term::App(f, a) => match type_of_with(rules, ctx, f)? {
            Ty::Arrow(param, result) => {
                expect("the argument", a, *param)?;
                Ok(*result)
            }
            other => Err(TypeError::NotAFunction(other)),
        },
        // T-True, T-False, T-Lit.
        Term::True | Term::False => Ok(Ty::Bool),
        Term::Lit(_) => Ok(Ty::Nat),
        // T-If: a boolean condition and two branches of the same type.
        Term::If(c, then_branch, else_branch) => {
            expect("the condition of `if`", c, Ty::Bool)?;
            let ty_then = type_of_with(rules, ctx, then_branch)?;
            let ty_else = type_of_with(rules, ctx, else_branch)?;
            match rules {
                Rules::Sound if ty_then != ty_else => {
                    Err(TypeError::BranchesDiffer(ty_then, ty_else))
                }
                // The broken rule never compares the two branches.
                _ => Ok(ty_then),
            }
        }
        // T-Add and T-IsZero.
        Term::Add(a, b) => {
            expect("the left operand of `+`", a, Ty::Nat)?;
            expect("the right operand of `+`", b, Ty::Nat)?;
            Ok(Ty::Nat)
        }
        Term::IsZero(n) => {
            expect("the argument of `iszero`", n, Ty::Nat)?;
            Ok(Ty::Bool)
        }
    }
}
// ANCHOR_END: type_of

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{add, app, ite, lam, twice};

    #[test]
    fn twice_has_the_expected_type() {
        let nat_to_nat = Ty::arrow(Ty::Nat, Ty::Nat);
        assert_eq!(
            type_of(&[], &twice()),
            Ok(Ty::arrow(nat_to_nat.clone(), nat_to_nat))
        );
    }

    #[test]
    fn rejects_ill_typed_terms() {
        let bad = add(Term::True, Term::Lit(1));
        assert_eq!(
            type_of(&[], &bad),
            Err(TypeError::Mismatch {
                place: "the left operand of `+`",
                expected: Ty::Nat,
                found: Ty::Bool
            })
        );
        assert_eq!(
            type_of(&[], &app(Term::Lit(3), Term::True)),
            Err(TypeError::NotAFunction(Ty::Nat))
        );
        assert_eq!(
            type_of(&[], &Term::Var(0)),
            Err(TypeError::UnboundVariable(0))
        );
    }

    #[test]
    fn variables_are_looked_up_by_index() {
        let ctx = [Ty::Bool, Ty::Nat];
        assert_eq!(type_of(&ctx, &Term::Var(1)), Ok(Ty::Nat));
        // Under a binder, the old #1 is #2.
        let t = lam(Ty::Bool, Term::Var(2));
        assert_eq!(type_of(&ctx, &t), Ok(Ty::arrow(Ty::Bool, Ty::Nat)));
    }

    #[test]
    fn the_broken_rule_accepts_mismatched_branches() {
        let t = ite(Term::False, Term::Lit(1), Term::True);
        assert_eq!(
            type_of(&[], &t),
            Err(TypeError::BranchesDiffer(Ty::Nat, Ty::Bool))
        );
        assert_eq!(type_of_with(Rules::BrokenIf, &[], &t), Ok(Ty::Nat));
    }
}
