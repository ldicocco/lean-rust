//! Renaming and substitution, exactly as in `code/lean/Book/Ch09/Syntax.lean`:
//! a renaming is a function from indices to indices, a substitution a function
//! from indices to terms, and both are *lifted* when they go under a binder.

use crate::syntax::Term;

// ANCHOR: rename
/// Applies the renaming `rho` to every free variable of `t`.
pub fn rename(t: &Term, rho: &dyn Fn(usize) -> usize) -> Term {
    let go = |u: &Term| Box::new(rename(u, rho));
    match t {
        Term::Var(i) => Term::Var(rho(*i)),
        Term::Lam(ty, body) => {
            // Under the binder, 0 is the new bound variable and stays 0; an
            // outer variable i + 1 is renamed to rho(i) and pushed up again.
            let lifted = |i: usize| if i == 0 { 0 } else { rho(i - 1) + 1 };
            Term::Lam(ty.clone(), Box::new(rename(body, &lifted)))
        }
        Term::App(f, a) => Term::App(go(f), go(a)),
        Term::True => Term::True,
        Term::False => Term::False,
        Term::If(c, t, e) => Term::If(go(c), go(t), go(e)),
        Term::Lit(n) => Term::Lit(*n),
        Term::Add(a, b) => Term::Add(go(a), go(b)),
        Term::IsZero(t) => Term::IsZero(go(t)),
    }
}

/// Every free variable moves up by one.
pub fn shift(t: &Term) -> Term {
    rename(t, &|i| i + 1)
}
// ANCHOR_END: rename

// ANCHOR: subst
/// Replaces every free variable `Var(i)` of `t` by `sigma(i)`.
pub fn subst(t: &Term, sigma: &dyn Fn(usize) -> Term) -> Term {
    let go = |u: &Term| Box::new(subst(u, sigma));
    match t {
        Term::Var(i) => sigma(*i),
        Term::Lam(ty, body) => {
            // Under the binder, 0 maps to itself, and the replacement for an
            // outer variable is shifted: it now lives under one more λ.
            let lifted = |i: usize| {
                if i == 0 {
                    Term::Var(0)
                } else {
                    shift(&sigma(i - 1))
                }
            };
            Term::Lam(ty.clone(), Box::new(subst(body, &lifted)))
        }
        Term::App(f, a) => Term::App(go(f), go(a)),
        Term::True => Term::True,
        Term::False => Term::False,
        Term::If(c, t, e) => Term::If(go(c), go(t), go(e)),
        Term::Lit(n) => Term::Lit(*n),
        Term::Add(a, b) => Term::Add(go(a), go(b)),
        Term::IsZero(t) => Term::IsZero(go(t)),
    }
}

/// The body of a λ with its bound variable replaced by `s`: variable 0
/// becomes `s`, and every other variable moves down by one.
pub fn instantiate(body: &Term, s: &Term) -> Term {
    subst(body, &|i| if i == 0 { s.clone() } else { Term::Var(i - 1) })
}
// ANCHOR_END: subst

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Ty, add, app, lam};

    #[test]
    fn shift_moves_only_free_variables() {
        let t = lam(Ty::Nat, add(Term::Var(0), Term::Var(1)));
        assert_eq!(shift(&t), lam(Ty::Nat, add(Term::Var(0), Term::Var(2))));
    }

    #[test]
    fn instantiate_matches_the_lean_examples() {
        let body = add(Term::Var(0), Term::Lit(1));
        assert_eq!(
            instantiate(&body, &Term::Lit(41)),
            add(Term::Lit(41), Term::Lit(1))
        );

        let body = lam(Ty::Nat, app(Term::Var(1), Term::Var(0)));
        let expected = lam(Ty::Nat, app(Term::Var(6), Term::Var(0)));
        assert_eq!(instantiate(&body, &Term::Var(5)), expected);

        let body = add(Term::Var(0), Term::Var(3));
        assert_eq!(
            instantiate(&body, &Term::Lit(7)),
            add(Term::Lit(7), Term::Var(2))
        );
    }

    #[test]
    fn identity_renaming_changes_nothing() {
        let t = crate::syntax::twice();
        assert_eq!(rename(&t, &|i| i), t);
        assert_eq!(subst(&t, &Term::Var), t);
    }
}
