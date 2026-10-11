//! Nameless terms: de Bruijn indices, shifting and substitution.
//!
//! A variable is the number of `λ`s between the occurrence and its binder:
//! `λx. λy. x` becomes `λ. λ. 1`. Free variables are numbered past the
//! binders, according to a list of free names (the *naming context*).

use crate::term::Term;
use std::fmt;

// ANCHOR: db_term
/// A λ-term with de Bruijn indices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DbTerm {
    /// A variable: the number of binders to skip to reach its `λ`.
    Var(usize),
    /// An abstraction. The binder has no name.
    Lam(Box<DbTerm>),
    /// An application.
    App(Box<DbTerm>, Box<DbTerm>),
}
// ANCHOR_END: db_term

fn db_lam(body: DbTerm) -> DbTerm {
    DbTerm::Lam(Box::new(body))
}

fn db_app(t: DbTerm, u: DbTerm) -> DbTerm {
    DbTerm::App(Box::new(t), Box::new(u))
}

// ANCHOR: to_de_bruijn
/// Converts a named term to de Bruijn form. `free` lists the names of the free
/// variables: the free variable `free[i]` becomes index `i` (plus the number of
/// enclosing binders).
pub fn to_de_bruijn(t: &Term, free: &[&str]) -> Result<DbTerm, String> {
    // `scope` holds the names of the enclosing binders, innermost last.
    fn go(t: &Term, scope: &mut Vec<String>, free: &[&str]) -> Result<DbTerm, String> {
        match t {
            Term::Var(x) => {
                // The nearest binder named x wins: that is how shadowing works.
                if let Some(pos) = scope.iter().rev().position(|y| y == x) {
                    Ok(DbTerm::Var(pos))
                } else if let Some(i) = free.iter().position(|y| y == x) {
                    Ok(DbTerm::Var(scope.len() + i))
                } else {
                    Err(format!("free variable `{x}` is not in the naming context"))
                }
            }
            Term::Lam(x, body) => {
                scope.push(x.clone());
                let body = go(body, scope, free);
                scope.pop();
                Ok(db_lam(body?))
            }
            Term::App(f, a) => Ok(db_app(go(f, scope, free)?, go(a, scope, free)?)),
        }
    }
    go(t, &mut Vec::new(), free)
}
// ANCHOR_END: to_de_bruijn

impl DbTerm {
    // ANCHOR: shift
    /// Adds one to every index that is at least `cutoff`. Indices below the
    /// cutoff are bound inside the term and do not move; the others are free.
    pub fn shift(&self, cutoff: usize) -> DbTerm {
        match self {
            DbTerm::Var(k) if *k < cutoff => DbTerm::Var(*k),
            DbTerm::Var(k) => DbTerm::Var(k + 1),
            DbTerm::Lam(body) => db_lam(body.shift(cutoff + 1)),
            DbTerm::App(t, u) => db_app(t.shift(cutoff), u.shift(cutoff)),
        }
    }
    // ANCHOR_END: shift

    // ANCHOR: db_subst
    /// `self[j := s]`: replaces index `j` by `s` and lowers the free indices
    /// above `j` by one (the binder of `j` is about to disappear). Each time we
    /// go under a `λ`, `j` grows by one and `s` is shifted, so that the free
    /// variables of `s` keep pointing past the new binder.
    pub fn subst(&self, j: usize, s: &DbTerm) -> DbTerm {
        match self {
            DbTerm::Var(k) if *k < j => DbTerm::Var(*k),
            DbTerm::Var(k) if *k == j => s.clone(),
            DbTerm::Var(k) => DbTerm::Var(k - 1),
            DbTerm::Lam(body) => db_lam(body.subst(j + 1, &s.shift(0))),
            DbTerm::App(t, u) => db_app(t.subst(j, s), u.subst(j, s)),
        }
    }
    // ANCHOR_END: db_subst

    /// The same substitution with the shift forgotten: a deliberately wrong
    /// version, used to show that the shift is what prevents capture.
    pub fn subst_without_shift(&self, j: usize, s: &DbTerm) -> DbTerm {
        match self {
            DbTerm::Var(k) if *k < j => DbTerm::Var(*k),
            DbTerm::Var(k) if *k == j => s.clone(),
            DbTerm::Var(k) => DbTerm::Var(k - 1),
            DbTerm::Lam(body) => db_lam(body.subst_without_shift(j + 1, s)),
            DbTerm::App(t, u) => {
                db_app(t.subst_without_shift(j, s), u.subst_without_shift(j, s))
            }
        }
    }

    // ANCHOR: db_step
    /// One step of normal-order reduction: contract the leftmost-outermost
    /// redex, `(λ. t) s` becoming `t[0 := s]`.
    pub fn step_normal(&self) -> Option<DbTerm> {
        match self {
            DbTerm::Var(_) => None,
            DbTerm::Lam(body) => body.step_normal().map(db_lam),
            DbTerm::App(f, a) => {
                if let DbTerm::Lam(body) = &**f {
                    return Some(body.subst(0, a));
                }
                if let Some(f2) = f.step_normal() {
                    return Some(db_app(f2, (**a).clone()));
                }
                a.step_normal().map(|a2| db_app((**f).clone(), a2))
            }
        }
    }
    // ANCHOR_END: db_step

    /// Normal-order reduction for at most `fuel` steps. Returns the final term
    /// and the number of steps, or `None` if the fuel ran out first.
    pub fn normalize(&self, fuel: usize) -> Option<(DbTerm, usize)> {
        let mut t = self.clone();
        for steps in 0..=fuel {
            match t.step_normal() {
                None => return Some((t, steps)),
                Some(next) => t = next,
            }
        }
        None
    }
}

impl fmt::Display for DbTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DbTerm::Var(k) => write!(f, "{k}"),
            DbTerm::Lam(body) => write!(f, "λ. {body}"),
            DbTerm::App(t, u) => {
                match **t {
                    DbTerm::Lam(..) => write!(f, "({t})")?,
                    _ => write!(f, "{t}")?,
                }
                match **u {
                    DbTerm::Var(_) => write!(f, " {u}"),
                    _ => write!(f, " ({u})"),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    fn db(s: &str) -> DbTerm {
        to_de_bruijn(&parse(s).unwrap(), &[]).unwrap()
    }

    #[test]
    fn conversion() {
        assert_eq!(db("λx. λy. x").to_string(), "λ. λ. 1");
        assert_eq!(db("λx. λy. x (y x)").to_string(), "λ. λ. 1 (0 1)");
        // Shadowing: the inner x refers to the inner binder.
        assert_eq!(db("λx. λx. x").to_string(), "λ. λ. 0");
        // Free variables are numbered past the binders.
        let t = to_de_bruijn(&parse("λx. x z").unwrap(), &["z"]).unwrap();
        assert_eq!(t.to_string(), "λ. 0 1");
        assert!(to_de_bruijn(&parse("λx. y").unwrap(), &[]).is_err());
    }

    #[test]
    fn alpha_equivalent_terms_are_equal() {
        assert_eq!(db("λx. λy. x"), db("λa. λb. a"));
        assert_ne!(db("λx. λy. x"), db("λx. λy. y"));
    }

    #[test]
    fn shifting() {
        // λ. 0 2: index 0 is bound, index 2 is free (it is 1 outside the λ).
        let t = DbTerm::Lam(Box::new(db_app(DbTerm::Var(0), DbTerm::Var(2))));
        assert_eq!(t.shift(0).to_string(), "λ. 0 3");
    }

    #[test]
    fn beta_with_a_free_variable_in_the_argument() {
        // (λx. λy. x) z, in the naming context [z]: (λ. λ. 1) 0.
        let k = db("λx. λy. x");
        let DbTerm::Lam(body) = &k else { panic!() };
        let z = DbTerm::Var(0);
        // Correct: λ. 1, the constant function returning z.
        assert_eq!(body.subst(0, &z).to_string(), "λ. 1");
        // Without the shift, z is captured: λ. 0, the identity.
        assert_eq!(body.subst_without_shift(0, &z).to_string(), "λ. 0");
    }

    #[test]
    fn normal_order_on_church_numerals() {
        let two_plus_two =
            db("(λm. λn. λf. λx. m f (n f x)) (λf. λx. f (f x)) (λf. λx. f (f x))");
        let (nf, _) = two_plus_two.normalize(100).unwrap();
        assert_eq!(nf, db("λf. λx. f (f (f (f x)))"));
    }

    #[test]
    fn omega_runs_out_of_fuel() {
        let omega = db("(λx. x x) (λx. x x)");
        assert_eq!(omega.step_normal(), Some(omega.clone()));
        assert!(omega.normalize(1000).is_none());
    }
}
