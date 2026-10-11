//! Named λ-terms: syntax, free variables, α-equivalence and capture-avoiding
//! substitution.

use std::collections::BTreeSet;
use std::fmt;

// ANCHOR: term
/// A term of the untyped λ-calculus, with variables as names:
/// `t ::= x | λx. t | t t`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// A variable `x`.
    Var(String),
    /// An abstraction `λx. t`: the function that sends `x` to `t`.
    Lam(String, Box<Term>),
    /// An application `t u`: the function `t` applied to the argument `u`.
    App(Box<Term>, Box<Term>),
}
// ANCHOR_END: term

/// The variable `x`.
pub fn var(x: &str) -> Term {
    Term::Var(x.to_string())
}

/// The abstraction `λx. body`.
pub fn lam(x: &str, body: Term) -> Term {
    Term::Lam(x.to_string(), Box::new(body))
}

/// The application `f a`.
pub fn app(f: Term, a: Term) -> Term {
    Term::App(Box::new(f), Box::new(a))
}

/// The application `f a1 a2 ... an`, which means `(((f a1) a2) ... an)`.
pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, app)
}

impl Term {
    // ANCHOR: free_vars
    /// The free variables of a term: the variables that are not bound by an
    /// enclosing `λ`.
    pub fn free_vars(&self) -> BTreeSet<String> {
        match self {
            Term::Var(x) => BTreeSet::from([x.clone()]),
            Term::Lam(x, body) => {
                let mut fv = body.free_vars();
                fv.remove(x);
                fv
            }
            Term::App(t, u) => {
                let mut fv = t.free_vars();
                fv.extend(u.free_vars());
                fv
            }
        }
    }
    // ANCHOR_END: free_vars

    /// Every variable name that occurs in the term, free or bound.
    pub fn all_names(&self) -> BTreeSet<String> {
        match self {
            Term::Var(x) => BTreeSet::from([x.clone()]),
            Term::Lam(x, body) => {
                let mut names = body.all_names();
                names.insert(x.clone());
                names
            }
            Term::App(t, u) => {
                let mut names = t.all_names();
                names.extend(u.all_names());
                names
            }
        }
    }

    /// Is the term closed (no free variables)?
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    /// The number of nodes in the syntax tree.
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) => 1,
            Term::Lam(_, body) => 1 + body.size(),
            Term::App(t, u) => 1 + t.size() + u.size(),
        }
    }

    // ANCHOR: subst
    /// Capture-avoiding substitution `self[x := s]`: replace the free
    /// occurrences of `x` in `self` by `s`, renaming bound variables of `self`
    /// when they would capture a free variable of `s`.
    pub fn subst(&self, x: &str, s: &Term) -> Term {
        match self {
            Term::Var(y) if y == x => s.clone(),
            Term::Var(_) => self.clone(),
            Term::App(t, u) => app(t.subst(x, s), u.subst(x, s)),
            // `λx. body` binds x: there is no free x inside, nothing to do.
            Term::Lam(y, _) if y == x => self.clone(),
            Term::Lam(y, body) => {
                if s.free_vars().contains(y) && body.free_vars().contains(x) {
                    // Going under `λy` would capture the free `y` of `s`.
                    // Rename the bound `y` to a name used nowhere nearby.
                    let mut avoid = s.free_vars();
                    avoid.extend(body.all_names());
                    avoid.insert(x.to_string());
                    let fresh_y = fresh(y, &avoid);
                    let renamed = body.subst(y, &Term::Var(fresh_y.clone()));
                    lam(&fresh_y, renamed.subst(x, s))
                } else {
                    lam(y, body.subst(x, s))
                }
            }
        }
    }
    // ANCHOR_END: subst

    /// α-equivalence: equal up to the names of bound variables. Implemented by
    /// converting both terms to de Bruijn indices and comparing.
    pub fn alpha_eq(&self, other: &Term) -> bool {
        let mut free: Vec<String> = self.free_vars().into_iter().collect();
        for x in other.free_vars() {
            if !free.contains(&x) {
                free.push(x);
            }
        }
        let names: Vec<&str> = free.iter().map(String::as_str).collect();
        match (
            crate::debruijn::to_de_bruijn(self, &names),
            crate::debruijn::to_de_bruijn(other, &names),
        ) {
            (Ok(a), Ok(b)) => a == b,
            _ => false,
        }
    }
}

// ANCHOR: fresh
/// A variant of `base` (with primes appended) that is not in `avoid`.
pub fn fresh(base: &str, avoid: &BTreeSet<String>) -> String {
    let mut name = format!("{base}'");
    while avoid.contains(&name) {
        name.push('\'');
    }
    name
}
// ANCHOR_END: fresh

/// Prints with the usual conventions: application associates to the left and
/// the body of a `λ` extends as far to the right as possible, so
/// `λx. λy. x y z` means `λx. (λy. ((x y) z))`.
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{x}"),
            Term::Lam(x, body) => write!(f, "λ{x}. {body}"),
            Term::App(t, u) => {
                match **t {
                    Term::Lam(..) => write!(f, "({t})")?,
                    _ => write!(f, "{t}")?,
                }
                match **u {
                    Term::Var(_) => write!(f, " {u}"),
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

    fn p(s: &str) -> Term {
        parse(s).unwrap()
    }

    #[test]
    fn free_variables() {
        let fv = p("λx. x y (λy. y z)").free_vars();
        assert_eq!(fv, BTreeSet::from(["y".to_string(), "z".to_string()]));
        assert!(p("λx. λy. x").is_closed());
        // The same name can occur free and bound in one term.
        assert_eq!(
            p("x (λx. x)").free_vars(),
            BTreeSet::from(["x".to_string()])
        );
    }

    #[test]
    fn printing_round_trips() {
        for s in [
            "λx. x",
            "λx. λy. x y z",
            "(λx. x x) (λx. x x)",
            "f (λx. x) y",
            "x (y z) w",
            "λf. λx. f (f x)",
        ] {
            assert_eq!(p(s).to_string(), s);
        }
    }

    #[test]
    fn substitution_without_capture() {
        assert_eq!(p("x y").subst("x", &p("λz. z")), p("(λz. z) y"));
        // A bound x is not replaced.
        assert_eq!(p("λx. x").subst("x", &p("y")), p("λx. x"));
    }

    #[test]
    fn substitution_renames_to_avoid_capture() {
        // (λy. x)[x := y] must not become the identity λy. y.
        let result = p("λy. x").subst("x", &p("y"));
        assert_eq!(result, p("λy'. y"));
        assert!(!result.alpha_eq(&p("λy. y")));
        // The fresh name also avoids names already used in the body.
        let result = p("λy. x y'").subst("x", &p("y"));
        assert_eq!(result, p("λy''. y y'"));
    }

    #[test]
    fn alpha_equivalence() {
        assert!(p("λx. x").alpha_eq(&p("λy. y")));
        assert!(p("λx. λy. x").alpha_eq(&p("λa. λb. a")));
        assert!(!p("λx. λy. x").alpha_eq(&p("λx. λy. y")));
        // Free variables must match by name.
        assert!(p("λx. z").alpha_eq(&p("λy. z")));
        assert!(!p("λx. z").alpha_eq(&p("λx. w")));
    }

    #[test]
    fn fresh_names() {
        let avoid = BTreeSet::from(["y'".to_string()]);
        assert_eq!(fresh("y", &avoid), "y''");
        assert_eq!(fresh("y", &BTreeSet::new()), "y'");
    }
}
