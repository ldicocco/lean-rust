//! Types and terms of the simply typed λ-calculus with booleans and natural
//! numbers, in de Bruijn notation, and a printer.
//!
//! The definitions mirror `code/lean/Book/Ch09/Syntax.lean` constructor for
//! constructor, and the printer produces the same notation as the Lean one:
//! `λ:nat. #0 + 1` is `λ (x : nat). x + 1`, with the bound variable printed as
//! its index `#0`.

use std::fmt;

// ANCHOR: ty
/// The types: booleans, natural numbers and functions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Nat,
    Arrow(Box<Ty>, Box<Ty>),
}
// ANCHOR_END: ty

impl Ty {
    /// The function type `a → b`.
    pub fn arrow(a: Ty, b: Ty) -> Ty {
        Ty::Arrow(Box::new(a), Box::new(b))
    }
}

// ANCHOR: term
/// Terms in de Bruijn notation. `Var(i)` refers to the binder `i` levels up;
/// `Lam(τ, t)` is `λ (x : τ). t`, with the bound variable written `Var(0)` in `t`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(usize),
    Lam(Ty, Box<Term>),
    App(Box<Term>, Box<Term>),
    True,
    False,
    If(Box<Term>, Box<Term>, Box<Term>),
    Lit(u64),
    Add(Box<Term>, Box<Term>),
    IsZero(Box<Term>),
}
// ANCHOR_END: term

/// `λ (x : ty). body`
pub fn lam(ty: Ty, body: Term) -> Term {
    Term::Lam(ty, Box::new(body))
}

/// `f a`
pub fn app(f: Term, a: Term) -> Term {
    Term::App(Box::new(f), Box::new(a))
}

/// `if c then t else e`
pub fn ite(c: Term, t: Term, e: Term) -> Term {
    Term::If(Box::new(c), Box::new(t), Box::new(e))
}

/// `a + b`
pub fn add(a: Term, b: Term) -> Term {
    Term::Add(Box::new(a), Box::new(b))
}

/// `iszero t`
pub fn is_zero(t: Term) -> Term {
    Term::IsZero(Box::new(t))
}

impl Term {
    /// The number of constructors in the term: the measure the generator and
    /// the shrinker use.
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) | Term::True | Term::False | Term::Lit(_) => 1,
            Term::Lam(_, body) => 1 + body.size(),
            Term::IsZero(t) => 1 + t.size(),
            Term::App(a, b) | Term::Add(a, b) => 1 + a.size() + b.size(),
            Term::If(c, t, e) => 1 + c.size() + t.size() + e.size(),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Nat => write!(f, "nat"),
            // `→` associates to the right, so only a function on the left of
            // an arrow needs parentheses.
            Ty::Arrow(a, b) if matches!(**a, Ty::Arrow(..)) => write!(f, "({a}) → {b}"),
            Ty::Arrow(a, b) => write!(f, "{a} → {b}"),
        }
    }
}

/// Prints `t` at precedence level `prec`: 0 for `λ` and `if` (which extend as
/// far right as possible), 1 for `+`, 2 for application and `iszero`, 3 for
/// atoms. A term is parenthesized when its own level is below `prec`.
fn show(t: &Term, prec: u8) -> String {
    let paren = |level: u8, s: String| if prec > level { format!("({s})") } else { s };
    match t {
        Term::Var(i) => format!("#{i}"),
        Term::True => "true".to_string(),
        Term::False => "false".to_string(),
        Term::Lit(n) => n.to_string(),
        Term::Lam(ty, body) => {
            let annot = match ty {
                Ty::Arrow(..) => format!("({ty})"),
                _ => ty.to_string(),
            };
            paren(0, format!("λ:{annot}. {}", show(body, 0)))
        }
        Term::If(c, t, e) => paren(
            0,
            format!("if {} then {} else {}", show(c, 0), show(t, 0), show(e, 0)),
        ),
        Term::Add(a, b) => paren(1, format!("{} + {}", show(a, 1), show(b, 2))),
        Term::App(g, a) => paren(2, format!("{} {}", show(g, 2), show(a, 3))),
        Term::IsZero(t) => paren(2, format!("iszero {}", show(t, 3))),
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", show(self, 0))
    }
}

/// `λ (f : nat → nat). λ (x : nat). f (f x)`, as in the Lean file.
pub fn twice() -> Term {
    let f = || Term::Var(1);
    lam(
        Ty::arrow(Ty::Nat, Ty::Nat),
        lam(Ty::Nat, app(f(), app(f(), Term::Var(0)))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_like_lean() {
        let incr41 = app(lam(Ty::Nat, add(Term::Var(0), Term::Lit(1))), Term::Lit(41));
        assert_eq!(incr41.to_string(), "(λ:nat. #0 + 1) 41");
        assert_eq!(twice().to_string(), "λ:(nat → nat). λ:nat. #1 (#1 #0)");
    }

    #[test]
    fn prints_types_with_right_associative_arrows() {
        let t = Ty::arrow(Ty::arrow(Ty::Nat, Ty::Nat), Ty::arrow(Ty::Nat, Ty::Bool));
        assert_eq!(t.to_string(), "(nat → nat) → nat → bool");
    }

    #[test]
    fn parenthesizes_by_precedence() {
        let t = add(Term::Lit(1), add(Term::Lit(2), Term::Lit(3)));
        assert_eq!(t.to_string(), "1 + (2 + 3)");
        let t = is_zero(app(Term::Var(0), Term::Lit(1)));
        assert_eq!(t.to_string(), "iszero (#0 1)");
        let t = add(ite(Term::False, Term::Lit(1), Term::True), Term::Lit(2));
        assert_eq!(t.to_string(), "(if false then 1 else true) + 2");
    }

    #[test]
    fn size_counts_constructors() {
        assert_eq!(twice().size(), 7);
    }
}
