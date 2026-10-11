//! The abstract syntax of Arith: types and expressions as Rust enums.
//!
//! The grammar, in BNF:
//!
//! ```text
//! τ ::= Nat | Bool
//! e ::= n | true | false | x | e + e | e == e
//!     | if e then e else e | let x = e in e
//! ```
//!
//! Each alternative of the grammar becomes one variant of an enum. The
//! sub-expressions are boxed because `Expr` is a recursive type: without the
//! indirection it would have infinite size (Chapter 11 explains why).

use std::fmt;

// ANCHOR: ty
/// The types of Arith: τ ::= Nat | Bool.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    Nat,
    Bool,
}
// ANCHOR_END: ty

// ANCHOR: expr
/// The expressions of Arith, one variant per alternative of the grammar.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// A natural-number literal `n`.
    Num(u64),
    /// A boolean literal, `true` or `false`.
    Bool(bool),
    /// A variable `x`.
    Var(String),
    /// `e1 + e2`
    Add(Box<Expr>, Box<Expr>),
    /// `e1 == e2`
    Eq(Box<Expr>, Box<Expr>),
    /// `if c then e1 else e2`
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `let x = e1 in e2`
    Let(String, Box<Expr>, Box<Expr>),
}
// ANCHOR_END: expr

// ANCHOR: smart_constructors
/// Short constructors, so that tests and examples can build trees by hand
/// without writing `Box::new` everywhere.
pub mod build {
    use super::Expr;

    pub fn num(n: u64) -> Expr {
        Expr::Num(n)
    }
    pub fn boolean(b: bool) -> Expr {
        Expr::Bool(b)
    }
    pub fn var(x: &str) -> Expr {
        Expr::Var(x.to_string())
    }
    pub fn add(e1: Expr, e2: Expr) -> Expr {
        Expr::Add(Box::new(e1), Box::new(e2))
    }
    pub fn eq(e1: Expr, e2: Expr) -> Expr {
        Expr::Eq(Box::new(e1), Box::new(e2))
    }
    pub fn ite(c: Expr, e1: Expr, e2: Expr) -> Expr {
        Expr::If(Box::new(c), Box::new(e1), Box::new(e2))
    }
    pub fn let_in(x: &str, e1: Expr, e2: Expr) -> Expr {
        Expr::Let(x.to_string(), Box::new(e1), Box::new(e2))
    }
}
// ANCHOR_END: smart_constructors

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Nat => write!(f, "Nat"),
            Ty::Bool => write!(f, "Bool"),
        }
    }
}

// ANCHOR: precedence
/// How tightly an expression binds, used to decide where parentheses are
/// needed when printing. `let` and `if` extend as far to the right as
/// possible, so they bind most loosely; literals and variables are atoms.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Open,
    Compare,
    Sum,
    Atom,
}

impl Expr {
    fn prec(&self) -> Prec {
        match self {
            Expr::Let(..) | Expr::If(..) => Prec::Open,
            Expr::Eq(..) => Prec::Compare,
            Expr::Add(..) => Prec::Sum,
            Expr::Num(_) | Expr::Bool(_) | Expr::Var(_) => Prec::Atom,
        }
    }

    /// Print `self`, adding parentheses if it binds more loosely than `min`.
    fn fmt_at(&self, min: Prec, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.prec() < min {
            write!(f, "(")?;
            self.fmt_at(Prec::Open, f)?;
            return write!(f, ")");
        }
        match self {
            Expr::Num(n) => write!(f, "{n}"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Var(x) => write!(f, "{x}"),
            // `+` associates to the left: `1 + 2 + 3` is `(1 + 2) + 3`, so the
            // right operand must be printed one level tighter.
            Expr::Add(a, b) => {
                a.fmt_at(Prec::Sum, f)?;
                write!(f, " + ")?;
                b.fmt_at(Prec::Atom, f)
            }
            // `==` does not associate at all: both sides must be sums.
            Expr::Eq(a, b) => {
                a.fmt_at(Prec::Sum, f)?;
                write!(f, " == ")?;
                b.fmt_at(Prec::Sum, f)
            }
            Expr::If(c, a, b) => {
                write!(f, "if ")?;
                c.fmt_at(Prec::Open, f)?;
                write!(f, " then ")?;
                a.fmt_at(Prec::Open, f)?;
                write!(f, " else ")?;
                b.fmt_at(Prec::Open, f)
            }
            Expr::Let(x, a, b) => {
                write!(f, "let {x} = ")?;
                a.fmt_at(Prec::Open, f)?;
                write!(f, " in ")?;
                b.fmt_at(Prec::Open, f)
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(Prec::Open, f)
    }
}
// ANCHOR_END: precedence

#[cfg(test)]
mod tests {
    use super::build::*;

    #[test]
    fn printing_adds_only_the_parentheses_that_are_needed() {
        assert_eq!(add(add(num(1), num(2)), num(3)).to_string(), "1 + 2 + 3");
        assert_eq!(add(num(1), add(num(2), num(3))).to_string(), "1 + (2 + 3)");
        assert_eq!(eq(add(var("x"), num(1)), num(2)).to_string(), "x + 1 == 2");
        assert_eq!(
            eq(eq(num(1), num(1)), boolean(true)).to_string(),
            "(1 == 1) == true"
        );
        let e = add(ite(boolean(true), num(1), num(2)), num(3));
        assert_eq!(e.to_string(), "(if true then 1 else 2) + 3");
        let e = let_in("x", num(1), ite(var("x"), num(1), num(2)));
        assert_eq!(e.to_string(), "let x = 1 in if x then 1 else 2");
    }
}
