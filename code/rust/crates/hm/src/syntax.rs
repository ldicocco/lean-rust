//! The abstract syntax of mini-ML.
//!
//! ```text
//! e ::= n | true | false | x          literals and variables
//!     | fun x -> e                    function (λx. e)
//!     | e e                           application
//!     | let x = e in e                local definition (polymorphic)
//!     | let rec f = e in e            recursive definition
//!     | if e then e else e            conditional
//!     | (e, e)                        pair
//! ```
//!
//! Everything else the parser accepts is sugar for these forms: operators
//! (`a + b` is `(+) a b`), lists (`[1, 2]` is `cons 1 (cons 2 nil)`),
//! functions of several parameters (`fun x y -> e` is `fun x -> fun y -> e`)
//! and function definitions (`let f x = e in ...` is `let f = fun x -> e in ...`).
//! The operators and the list functions are ordinary names, given polymorphic
//! types by the prelude (see `infer.rs`).

// ANCHOR: syntax
/// A region of the source text, as byte offsets `start..end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// An expression together with the part of the source it came from, so that
/// error messages can point at it.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Int(i64),
    Bool(bool),
    Var(String),
    Lam(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    LetRec(String, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Pair(Box<Expr>, Box<Expr>),
}
// ANCHOR_END: syntax

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }

    /// The smallest span covering both `self` and `other`.
    pub fn to(self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Expr {
        Expr { kind, span }
    }

    /// The source text of this expression.
    pub fn text<'a>(&self, source: &'a str) -> &'a str {
        &source[self.span.start..self.span.end]
    }
}
