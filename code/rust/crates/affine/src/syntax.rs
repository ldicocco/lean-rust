//! The abstract syntax of the checker's input language: the affine
//! λ-calculus of Chapter 22 written with Rust-like syntax, plus the few
//! declarations Chapter 23 needs (structs, `#[derive(Clone, Copy)]`,
//! `impl Drop`).

use std::fmt;

/// A region of the source text, as byte offsets `start..end`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }

    /// The smallest span that covers both `self` and `other`.
    pub fn to(self, other: Span) -> Span {
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }
}

// ANCHOR: ty
/// The types of λ^aff, in Rust notation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `()`, the unit type 𝟏.
    Unit,
    /// A base type such as `String`, `File`, `i32`, or a declared struct.
    Named(String),
    /// `(A, B)`, the multiplicative pair A ⊗ B.
    Tuple(Box<Ty>, Box<Ty>),
    /// `FnOnce(A) -> B`, the affine function type A ⊸ B.
    Fn(Box<Ty>, Box<Ty>),
    /// `With<A, B>`, the additive pair A & B: an offer of either one.
    With(Box<Ty>, Box<Ty>),
    /// `Either<A, B>`, the sum A ⊕ B.
    Either(Box<Ty>, Box<Ty>),
    /// `&A` and `&mut A` (Chapter 23): opaque permissions, only used to
    /// show which of them are `Copy`.
    Ref { mutable: bool, inner: Box<Ty> },
    /// `Rc<A>` (Chapter 23): shared ownership with a reference count.
    Rc(Box<Ty>),
}
// ANCHOR_END: ty

impl Ty {
    pub fn named(name: &str) -> Ty {
        Ty::Named(name.to_string())
    }
    pub fn tuple(a: Ty, b: Ty) -> Ty {
        Ty::Tuple(Box::new(a), Box::new(b))
    }
    pub fn func(a: Ty, b: Ty) -> Ty {
        Ty::Fn(Box::new(a), Box::new(b))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Unit => write!(f, "()"),
            Ty::Named(n) => write!(f, "{n}"),
            Ty::Tuple(a, b) => write!(f, "({a}, {b})"),
            Ty::Fn(a, b) => write!(f, "FnOnce({a}) -> {b}"),
            Ty::With(a, b) => write!(f, "With<{a}, {b}>"),
            Ty::Either(a, b) => write!(f, "Either<{a}, {b}>"),
            Ty::Ref {
                mutable: false,
                inner,
            } => write!(f, "&{inner}"),
            Ty::Ref {
                mutable: true,
                inner,
            } => write!(f, "&mut {inner}"),
            Ty::Rc(a) => write!(f, "Rc<{a}>"),
        }
    }
}

/// A name together with where it was written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// A `let` pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    /// `let x = ...`
    Var(Ident),
    /// `let (x, y) = ...`, the eliminator of `(A, B)`.
    Pair(Ident, Ident),
    /// `let _ = ...`, and the statement `e;`: the value is discarded.
    Wild,
}

/// A projection out of a place: `.0`, `.1`, `.field`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proj {
    Index(usize),
    Field(String),
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Proj::Index(i) => write!(f, ".{i}"),
            Proj::Field(n) => write!(f, ".{n}"),
        }
    }
}

/// An expression with its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

/// The expressions. Blocks `{ let x = e1; e2 }` are parsed into nested
/// `Let`s, so there is no separate block node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// A variable.
    Var(String),
    /// `()`
    Unit,
    /// An integer literal, of type `i32`.
    Int(i64),
    /// `(e1, e2)`
    Tuple(Box<Expr>, Box<Expr>),
    /// `let pat: ty = value; body` (the type annotation is optional).
    Let {
        pat: Pat,
        ty: Option<Ty>,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    /// `|x: T| body`; `head` is the span of `|x: T|`.
    Closure {
        param: Ident,
        ty: Ty,
        body: Box<Expr>,
        head: Span,
    },
    /// `f(a, b, ...)`: a call of a closure in scope or of a declared `fn`.
    Call {
        callee: Ident,
        args: Vec<Expr>,
    },
    /// `with(e1, e2)`, the additive pair.
    With(Box<Expr>, Box<Expr>),
    /// `Left(e)` and `Right(e)`.
    Left(Box<Expr>),
    Right(Box<Expr>),
    /// `match e { Left(x) => e1, Right(y) => e2 }`
    Match {
        scrutinee: Box<Expr>,
        left: (Ident, Box<Expr>),
        right: (Ident, Box<Expr>),
    },
    /// `e.0`, `e.1`, `e.name`, and the projections `e.fst`, `e.snd` of a `With`.
    Field(Box<Expr>, Proj, Span),
    /// `e.clone()`
    Clone(Box<Expr>),
    /// `Name { field: e, ... }`
    StructLit {
        name: Ident,
        fields: Vec<(Ident, Expr)>,
    },
}

/// A function: parameters, result type, and a body (or none, for a function
/// that the environment provides, like `fn close(f: File);`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDef {
    pub name: Ident,
    pub params: Vec<(Ident, Ty)>,
    pub ret: Ty,
    pub body: Option<Expr>,
}

/// A struct declaration with its `#[derive(...)]` list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructDef {
    pub name: Ident,
    pub derives: Vec<Ident>,
    /// Field name, type, and the span of `name: Type`.
    pub fields: Vec<(Ident, Ty, Span)>,
}

/// A top-level item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Fn(FnDef),
    Struct(StructDef),
    /// `impl Drop for Name {}`: the type has a destructor.
    DropImpl {
        ty: Ident,
        span: Span,
    },
}

/// A whole program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
    pub items: Vec<Item>,
}

impl Program {
    pub fn function(&self, name: &str) -> Option<&FnDef> {
        self.items.iter().find_map(|item| match item {
            Item::Fn(f) if f.name.name == name => Some(f),
            _ => None,
        })
    }

    pub fn structure(&self, name: &str) -> Option<&StructDef> {
        self.items.iter().find_map(|item| match item {
            Item::Struct(s) if s.name.name == name => Some(s),
            _ => None,
        })
    }

    pub fn has_drop(&self, name: &str) -> bool {
        self.items
            .iter()
            .any(|item| matches!(item, Item::DropImpl { ty, .. } if ty.name == name))
    }
}

/// Print an expression on one line, in the input syntax. Sequences (`let`
/// and `;`) are put in braces when they appear inside another expression.
pub fn show_expr(e: &Expr) -> String {
    show(e, true)
}

/// Like [`show_expr`], but the arms of a `match`, the body of a long `let`
/// and the long components of a long pair or call are abbreviated to `…`
/// (derivations show them in the premises).
pub fn show_expr_brief(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Match {
            scrutinee,
            left,
            right,
        } => format!(
            "match {} {{ Left({}) => …, Right({}) => … }}",
            show(scrutinee, false),
            left.0.name,
            right.0.name
        ),
        // A long `let`: the body is shown in the premise.
        ExprKind::Let { pat, ty, value, .. } if show_expr(e).chars().count() > 40 => {
            let value = show(value, false);
            let ann = ty.as_ref().map(|t| format!(": {t}")).unwrap_or_default();
            match pat {
                Pat::Var(x) => format!("let {}{ann} = {value}; …", x.name),
                Pat::Pair(x, y) => {
                    format!("let ({}, {}){ann} = {value}; …", x.name, y.name)
                }
                Pat::Wild => format!("{value}; …"),
            }
        }
        // A long pair or call: its components are shown in the premises.
        ExprKind::Tuple(a, b) if show_expr(e).chars().count() > 40 => {
            format!("({}, {})", short(a), short(b))
        }
        ExprKind::Call { callee, args } if show_expr(e).chars().count() > 40 => {
            let args: Vec<String> = args.iter().map(short).collect();
            format!("{}({})", callee.name, args.join(", "))
        }
        _ => show_expr(e),
    }
}

/// A component in an abbreviated expression: shown if it is short, `…` if not.
fn short(e: &Expr) -> String {
    let text = show(e, false);
    if text.chars().count() <= 16 {
        text
    } else {
        "…".to_string()
    }
}

fn show(e: &Expr, top: bool) -> String {
    let text = match &e.kind {
        ExprKind::Var(x) => x.clone(),
        ExprKind::Unit => "()".to_string(),
        ExprKind::Int(n) => n.to_string(),
        ExprKind::Tuple(a, b) => format!("({}, {})", show(a, false), show(b, false)),
        ExprKind::Let {
            pat,
            ty,
            value,
            body,
        } => {
            let value = show(value, false);
            let body = show(body, true);
            let ann = ty.as_ref().map(|t| format!(": {t}")).unwrap_or_default();
            match pat {
                Pat::Var(x) => format!("let {}{ann} = {value}; {body}", x.name),
                Pat::Pair(x, y) => {
                    format!("let ({}, {}){ann} = {value}; {body}", x.name, y.name)
                }
                Pat::Wild => format!("{value}; {body}"),
            }
        }
        ExprKind::Closure {
            param, ty, body, ..
        } => format!("|{}: {ty}| {}", param.name, show(body, false)),
        ExprKind::Call { callee, args } => {
            let args: Vec<String> = args.iter().map(|a| show(a, false)).collect();
            format!("{}({})", callee.name, args.join(", "))
        }
        ExprKind::With(a, b) => format!("with({}, {})", show(a, false), show(b, false)),
        ExprKind::Left(a) => format!("Left({})", show(a, false)),
        ExprKind::Right(a) => format!("Right({})", show(a, false)),
        ExprKind::Match {
            scrutinee,
            left,
            right,
        } => format!(
            "match {} {{ Left({}) => {}, Right({}) => {} }}",
            show(scrutinee, false),
            left.0.name,
            show(&left.1, false),
            right.0.name,
            show(&right.1, false)
        ),
        ExprKind::Field(base, proj, _) => format!("{}{proj}", show(base, false)),
        ExprKind::Clone(base) => format!("{}.clone()", show(base, false)),
        ExprKind::StructLit { name, fields } => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(f, v)| format!("{}: {}", f.name, show(v, false)))
                .collect();
            format!("{} {{ {} }}", name.name, fields.join(", "))
        }
    };
    let is_sequence = matches!(e.kind, ExprKind::Let { .. });
    if is_sequence && !top {
        format!("{{ {text} }}")
    } else {
        text
    }
}
