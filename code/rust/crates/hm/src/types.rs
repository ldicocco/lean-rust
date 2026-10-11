//! Types, type variables and type schemes of mini-ML.
//!
//! The grammar of types is
//!
//! ```text
//! τ ::= α | Int | Bool | τ -> τ | τ * τ | List τ        (monotypes)
//! σ ::= forall α1 ... αn. τ                            (type schemes)
//! ```
//!
//! Every type that is not a variable is a *constructor applied to arguments*:
//! `Int` and `Bool` take no arguments, `->` and `*` take two, `List` takes one.
//! Unification only ever needs that uniform view, so the representation below
//! uses it: `Type::Con(TyCon::Fun, vec![a, b])` is the function type `a -> b`.

use std::collections::BTreeMap;
use std::fmt;

// ANCHOR: types
/// A type variable. While inference runs it is an unknown, printed `?0`,
/// `?1`, ...; in a final answer it is printed with a letter, `a`, `b`, ...
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyVar(pub u32);

/// The type constructors of mini-ML. Each has a fixed number of arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TyCon {
    Int,
    Bool,
    /// `a -> b`, the type of functions from `a` to `b`.
    Fun,
    /// `a * b`, the type of pairs.
    Pair,
    /// `List a`, the type of lists of `a`.
    List,
}

/// A monotype: a type variable, or a constructor applied to argument types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(TyVar),
    Con(TyCon, Vec<Type>),
}

/// A type scheme `forall vars. ty`. The variables in `vars` are *bound*: each
/// use of a variable with this scheme may choose them afresh.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scheme {
    pub vars: Vec<TyVar>,
    pub ty: Type,
}
// ANCHOR_END: types

impl TyCon {
    /// The name used when printing a type.
    pub fn name(self) -> &'static str {
        match self {
            TyCon::Int => "Int",
            TyCon::Bool => "Bool",
            TyCon::Fun => "->",
            TyCon::Pair => "*",
            TyCon::List => "List",
        }
    }
}

impl Type {
    pub fn var(v: TyVar) -> Type {
        Type::Var(v)
    }

    pub fn int() -> Type {
        Type::Con(TyCon::Int, vec![])
    }

    pub fn bool() -> Type {
        Type::Con(TyCon::Bool, vec![])
    }

    pub fn fun(arg: Type, result: Type) -> Type {
        Type::Con(TyCon::Fun, vec![arg, result])
    }

    pub fn pair(first: Type, second: Type) -> Type {
        Type::Con(TyCon::Pair, vec![first, second])
    }

    pub fn list(elem: Type) -> Type {
        Type::Con(TyCon::List, vec![elem])
    }

    /// The type variables of `self`, in order of first appearance, without
    /// repetitions. (The order makes printed schemes read naturally.)
    pub fn vars(&self) -> Vec<TyVar> {
        let mut out = Vec::new();
        self.collect_vars(&mut out);
        out
    }

    fn collect_vars(&self, out: &mut Vec<TyVar>) {
        match self {
            Type::Var(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Type::Con(_, args) => args.iter().for_each(|a| a.collect_vars(out)),
        }
    }

    /// Whether the variable `v` occurs in `self`. (The caller is responsible
    /// for applying the current substitution first.)
    pub fn mentions(&self, v: TyVar) -> bool {
        match self {
            Type::Var(w) => *w == v,
            Type::Con(_, args) => args.iter().any(|a| a.mentions(v)),
        }
    }

    /// The number of constructors and variables in the type.
    pub fn size(&self) -> usize {
        match self {
            Type::Var(_) => 1,
            Type::Con(_, args) => 1 + args.iter().map(Type::size).sum::<usize>(),
        }
    }
}

impl Scheme {
    /// A scheme with no bound variables: the type of a `fun` parameter.
    pub fn mono(ty: Type) -> Scheme {
        Scheme { vars: vec![], ty }
    }
}

/// Raw printing, with variables shown as inference variables `?n`. This is
/// what the traces of the algorithm use.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut name = |v: TyVar| format!("?{}", v.0);
        write!(f, "{}", show(self, Prec::Top, &mut name))
    }
}

/// Gives type variables readable names, `a`, `b`, `c`, ..., in the order in
/// which it meets them. One `Namer` is used for all the types of one message,
/// so that the same variable gets the same letter everywhere in it.
#[derive(Default)]
pub struct Namer {
    names: BTreeMap<TyVar, String>,
}

impl Namer {
    pub fn new() -> Namer {
        Namer::default()
    }

    /// The letter of `v`, assigning the next free one the first time.
    pub fn name(&mut self, v: TyVar) -> String {
        let next = self.names.len();
        self.names
            .entry(v)
            .or_insert_with(|| {
                let letter = (b'a' + (next % 26) as u8) as char;
                if next < 26 {
                    letter.to_string()
                } else {
                    format!("{letter}{}", next / 26)
                }
            })
            .clone()
    }

    /// A type, with readable variable names.
    pub fn show(&mut self, ty: &Type) -> String {
        show(ty, Prec::Top, &mut |v| self.name(v))
    }

    /// A scheme, as `forall a b. ...` (or just the type if nothing is bound).
    pub fn show_scheme(&mut self, scheme: &Scheme) -> String {
        if scheme.vars.is_empty() {
            return self.show(&scheme.ty);
        }
        // Name the bound variables in the order they appear in the type.
        let mut bound: Vec<TyVar> = scheme.ty.vars();
        bound.retain(|v| scheme.vars.contains(v));
        let names: Vec<String> = bound.iter().map(|v| self.name(*v)).collect();
        format!("forall {}. {}", names.join(" "), self.show(&scheme.ty))
    }
}

/// How tightly the surrounding context binds, to decide on parentheses:
/// `->` is loosest (and associates to the right), then `*`, then `List`.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum Prec {
    Top,
    FunArg,
    PairComponent,
    ListArg,
}

/// Prints a type, naming each variable with `name`.
pub fn show_with(ty: &Type, name: &mut dyn FnMut(TyVar) -> String) -> String {
    show(ty, Prec::Top, name)
}

fn show(ty: &Type, prec: Prec, name: &mut dyn FnMut(TyVar) -> String) -> String {
    let (text, needs_parens) = match ty {
        Type::Var(v) => (name(*v), false),
        Type::Con(TyCon::Fun, args) => {
            let arg = show(&args[0], Prec::FunArg, name);
            let res = show(&args[1], Prec::Top, name);
            (format!("{arg} -> {res}"), prec > Prec::Top)
        }
        Type::Con(TyCon::Pair, args) => {
            let a = show(&args[0], Prec::PairComponent, name);
            let b = show(&args[1], Prec::PairComponent, name);
            (format!("{a} * {b}"), prec >= Prec::PairComponent)
        }
        Type::Con(TyCon::List, args) => {
            let elem = show(&args[0], Prec::ListArg, name);
            (format!("List {elem}"), prec >= Prec::ListArg)
        }
        Type::Con(con, _) => (con.name().to_string(), false),
    };
    if needs_parens {
        format!("({text})")
    } else {
        text
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: u32) -> Type {
        Type::Var(TyVar(n))
    }

    #[test]
    fn printing_uses_minimal_parentheses() {
        let mut namer = Namer::new();
        let twice = Type::fun(Type::fun(v(7), v(7)), Type::fun(v(7), v(7)));
        assert_eq!(namer.show(&twice), "(a -> a) -> a -> a");
        let t = Type::list(Type::pair(Type::int(), Type::list(Type::bool())));
        assert_eq!(namer.show(&t), "List (Int * List Bool)");
        let nested = Type::pair(Type::pair(v(1), v(2)), Type::fun(v(1), v(2)));
        assert_eq!(namer.show(&nested), "(b * c) * (b -> c)");
    }

    #[test]
    fn raw_printing_shows_inference_variables() {
        assert_eq!(Type::fun(v(0), Type::int()).to_string(), "?0 -> Int");
    }

    #[test]
    fn schemes_name_bound_variables_in_order() {
        let scheme = Scheme {
            vars: vec![TyVar(5), TyVar(3)],
            ty: Type::fun(v(3), v(5)),
        };
        assert_eq!(Namer::new().show_scheme(&scheme), "forall a b. a -> b");
    }

    #[test]
    fn vars_and_size() {
        let t = Type::fun(v(2), Type::pair(v(1), v(2)));
        assert_eq!(t.vars(), vec![TyVar(2), TyVar(1)]);
        assert!(t.mentions(TyVar(1)) && !t.mentions(TyVar(0)));
        assert_eq!(t.size(), 5);
    }
}
