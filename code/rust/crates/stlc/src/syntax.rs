//! Types and terms of the simply typed λ-calculus, with a printer.

use std::collections::BTreeSet;
use std::fmt;

// ANCHOR: ty
/// Simple types: `τ ::= Unit | Bool | Nat | τ → τ | τ × τ | τ + τ`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Bool,
    Nat,
    /// Functions `σ → τ`.
    Fun(Box<Ty>, Box<Ty>),
    /// Pairs `σ × τ`.
    Prod(Box<Ty>, Box<Ty>),
    /// Tagged unions `σ + τ`: a value is `inl` of a `σ` or `inr` of a `τ`.
    Sum(Box<Ty>, Box<Ty>),
}
// ANCHOR_END: ty

/// The function type `a → b`.
pub fn fun(a: Ty, b: Ty) -> Ty {
    Ty::Fun(Box::new(a), Box::new(b))
}

/// The product type `a × b`.
pub fn prod(a: Ty, b: Ty) -> Ty {
    Ty::Prod(Box::new(a), Box::new(b))
}

/// The sum type `a + b`.
pub fn sum(a: Ty, b: Ty) -> Ty {
    Ty::Sum(Box::new(a), Box::new(b))
}

// ANCHOR: term
/// Terms. `Lam` may carry an annotation on its parameter; `Ann` is a type
/// annotation `(e : τ)` on any term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    /// `λx. e` or `λx: τ. e`
    Lam(String, Option<Ty>, Box<Term>),
    /// `e1 e2`
    App(Box<Term>, Box<Term>),
    /// `(e : τ)`
    Ann(Box<Term>, Ty),
    /// `let x = e1 in e2`
    Let(String, Box<Term>, Box<Term>),
    /// `()`
    Unit,
    /// `true`, `false`
    Bool(bool),
    /// `if c then e1 else e2`
    If(Box<Term>, Box<Term>, Box<Term>),
    /// `0`, `1`, `2`, ...: numerals stand for `succ (succ (... 0))`
    Nat(u64),
    /// `succ e`
    Succ(Box<Term>),
    /// `iter n z s`: apply `s` to `z`, `n` times
    Iter(Box<Term>, Box<Term>, Box<Term>),
    /// `(e1, e2)`
    Pair(Box<Term>, Box<Term>),
    /// `fst e`
    Fst(Box<Term>),
    /// `snd e`
    Snd(Box<Term>),
    /// `inl e`
    Inl(Box<Term>),
    /// `inr e`
    Inr(Box<Term>),
    /// `case e of inl x => e1 | inr y => e2`
    Case(Box<Term>, String, Box<Term>, String, Box<Term>),
}
// ANCHOR_END: term

impl Term {
    /// The free variables of a term. For a `λ`, these are exactly what a
    /// closure has to capture.
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_free(&mut Vec::new(), &mut out);
        out
    }

    fn collect_free(&self, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
        use Term::*;
        let mut under = |x: &str, t: &Term, bound: &mut Vec<String>| {
            bound.push(x.to_string());
            t.collect_free(bound, out);
            bound.pop();
        };
        match self {
            Var(x) => {
                if !bound.iter().any(|y| y == x) {
                    out.insert(x.clone());
                }
            }
            Lam(x, _, body) => under(x, body, bound),
            Let(x, e1, e2) => {
                e1.collect_free(bound, out);
                bound.push(x.clone());
                e2.collect_free(bound, out);
                bound.pop();
            }
            Case(e, x, l, y, r) => {
                e.collect_free(bound, out);
                bound.push(x.clone());
                l.collect_free(bound, out);
                bound.pop();
                bound.push(y.clone());
                r.collect_free(bound, out);
                bound.pop();
            }
            Unit | Bool(_) | Nat(_) => {}
            Ann(e, _) | Succ(e) | Fst(e) | Snd(e) | Inl(e) | Inr(e) => {
                e.collect_free(bound, out)
            }
            App(a, b) | Pair(a, b) => {
                a.collect_free(bound, out);
                b.collect_free(bound, out);
            }
            If(a, b, c) | Iter(a, b, c) => {
                a.collect_free(bound, out);
                b.collect_free(bound, out);
                c.collect_free(bound, out);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

impl Ty {
    /// Precedence levels: 0 = function type, 1 = sum, 2 = product, 3 = atom.
    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        let (level, body): (u8, String) = match self {
            Ty::Unit => (3, "Unit".into()),
            Ty::Bool => (3, "Bool".into()),
            Ty::Nat => (3, "Nat".into()),
            Ty::Fun(a, b) => (0, format!("{} → {}", Paren(a, 1), Paren(b, 0))),
            Ty::Sum(a, b) => (1, format!("{} + {}", Paren(a, 1), Paren(b, 2))),
            Ty::Prod(a, b) => (2, format!("{} × {}", Paren(a, 2), Paren(b, 3))),
        };
        if level < prec {
            write!(f, "({body})")
        } else {
            write!(f, "{body}")
        }
    }
}

/// A type printed at a given precedence.
struct Paren<'a>(&'a Ty, u8);

impl fmt::Display for Paren<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt_prec(f, self.1)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}

/// Term precedence: 0 = anything (λ, let, if, case extend to the right),
/// 1 = an application or a built-in like `succ e`, 2 = an atom.
fn level(t: &Term) -> u8 {
    use Term::*;
    match t {
        Lam(..) | Let(..) | If(..) | Case(..) => 0,
        App(..) | Succ(_) | Iter(..) | Fst(_) | Snd(_) | Inl(_) | Inr(_) => 1,
        Var(_) | Unit | Bool(_) | Nat(_) | Pair(..) | Ann(..) => 2,
    }
}

/// A term printed at a given precedence: parenthesized if its level is lower.
struct At<'a>(&'a Term, u8);

impl fmt::Display for At<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if level(self.0) < self.1 {
            write!(f, "({})", self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            Var(x) => write!(f, "{x}"),
            Lam(x, None, body) => write!(f, "λ{x}. {body}"),
            Lam(x, Some(ty), body) => write!(f, "λ{x}: {ty}. {body}"),
            App(g, a) => write!(f, "{} {}", At(g, 1), At(a, 2)),
            Ann(e, ty) => write!(f, "({e} : {ty})"),
            Let(x, e1, e2) => write!(f, "let {x} = {e1} in {e2}"),
            Unit => write!(f, "()"),
            Bool(b) => write!(f, "{b}"),
            If(c, a, b) => write!(f, "if {c} then {a} else {b}"),
            Nat(n) => write!(f, "{n}"),
            Succ(e) => write!(f, "succ {}", At(e, 2)),
            Iter(n, z, s) => write!(f, "iter {} {} {}", At(n, 2), At(z, 2), At(s, 2)),
            Pair(a, b) => write!(f, "({a}, {b})"),
            Fst(e) => write!(f, "fst {}", At(e, 2)),
            Snd(e) => write!(f, "snd {}", At(e, 2)),
            Inl(e) => write!(f, "inl {}", At(e, 2)),
            Inr(e) => write!(f, "inr {}", At(e, 2)),
            Case(e, x, l, y, r) => {
                write!(f, "case {e} of inl {x} => {} | inr {y} => {r}", At(l, 1))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_printing() {
        let nat_to_nat = fun(Ty::Nat, Ty::Nat);
        assert_eq!(
            fun(nat_to_nat.clone(), nat_to_nat).to_string(),
            "(Nat → Nat) → Nat → Nat"
        );
        assert_eq!(
            prod(Ty::Nat, sum(Ty::Bool, Ty::Unit)).to_string(),
            "Nat × (Bool + Unit)"
        );
        assert_eq!(
            sum(prod(Ty::Nat, Ty::Nat), Ty::Unit).to_string(),
            "Nat × Nat + Unit"
        );
    }

    #[test]
    fn free_variables() {
        let t = Term::Lam(
            "x".into(),
            None,
            Box::new(Term::App(
                Box::new(Term::Var("f".into())),
                Box::new(Term::Var("x".into())),
            )),
        );
        assert_eq!(t.free_vars(), BTreeSet::from(["f".to_string()]));
    }
}
