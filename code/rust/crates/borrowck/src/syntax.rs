//! Types and terms of the borrow calculus, and how to print them.

use std::fmt;

/// A lifetime variable, stored without its quote: `"a"` stands for `'a`.
pub type Lifetime = String;

// ANCHOR: ty
/// The types of the calculus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// Integers (Rust's `i32`).
    Int,
    /// The unit type `()`.
    Unit,
    /// The pair type `τ₁ ⊗ τ₂` (Rust's tuple `(T, U)`).
    Pair(Box<Ty>, Box<Ty>),
    /// An owned location holding a `τ` (Rust's `Box<T>`).
    Box(Box<Ty>),
    /// A shared reference `&'κ τ`.
    Ref(Lifetime, Box<Ty>),
    /// A mutable reference `&'κ mut τ`.
    RefMut(Lifetime, Box<Ty>),
}
// ANCHOR_END: ty

impl Ty {
    // ANCHOR: is_copy
    /// The `Copy` predicate: integers, unit, shared references, and pairs of
    /// `Copy` types. Owners and mutable references are never `Copy`.
    pub fn is_copy(&self) -> bool {
        match self {
            Ty::Int | Ty::Unit | Ty::Ref(..) => true,
            Ty::Pair(a, b) => a.is_copy() && b.is_copy(),
            Ty::Box(_) | Ty::RefMut(..) => false,
        }
    }
    // ANCHOR_END: is_copy

    // ANCHOR: mentions
    /// Is the lifetime `lt` among the free lifetimes `flv(τ)` of this type?
    pub fn mentions(&self, lt: &str) -> bool {
        match self {
            Ty::Int | Ty::Unit => false,
            Ty::Pair(a, b) => a.mentions(lt) || b.mentions(lt),
            Ty::Box(t) => t.mentions(lt),
            Ty::Ref(k, t) | Ty::RefMut(k, t) => k == lt || t.mentions(lt),
        }
    }
    // ANCHOR_END: mentions

    /// The free lifetimes of this type, in order of appearance.
    pub fn lifetimes(&self) -> Vec<Lifetime> {
        let mut out = Vec::new();
        self.collect_lifetimes(&mut out);
        out
    }

    fn collect_lifetimes(&self, out: &mut Vec<Lifetime>) {
        match self {
            Ty::Int | Ty::Unit => {}
            Ty::Pair(a, b) => {
                a.collect_lifetimes(out);
                b.collect_lifetimes(out);
            }
            Ty::Box(t) => t.collect_lifetimes(out),
            Ty::Ref(k, t) | Ty::RefMut(k, t) => {
                if !out.contains(k) {
                    out.push(k.clone());
                }
                t.collect_lifetimes(out);
            }
        }
    }

    /// Shorthand constructors, used by the parser and the tests.
    pub fn pair(a: Ty, b: Ty) -> Ty {
        Ty::Pair(Box::new(a), Box::new(b))
    }
    pub fn boxed(t: Ty) -> Ty {
        Ty::Box(Box::new(t))
    }
    pub fn shared(k: &str, t: Ty) -> Ty {
        Ty::Ref(k.to_string(), Box::new(t))
    }
    pub fn mutable(k: &str, t: Ty) -> Ty {
        Ty::RefMut(k.to_string(), Box::new(t))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Operands of `⊗` and of the prefix constructors are parenthesized when
        // they are pairs themselves.
        fn operand(t: &Ty, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match t {
                Ty::Pair(..) => write!(f, "({t})"),
                _ => write!(f, "{t}"),
            }
        }
        match self {
            Ty::Int => write!(f, "Int"),
            Ty::Unit => write!(f, "Unit"),
            Ty::Pair(a, b) => {
                operand(a, f)?;
                write!(f, " ⊗ ")?;
                operand(b, f)
            }
            Ty::Box(t) => {
                write!(f, "Box ")?;
                operand(t, f)
            }
            Ty::Ref(k, t) => {
                write!(f, "&'{k} ")?;
                operand(t, f)
            }
            Ty::RefMut(k, t) => {
                write!(f, "&'{k} mut ")?;
                operand(t, f)
            }
        }
    }
}

// ANCHOR: term
/// The three ways to create a reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BorrowKind {
    /// `borrow y = &'a e₁ in e₂`
    Shared,
    /// `borrow y = &'a mut e₁ in e₂`
    Mut,
    /// `borrow y = &'a mut *e₁ in e₂`
    Reborrow,
}

/// The terms of the calculus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Lit(i64),
    Unit,
    /// `(e₁, e₂)`
    Pair(Box<Term>, Box<Term>),
    /// `let x = e₁ in e₂`
    Let(String, Box<Term>, Box<Term>),
    /// `let (x, y) = e₁ in e₂`
    LetPair(String, String, Box<Term>, Box<Term>),
    /// `new e`: allocate a location (`Box::new`).
    New(Box<Term>),
    /// `drop e`: consume a value, freeing what it owns (`std::mem::drop`).
    Drop(Box<Term>),
    /// `*e`: read through a shared reference.
    Deref(Box<Term>),
    /// `*e₁ := e₂`: write through a mutable reference.
    Assign(Box<Term>, Box<Term>),
    /// The three borrow forms. They bind `lifetime` and `var` in `body`.
    Borrow {
        kind: BorrowKind,
        lifetime: Lifetime,
        var: String,
        owner: Box<Term>,
        body: Box<Term>,
    },
    /// Run-time only: a pointer to store location `ℓ`.
    Ptr(Ptr, usize),
    /// Run-time only: `restore w after e`, the frame of a borrow in progress.
    Restore(Box<Term>, Box<Term>),
}

/// The three kinds of pointer values that exist at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ptr {
    /// `own ℓ`, the value of an owner of type `Box τ`.
    Own,
    /// `shr ℓ`, the value of a shared reference.
    Shr,
    /// `uniq ℓ`, the value of a mutable reference.
    Uniq,
}
// ANCHOR_END: term

impl Term {
    /// Does the variable `x` occur free in this term?
    pub fn occurs(&self, x: &str) -> bool {
        match self {
            Term::Var(y) => x == y,
            Term::Lit(_) | Term::Unit | Term::Ptr(..) => false,
            Term::Pair(a, b) | Term::Assign(a, b) | Term::Restore(a, b) => {
                a.occurs(x) || b.occurs(x)
            }
            Term::New(e) | Term::Drop(e) | Term::Deref(e) => e.occurs(x),
            Term::Let(y, e1, e2) => e1.occurs(x) || (y != x && e2.occurs(x)),
            Term::LetPair(y, z, e1, e2) => {
                e1.occurs(x) || (y != x && z != x && e2.occurs(x))
            }
            Term::Borrow {
                var, owner, body, ..
            } => owner.occurs(x) || (var != x && body.occurs(x)),
        }
    }

    /// Is this term a value? Values are what evaluation produces.
    pub fn is_value(&self) -> bool {
        match self {
            Term::Lit(_) | Term::Unit | Term::Ptr(..) => true,
            Term::Pair(a, b) => a.is_value() && b.is_value(),
            _ => false,
        }
    }

    /// Variables, literals and pointers: terms that never need parentheses.
    fn is_atom(&self) -> bool {
        matches!(
            self,
            Term::Var(_) | Term::Lit(_) | Term::Unit | Term::Ptr(..) | Term::Pair(..)
        )
    }

    /// Atoms and prefix forms (`*e`, `new e`, `drop e`).
    fn is_unary(&self) -> bool {
        self.is_atom() || matches!(self, Term::Deref(_) | Term::New(_) | Term::Drop(_))
    }

    /// A one-line summary for derivation trees: the whole term if it is short,
    /// otherwise its outermost construct with every subterm that is not a
    /// variable or a constant written `…`.
    pub fn summary(&self) -> String {
        let full = self.to_string();
        if full.chars().count() <= 30 {
            return full;
        }
        let mut out = String::new();
        // Writing to a String cannot fail.
        let _ = self.write(&mut out, &|t: &Term| {
            if t.is_atom() && !matches!(t, Term::Pair(..)) {
                t.to_string()
            } else {
                "…".to_string()
            }
        });
        out
    }

    /// Print this term, using `sub` to print its immediate subterms.
    fn write(&self, out: &mut String, sub: &dyn Fn(&Term) -> String) -> fmt::Result {
        use std::fmt::Write;
        // Subterms in operand position get parentheses unless they are unary.
        let operand = |t: &Term| {
            let s = sub(t);
            if t.is_unary() || s == "…" {
                s
            } else {
                format!("({s})")
            }
        };
        match self {
            Term::Var(x) => write!(out, "{x}"),
            Term::Lit(n) => write!(out, "{n}"),
            Term::Unit => write!(out, "()"),
            Term::Pair(a, b) => write!(out, "({}, {})", sub(a), sub(b)),
            Term::Let(x, e1, e2) => {
                write!(out, "let {x} = {} in {}", operand(e1), sub(e2))
            }
            Term::LetPair(x, y, e1, e2) => {
                write!(out, "let ({x}, {y}) = {} in {}", operand(e1), sub(e2))
            }
            Term::New(e) => write!(out, "new {}", operand(e)),
            Term::Drop(e) => write!(out, "drop {}", operand(e)),
            Term::Deref(e) => write!(out, "*{}", operand(e)),
            Term::Assign(e1, e2) => write!(out, "*{} := {}", operand(e1), sub(e2)),
            Term::Borrow {
                kind,
                lifetime,
                var,
                owner,
                body,
            } => {
                let amp = match kind {
                    BorrowKind::Shared => format!("&'{lifetime} "),
                    BorrowKind::Mut => format!("&'{lifetime} mut "),
                    BorrowKind::Reborrow => format!("&'{lifetime} mut *"),
                };
                write!(
                    out,
                    "borrow {var} = {amp}{} in {}",
                    operand(owner),
                    sub(body)
                )
            }
            Term::Ptr(p, l) => {
                let kind = match p {
                    Ptr::Own => "own",
                    Ptr::Shr => "shr",
                    Ptr::Uniq => "uniq",
                };
                write!(out, "{kind} ℓ{l}")
            }
            Term::Restore(w, e) => {
                write!(out, "restore {} after {}", operand(w), sub(e))
            }
        }
    }

    // Shorthand constructors, used by the parser, the tests and the examples.
    pub fn var(x: &str) -> Term {
        Term::Var(x.to_string())
    }
    pub fn pair(a: Term, b: Term) -> Term {
        Term::Pair(Box::new(a), Box::new(b))
    }
    pub fn let_in(x: &str, e1: Term, e2: Term) -> Term {
        Term::Let(x.to_string(), Box::new(e1), Box::new(e2))
    }
    pub fn let_pair(x: &str, y: &str, e1: Term, e2: Term) -> Term {
        Term::LetPair(x.to_string(), y.to_string(), Box::new(e1), Box::new(e2))
    }
    pub fn deref(e: Term) -> Term {
        Term::Deref(Box::new(e))
    }
    pub fn assign(e1: Term, e2: Term) -> Term {
        Term::Assign(Box::new(e1), Box::new(e2))
    }
    pub fn borrow(
        kind: BorrowKind,
        lt: &str,
        y: &str,
        owner: Term,
        body: Term,
    ) -> Term {
        Term::Borrow {
            kind,
            lifetime: lt.to_string(),
            var: y.to_string(),
            owner: Box::new(owner),
            body: Box::new(body),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        self.write(&mut out, &|t: &Term| t.to_string())?;
        f.write_str(&out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copy_predicate() {
        assert!(Ty::Int.is_copy());
        assert!(Ty::shared("a", Ty::boxed(Ty::Int)).is_copy());
        assert!(Ty::pair(Ty::Int, Ty::shared("a", Ty::Int)).is_copy());
        assert!(!Ty::boxed(Ty::Int).is_copy());
        assert!(!Ty::mutable("a", Ty::Int).is_copy());
        assert!(!Ty::pair(Ty::Int, Ty::mutable("a", Ty::Int)).is_copy());
    }

    #[test]
    fn free_lifetimes() {
        let t = Ty::pair(
            Ty::shared("a", Ty::Int),
            Ty::mutable("b", Ty::shared("a", Ty::Int)),
        );
        assert!(t.mentions("a") && t.mentions("b") && !t.mentions("c"));
        assert_eq!(t.lifetimes(), vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn printing() {
        let t = Ty::pair(Ty::boxed(Ty::Int), Ty::pair(Ty::Int, Ty::Unit));
        assert_eq!(t.to_string(), "Box Int ⊗ (Int ⊗ Unit)");
        let e = Term::borrow(
            BorrowKind::Reborrow,
            "b",
            "y",
            Term::var("r"),
            Term::assign(Term::var("y"), Term::Lit(1)),
        );
        assert_eq!(e.to_string(), "borrow y = &'b mut *r in *y := 1");
    }

    #[test]
    fn occurrences_respect_binders() {
        let e = Term::let_in("x", Term::var("x"), Term::var("x"));
        assert!(e.occurs("x"));
        let e = Term::let_in("x", Term::Lit(1), Term::var("x"));
        assert!(!e.occurs("x"));
    }
}
