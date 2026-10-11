/-!
# Chapter 9 · Syntax

The simply typed λ-calculus with booleans and natural numbers, in de Bruijn
notation: types, terms, a printer, and the two operations that the metatheory
is built on, *renaming* and *substitution*.
-/

namespace Ch09

-- ANCHOR: ty
/-- The types of the language: booleans, natural numbers and functions. -/
inductive Ty where
  | bool : Ty
  | nat : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq
-- ANCHOR_END: ty

-- ANCHOR: term
/-- Terms in de Bruijn notation: `var i` refers to the binder `i` levels up.
`lam τ t` is `λ (x : τ). t`, with the bound variable written `var 0` in `t`.
`tt` and `ff` are the boolean literals (`true` and `false` are Lean's own). -/
inductive Term where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  | tt : Term
  | ff : Term
  | ite : Term → Term → Term → Term
  | lit : Nat → Term
  | add : Term → Term → Term
  | isZero : Term → Term
  deriving DecidableEq
-- ANCHOR_END: term

/-! ## A printer

The printer shows terms the way the book writes them: `λ:nat. #0 + 1` is the
function `λ (x : nat). x + 1`, with the bound variable printed as its index `#0`.
The Rust crate `safety` prints terms in exactly the same notation. -/

/-- Types, with `→` associating to the right. -/
def Ty.show : Ty → String
  | .bool => "bool"
  | .nat => "nat"
  | .arrow (.arrow a b) c => s!"({Ty.show (.arrow a b)}) → {Ty.show c}"
  | .arrow a b => s!"{Ty.show a} → {Ty.show b}"

/-- Terms, at three precedence levels: 0 (λ and `if`, which extend as far to the
right as possible), 1 (`+`), 2 (application and `iszero`), 3 (atoms). -/
def Term.showPrec : Term → Nat → String
  | .var i, _ => s!"#{i}"
  | .tt, _ => "true"
  | .ff, _ => "false"
  | .lit n, _ => toString n
  | .lam τ t, p => paren (p > 0) s!"λ:{showAnnot τ}. {t.showPrec 0}"
  | .ite c t e, p =>
    paren (p > 0) s!"if {c.showPrec 0} then {t.showPrec 0} else {e.showPrec 0}"
  | .add a b, p => paren (p > 1) s!"{a.showPrec 1} + {b.showPrec 2}"
  | .app f a, p => paren (p > 2) s!"{f.showPrec 2} {a.showPrec 3}"
  | .isZero t, p => paren (p > 2) s!"iszero {t.showPrec 3}"
where
  paren (b : Bool) (s : String) : String := if b then s!"({s})" else s
  showAnnot : Ty → String
    | .arrow a b => s!"({Ty.show (.arrow a b)})"
    | τ => τ.show

/-- `#eval` displays types and terms with the printer (in parentheses when they
appear as the argument of something else, as in `some (nat → nat)`). -/
instance : Repr Ty where
  reprPrec τ p := match τ with
    | .arrow _ _ => if p ≥ max_prec then s!"({τ.show})" else τ.show
    | _ => τ.show

instance : Repr Term where
  reprPrec t p := t.showPrec (if p ≥ max_prec then 3 else 0)

-- ANCHOR: examples
/-- `(λ (x : nat). x + 1) 41` -/
def incr41 : Term := .app (.lam .nat (.add (.var 0) (.lit 1))) (.lit 41)

/-- `λ (f : nat → nat). λ (x : nat). f (f x)`: apply a function twice. The inner
`#1` is `f`, one binder further out than `x`, which is `#0`. -/
def twice : Term :=
  .lam (.arrow .nat .nat) (.lam .nat (.app (.var 1) (.app (.var 1) (.var 0))))

/-- info: (λ:nat. #0 + 1) 41 -/
#guard_msgs in
#eval incr41

/-- info: λ:(nat → nat). λ:nat. #1 (#1 #0) -/
#guard_msgs in
#eval twice
-- ANCHOR_END: examples

/-! ## Renaming -/

-- ANCHOR: rename
/-- Push a renaming under one binder: index 0 is the variable that the binder
introduces, and it stays 0; every other index `i + 1` refers to the variable `i`
of the outer scope, which is renamed by `ρ` and then pushed up by one again. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- Apply a renaming (a function from indices to indices) to every free variable
of a term. Under a λ the renaming is lifted. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .var i => .var (ρ i)
  | .lam τ t => .lam τ (rename (liftRen ρ) t)
  | .app t₁ t₂ => .app (rename ρ t₁) (rename ρ t₂)
  | .tt => .tt
  | .ff => .ff
  | .ite c t e => .ite (rename ρ c) (rename ρ t) (rename ρ e)
  | .lit n => .lit n
  | .add t₁ t₂ => .add (rename ρ t₁) (rename ρ t₂)
  | .isZero t => .isZero (rename ρ t)

/-- Shifting: every free variable moves up by one. This is what a term needs
when it is carried under one more binder. -/
def shift (t : Term) : Term := rename (· + 1) t
-- ANCHOR_END: rename

-- ANCHOR: shift_example
/-- In `λ:nat. #0 + #1`, the `#0` is bound and the `#1` is free (it refers to
the variable just outside the λ, written `#0` out there). Shifting moves only
the free one. -/
example : shift (.lam .nat (.add (.var 0) (.var 1)))
    = .lam .nat (.add (.var 0) (.var 2)) := rfl
-- ANCHOR_END: shift_example

/-! ## Substitution -/

-- ANCHOR: subst
/-- Push a substitution under one binder: index 0 is the new bound variable and
maps to itself; the term `σ i` that replaces outer variable `i` is shifted,
because it now lives under one more binder. -/
def liftSub (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | i + 1 => shift (σ i)

/-- Simultaneous substitution: replace every free variable `var i` by `σ i`. -/
def subst (σ : Nat → Term) : Term → Term
  | .var i => σ i
  | .lam τ t => .lam τ (subst (liftSub σ) t)
  | .app t₁ t₂ => .app (subst σ t₁) (subst σ t₂)
  | .tt => .tt
  | .ff => .ff
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | .lit n => .lit n
  | .add t₁ t₂ => .add (subst σ t₁) (subst σ t₂)
  | .isZero t => .isZero (subst σ t)

/-- The substitution used by β-reduction: variable 0 becomes `s`, and every
other variable moves down by one, because the λ that bound variable 0 is gone. -/
def single (s : Term) : Nat → Term
  | 0 => s
  | i + 1 => .var i

/-- `instantiate body s` is the body of a λ with its bound variable replaced by
`s`; on paper we write it $t[s]$. -/
def instantiate (body s : Term) : Term := subst (single s) body
-- ANCHOR_END: subst

-- ANCHOR: subst_examples
/-- The body of `λ:nat. #0 + 1`, instantiated with `41`. -/
example : instantiate (.add (.var 0) (.lit 1)) (.lit 41)
    = .add (.lit 41) (.lit 1) := rfl

/-- Substituting under a binder. The body is `λ:nat. #1 #0` (inside it, `#1` is
the outer bound variable) and the argument is a free variable `#5`. The result
mentions `#6`: under the inner λ, the argument had to be shifted. -/
example : instantiate (.lam .nat (.app (.var 1) (.var 0))) (.var 5)
    = .lam .nat (.app (.var 6) (.var 0)) := rfl

/-- A free variable of the body that is *not* the one being replaced moves down
by one, because the λ that bound `#0` has disappeared. -/
example : instantiate (.add (.var 0) (.var 3)) (.lit 7)
    = .add (.lit 7) (.var 2) := rfl
-- ANCHOR_END: subst_examples

end Ch09
