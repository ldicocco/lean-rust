/-!
# Chapter 28 · Syntax of the borrow calculus

Types, terms, the `Copy` predicate, the free lifetimes of a type and the number
of free occurrences of a variable in a term, for the core calculus of borrowing
of Chapter 28. Variables and lifetimes are named by strings, so that the
derivations in `Derivations.lean` read like the ones in the text.
-/

namespace Ch28

-- ANCHOR: names
/-- Program variables: `r`, `y1`, `v`. -/
abbrev Var := String

/-- Lifetime (region) variables, written without the quote: `"a"` stands for
Rust's `'a`. -/
abbrev Lft := String
-- ANCHOR_END: names

-- ANCHOR: ty
/-- The types of the calculus. -/
inductive Ty where
  /-- Machine integers (Rust's `i32`). -/
  | int
  /-- The unit type `()`. -/
  | unit
  /-- The pair type `τ₁ ⊗ τ₂` (Rust's tuple `(T, U)`). -/
  | pair (τ₁ τ₂ : Ty)
  /-- An owned location in the store holding a `τ` (Rust's `Box<T>`). -/
  | box (τ : Ty)
  /-- A shared reference `&'κ τ`. -/
  | ref (κ : Lft) (τ : Ty)
  /-- A mutable reference `&'κ mut τ`. -/
  | refMut (κ : Lft) (τ : Ty)
  deriving DecidableEq, Repr
-- ANCHOR_END: ty

-- ANCHOR: copy
/-- `Copy τ`: values of type `τ` may be duplicated. The least predicate closed
under these four rules; in particular `box` and `refMut` are never `Copy`. -/
inductive Copy : Ty → Prop where
  | int : Copy .int
  | unit : Copy .unit
  | ref {κ τ} : Copy (.ref κ τ)
  | pair {τ₁ τ₂} : Copy τ₁ → Copy τ₂ → Copy (.pair τ₁ τ₂)
-- ANCHOR_END: copy

-- ANCHOR: not_copy
/-- An owner is not `Copy`: no rule concludes `Copy (.box τ)`, so a proof of it
cannot exist, and `nomatch` checks exactly that. -/
theorem not_copy_box (τ : Ty) : ¬ Copy (.box τ) := fun h => nomatch h

/-- A mutable reference is not `Copy` either. -/
theorem not_copy_refMut (κ : Lft) (τ : Ty) : ¬ Copy (.refMut κ τ) :=
  fun h => nomatch h
-- ANCHOR_END: not_copy

-- ANCHOR: lfts
/-- `flv(τ)`: the lifetimes mentioned in a type. The escape check asks that a
fresh lifetime is not in this list. -/
def Ty.lfts : Ty → List Lft
  | .int | .unit => []
  | .pair τ₁ τ₂ => τ₁.lfts ++ τ₂.lfts
  | .box τ => τ.lfts
  | .ref κ τ | .refMut κ τ => κ :: τ.lfts
-- ANCHOR_END: lfts

-- ANCHOR: term
/-- The terms of the calculus. The three `borrow` forms bind the lifetime `α`
and the reference variable `y` in the body `e₂`. -/
inductive Term where
  | var (x : Var)
  | lit (n : Nat)
  | unit
  /-- `(e₁, e₂)` -/
  | pair (e₁ e₂ : Term)
  /-- `let x = e₁ in e₂` -/
  | letIn (x : Var) (e₁ e₂ : Term)
  /-- `let (x, y) = e₁ in e₂` -/
  | letPair (x y : Var) (e₁ e₂ : Term)
  /-- `new e`: allocate a location holding the value of `e` (`Box::new`). -/
  | new (e : Term)
  /-- `drop e`: consume a value and free what it owns (`std::mem::drop`). -/
  | drop (e : Term)
  /-- `*e`: read through a shared reference. -/
  | deref (e : Term)
  /-- `*e₁ := e₂`: write through a mutable reference. -/
  | assign (e₁ e₂ : Term)
  /-- `borrow y = &'α e₁ in e₂`: a shared borrow of the owner `e₁`. -/
  | borrow (α : Lft) (y : Var) (e₁ e₂ : Term)
  /-- `borrow y = &'α mut e₁ in e₂`: a mutable borrow of the owner `e₁`. -/
  | borrowMut (α : Lft) (y : Var) (e₁ e₂ : Term)
  /-- `borrow y = &'α mut *e₁ in e₂`: a reborrow of the mutable reference `e₁`. -/
  | reborrow (α : Lft) (y : Var) (e₁ e₂ : Term)
  deriving Repr
-- ANCHOR_END: term

-- ANCHOR: occ
/-- The number of free occurrences of `x` in a term. A binder for `x` hides
the occurrences in its scope. -/
def Term.occ (x : Var) : Term → Nat
  | .var y => if x = y then 1 else 0
  | .lit _ | .unit => 0
  | .pair e₁ e₂ | .assign e₁ e₂ => e₁.occ x + e₂.occ x
  | .new e | .drop e | .deref e => e.occ x
  | .letIn y e₁ e₂ | .borrow _ y e₁ e₂ | .borrowMut _ y e₁ e₂
  | .reborrow _ y e₁ e₂ => e₁.occ x + (if x = y then 0 else e₂.occ x)
  | .letPair y z e₁ e₂ => e₁.occ x + (if x = y ∨ x = z then 0 else e₂.occ x)
-- ANCHOR_END: occ

end Ch28
