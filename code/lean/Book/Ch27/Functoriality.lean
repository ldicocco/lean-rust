import Book.Ch16.Category
import Book.Ch27.Variance
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Chapter 27 · Variance as functoriality

Lifetimes ordered by "outlives" form a preorder, and a preorder is a category
with at most one morphism between two objects (Chapter 16). Rust types ordered
by subtyping form another. A covariant type constructor is a functor from the
first to the second; a contravariant one is a functor from the *opposite*
category. We build both with the book's `Category` class from Chapter 16 and a
small functor structure (Chapter 17 has the full story; we redefine what we
need here), then look at Mathlib's version.
-/

namespace Ch27

open Ch16 Ch16.Category

-- ANCHOR: categories
/-- Lifetimes, named by their end points. -/
structure Lifetime where
  endsAt : ℕ

/-- The category of lifetimes: a morphism `a ⟶ b` is a proof that `a`
outlives `b`. There is at most one. -/
instance : Category Lifetime where
  Hom a b := PLift (b.endsAt ≤ a.endsAt)
  id _ := ⟨Nat.le_refl _⟩
  comp g f := ⟨Nat.le_trans g.down f.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Closed Rust-like types. -/
structure RType where
  ty : RTy ℕ

/-- The category of types: a morphism `t ⟶ u` is a proof that `t` is a
subtype of `u`. -/
instance : Category RType where
  Hom t u := PLift (RSub t.ty u.ty)
  id t := ⟨RSub.refl t.ty⟩
  comp g f := ⟨RSub.trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
-- ANCHOR_END: categories

-- ANCHOR: functor
/-- A functor between two categories of the book's `Category` class. -/
structure Fun (C D : Type) [Category C] [Category D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ a, map (Category.id a) = Category.id (obj a)
  map_comp : ∀ {a b c : C} (g : b ⟶ c) (f : a ⟶ b), map (g ⊚ f) = map g ⊚ map f

/-- In these categories any two morphisms with the same ends are equal, so
the functor laws hold automatically: a functor is just a monotone map. -/
def Fun.ofMonotone {C : Type} [Category C] (obj : C → RType)
    (map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)) : Fun C RType where
  obj := obj
  map := map
  map_id _ := rfl
  map_comp _ _ := rfl
-- ANCHOR_END: functor

-- ANCHOR: functors
/-- A covariant type (in its lifetime parameter `'x`) is a functor from
lifetimes to types. -/
def covariantFunctor (t : RTy Lft) (h : t.var = .co) : Fun Lifetime RType :=
  Fun.ofMonotone (fun a => ⟨t.inst a.endsAt⟩)
    (fun f => ⟨RTy.covariant h f.down⟩)

/-- A contravariant type is a functor from the *opposite* category of
lifetimes, where every arrow is reversed. -/
def contravariantFunctor (t : RTy Lft) (h : t.var = .contra) :
    Fun (Op Lifetime) RType :=
  Fun.ofMonotone (fun a => ⟨t.inst a.unop.endsAt⟩)
    (fun f => ⟨RTy.contravariant h f.down⟩)

/-- `&'x i32` is a functor `Lifetime ⥤ RType`... -/
def refFunctor : Fun Lifetime RType := covariantFunctor refX rfl

/-- ...and `fn(&'x i32)` a functor `Lifetimeᵒᵖ ⥤ RType`. -/
def callbackFunctor : Fun (Op Lifetime) RType :=
  contravariantFunctor (.fn refX .i32) rfl
-- ANCHOR_END: functors

-- ANCHOR: mathlib
/-- In Mathlib, every preorder is a category (`a ⟶ b` when `a ≤ b`), and a
monotone function is a functor between such categories. -/
example : CategoryTheory.Functor ℕ ℕ :=
  Monotone.functor (f := fun n : ℕ => 2 * n) (fun _ _ h => Nat.mul_le_mul_left 2 h)
-- ANCHOR_END: mathlib

end Ch27
