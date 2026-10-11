import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Data.Nat.Basic

/-!
# Chapter 16 · Categories in Mathlib

Mathlib's `CategoryTheory.Category`, its notation (`⟶`, `≫` in diagrammatic
order, `𝟙`), the category `Type u` (whose morphisms wrap functions), preorders
as categories, monomorphisms and epimorphisms in `Type`, and binary products
through the `Limits` library.

This file does not import `Book.Ch16.Category`: Mathlib's `⟶` is global
notation, and inside `namespace Ch16` it would clash with the book's own `⟶`.
-/

namespace Ch16.InMathlib

open CategoryTheory

-- ANCHOR: mathlib_generic
/-- A statement about every Mathlib category. `f ≫ g` is "first `f`, then `g`":
the diagrammatic order, the reverse of `g ∘ f`. -/
example {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    𝟙 X ≫ (f ≫ g) ≫ 𝟙 Z = f ≫ g := by
  rw [Category.id_comp, Category.comp_id]

/-- The same goal, closed by `simp`: the unit and associativity laws are
`simp` lemmas in Mathlib. -/
example {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (𝟙 W ≫ f) ≫ (g ≫ h) = f ≫ g ≫ h := by
  simp
-- ANCHOR_END: mathlib_generic

-- ANCHOR: mathlib_types
/-- In Mathlib, a morphism of `Type` is not literally a function: it is a
one-field structure wrapping one. `↾f` turns a function into a morphism. -/
def lenM : String ⟶ ℕ := ↾String.length
def doubleM : ℕ ⟶ ℕ := ↾(fun n => 2 * n)

/-- A morphism can still be applied to an argument, through a coercion. -/
example : (lenM ≫ doubleM) "hello" = 10 := rfl

/-- info: 10 -/
#guard_msgs in
#eval (lenM ≫ doubleM) "hello"

/-- Applying a composite applies the two functions in diagrammatic order. -/
example {X Y Z : Type} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by
  simp
-- ANCHOR_END: mathlib_types

-- ANCHOR: mathlib_preorder
/-- Every preorder is a category in Mathlib too; `homOfLE` and `leOfHom`
convert between proofs of `≤` and morphisms. -/
def threeToFive : (3 : ℕ) ⟶ 5 := homOfLE (by decide)
def fiveToEight : (5 : ℕ) ⟶ 8 := homOfLE (by decide)

example : (3 : ℕ) ≤ 8 := leOfHom (threeToFive ≫ fiveToEight)

/-- Parallel morphisms of a preorder are equal (`Subsingleton.elim`). -/
example (f g : (3 : ℕ) ⟶ 8) : f = g := Subsingleton.elim f g
-- ANCHOR_END: mathlib_preorder

-- ANCHOR: mathlib_mono
/-- Mathlib's versions of the two theorems we proved by hand. -/
example {X Y : Type} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  mono_iff_injective f

example {X Y : Type} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  epi_iff_surjective f
-- ANCHOR_END: mathlib_mono

open Limits

-- ANCHOR: mathlib_products
/-- In any category with binary products, `prod.lift f g : X ⟶ A ⨯ B` is the
morphism of the universal property, and these are its two equations. -/
example {C : Type*} [Category C] [HasBinaryProducts C] {X A B : C}
    (f : X ⟶ A) (g : X ⟶ B) :
    prod.lift f g ≫ prod.fst = f ∧ prod.lift f g ≫ prod.snd = g :=
  ⟨prod.lift_fst f g, prod.lift_snd f g⟩

/-- Uniqueness: a morphism into a product is determined by its projections. -/
example {C : Type*} [Category C] [HasBinaryProducts C] {X A B : C}
    (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ A ⨯ B)
    (h₁ : h ≫ prod.fst = f) (h₂ : h ≫ prod.snd = g) : h = prod.lift f g := by
  apply prod.hom_ext   -- it suffices to compare the two projections
  · simp [h₁]          -- h ≫ fst = f = prod.lift f g ≫ fst
  · simp [h₂]          -- h ≫ snd = g = prod.lift f g ≫ snd

/-- In `Type`, the pair type is a limit (a product) in Mathlib's sense... -/
example (X Y : Type) : IsLimit (Types.binaryProductCone X Y) :=
  Types.binaryProductLimit X Y

/-- ...so the abstract product `X ⨯ Y` is isomorphic to `X × Y`... -/
noncomputable example (X Y : Type) : X ⨯ Y ≅ X × Y :=
  Types.binaryProductIso X Y

/-- ...and `PUnit` is terminal. -/
example : IsTerminal PUnit := Types.isTerminalPUnit
-- ANCHOR_END: mathlib_products

end Ch16.InMathlib
