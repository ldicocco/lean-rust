import Book.Ch16.Category
import Mathlib.CategoryTheory.Category.Basic

/-!
# Chapter 16 · From the book's categories to Mathlib's

Every instance of the book's `Ch16.Category` class gives a Mathlib
`CategoryTheory.Category`: the data is the same, composition is written in the
other order, and so the two unit laws trade places.

The file avoids the arrow `⟶`: Mathlib's version is global notation and would
be ambiguous with the book's inside `namespace Ch16`.
-/

namespace Ch16

universe u

-- ANCHOR: bridge
/-- The book's category class, translated into Mathlib's. Mathlib's `f ≫ g`
("first `f`, then `g`") is the book's `g ⊚ f`. -/
abbrev toMathlib (C : Type u) [Category C] : CategoryTheory.Category.{0} C where
  Hom a b := Category.Hom a b
  id a := Category.id a
  comp f g := Category.comp g f
  -- Mathlib's `𝟙 a ≫ f = f` is the book's `f ⊚ id a = f`: our `comp_id`.
  id_comp f := Category.comp_id f
  -- Mathlib's `f ≫ 𝟙 b = f` is the book's `id b ⊚ f = f`: our `id_comp`.
  comp_id f := Category.id_comp f
  -- Mathlib's `(f ≫ g) ≫ h = f ≫ (g ≫ h)` is the book's
  -- `h ⊚ (g ⊚ f) = (h ⊚ g) ⊚ f`: our `assoc`, unchanged.
  assoc f g h := Category.assoc h g f
-- ANCHOR_END: bridge

-- ANCHOR: bridge_use
/-- Mathlib's composition in the translated category is the book's composition
with the arguments swapped, by definition. -/
example (C : Type u) [Category C] {a b c : C}
    (f : Category.Hom a b) (g : Category.Hom b c) :
    (toMathlib C).comp f g = Category.comp g f :=
  rfl
-- ANCHOR_END: bridge_use

end Ch16
