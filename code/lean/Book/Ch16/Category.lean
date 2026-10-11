/-!
# Chapter 16 · The `Category` class

The core definitions of Part IV: categories, the category of Lean types and
functions, isomorphisms and opposite categories. Chapters 17-20 import this
module, so the names and statements below are stable; new material goes into
other files.

Every morphism type lives in `Type`. That is less general than Mathlib's
`CategoryTheory.Category` (which lets morphisms live in any universe) but it is
all this book needs, and it keeps universe annotations out of the way.
-/

namespace Ch16

universe u

-- ANCHOR: category
/-- A category: objects, morphisms between them, an identity morphism on every
object and an associative composition for which the identities are units. -/
class Category (Obj : Type u) where
  /-- The morphisms from `a` to `b`. -/
  Hom : Obj → Obj → Type
  /-- The identity morphism of `a`. -/
  id : (a : Obj) → Hom a a
  /-- Composition in the order of function composition: `comp g f` is
  "first `f`, then `g`". -/
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  /-- The identity is a left unit for composition. -/
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f
  /-- The identity is a right unit for composition. -/
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f
  /-- Composition is associative. -/
  assoc : ∀ {a b c d : Obj} (h : Hom c d) (g : Hom b c) (f : Hom a b),
    comp h (comp g f) = comp (comp h g) f
-- ANCHOR_END: category

-- ANCHOR: notation
/-- `a ⟶ b` is the type of morphisms from `a` to `b`. -/
scoped infixr:10 " ⟶ " => Category.Hom
/-- `g ⊚ f` is the composite "`f`, then `g`". -/
scoped infixr:80 " ⊚ " => Category.comp
-- ANCHOR_END: notation

open Category

-- ANCHOR: type_category
/-- The category whose objects are Lean types and whose morphisms are functions. -/
instance typeCategory : Category Type where
  Hom α β := α → β
  id _ := fun x => x
  comp g f := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
-- ANCHOR_END: type_category

-- ANCHOR: iso
/-- An isomorphism between `a` and `b`: morphisms in both directions whose
composites are the identities. -/
structure Iso {Obj : Type u} [Category Obj] (a b : Obj) where
  hom : a ⟶ b
  inv : b ⟶ a
  inv_hom : inv ⊚ hom = Category.id a
  hom_inv : hom ⊚ inv = Category.id b
-- ANCHOR_END: iso

/-- `a ≅ b` is the type of isomorphisms between `a` and `b`. -/
scoped infix:10 " ≅ " => Iso

-- ANCHOR: iso_refl
/-- Every object is isomorphic to itself. -/
def Iso.refl {Obj : Type u} [Category Obj] (a : Obj) : a ≅ a where
  hom := Category.id a
  inv := Category.id a
  inv_hom := Category.id_comp _
  hom_inv := Category.id_comp _

/-- Isomorphisms can be reversed. -/
def Iso.symm {Obj : Type u} [Category Obj] {a b : Obj} (i : a ≅ b) : b ≅ a where
  hom := i.inv
  inv := i.hom
  inv_hom := i.hom_inv
  hom_inv := i.inv_hom
-- ANCHOR_END: iso_refl

-- ANCHOR: iso_trans
/-- Isomorphisms compose. -/
def Iso.trans {Obj : Type u} [Category Obj] {a b c : Obj} (i : a ≅ b) (j : b ≅ c) :
    a ≅ c where
  hom := j.hom ⊚ i.hom
  inv := i.inv ⊚ j.inv
  inv_hom := by
    rw [Category.assoc, ← Category.assoc i.inv, j.inv_hom, Category.comp_id, i.inv_hom]
  hom_inv := by
    rw [Category.assoc, ← Category.assoc j.hom, i.hom_inv, Category.comp_id, j.hom_inv]
-- ANCHOR_END: iso_trans

-- ANCHOR: opposite
/-- The opposite of a category has the same objects and every arrow reversed.
`Op C` is a copy of `C`, so that the two category structures do not clash. -/
structure Op (Obj : Type u) where
  /-- The object of the original category. -/
  unop : Obj

instance opCategory {Obj : Type u} [Category Obj] : Category (Op Obj) where
  Hom a b := b.unop ⟶ a.unop
  id a := Category.id a.unop
  comp g f := f ⊚ g
  id_comp f := Category.comp_id f
  comp_id f := Category.id_comp f
  assoc h g f := (Category.assoc f g h).symm
-- ANCHOR_END: opposite

end Ch16
