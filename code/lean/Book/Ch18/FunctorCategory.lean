import Book.Ch16.Category
import Mathlib.Data.Nat.Notation

/-!
# Chapter 18 · Natural transformations between any two functors

Built on the book's `Category` class of Chapter 16. Functors between categories
(Chapter 17's definition, redefined here), natural transformations with their
naturality squares, vertical composition, and the functor category: functors
`C ⥤ D` and the natural transformations between them form a category. A small
example in a preorder, where a natural transformation is exactly a pointwise
inequality.
-/

namespace Ch18.General

open Ch16

-- ANCHOR: cat_functor
/-- A functor between two categories: a map on objects and a map on morphisms
that preserves identities and composition. -/
structure CatFunctor (C D : Type) [Category C] [Category D] where
  obj : C → D
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id : ∀ a : C, map (Category.id a) = Category.id (obj a)
  map_comp : ∀ {a b c : C} (g : b ⟶ c) (f : a ⟶ b), map (g ⊚ f) = map g ⊚ map f
-- ANCHOR_END: cat_functor

variable {C D : Type} [Category C] [Category D]

-- ANCHOR: cat_nat_trans
/-- A natural transformation `F ⇒ G`: a morphism `F a ⟶ G a` in `D` for every
object `a` of `C`, such that every naturality square commutes. -/
structure CatNatTrans (F G : CatFunctor C D) where
  app : (a : C) → (F.obj a ⟶ G.obj a)
  naturality : ∀ {a b : C} (f : a ⟶ b), app b ⊚ F.map f = G.map f ⊚ app a
-- ANCHOR_END: cat_nat_trans

-- ANCHOR: cat_vcomp
namespace CatNatTrans

/-- The identity natural transformation. -/
def id (F : CatFunctor C D) : CatNatTrans F F where
  app a := Category.id (F.obj a)
  naturality f := by
    -- id ⊚ F.map f = F.map f ⊚ id
    rw [Category.id_comp, Category.comp_id]

/-- Vertical composition: first `η : F ⇒ G`, then `θ : G ⇒ H`. -/
def vcomp {F G H : CatFunctor C D} (θ : CatNatTrans G H) (η : CatNatTrans F G) :
    CatNatTrans F H where
  app a := θ.app a ⊚ η.app a
  naturality f := by
    -- Goal: (θ_b ⊚ η_b) ⊚ F f = H f ⊚ (θ_a ⊚ η_a)
    rw [← Category.assoc, η.naturality, Category.assoc, θ.naturality,
      ← Category.assoc]
-- ANCHOR_END: cat_vcomp

-- ANCHOR: cat_ext
/-- Natural transformations with the same components are equal. -/
theorem ext {F G : CatFunctor C D} {η θ : CatNatTrans F G}
    (h : ∀ a, η.app a = θ.app a) : η = θ := by
  cases η with
  | mk app₁ _ =>
    cases θ with
    | mk app₂ _ =>
      have : app₁ = app₂ := funext h
      subst this
      rfl
-- ANCHOR_END: cat_ext

end CatNatTrans

-- ANCHOR: functor_category
/-- The functor category: objects are functors `C ⥤ D`, morphisms are natural
transformations, composition is vertical composition. The laws are inherited,
component by component, from the laws of `D`. -/
instance functorCategory : Category (CatFunctor C D) where
  Hom F G := CatNatTrans F G
  id F := CatNatTrans.id F
  comp θ η := CatNatTrans.vcomp θ η
  id_comp _ := CatNatTrans.ext fun _ => Category.id_comp _
  comp_id _ := CatNatTrans.ext fun _ => Category.comp_id _
  assoc _ _ _ := CatNatTrans.ext fun _ => Category.assoc _ _ _
-- ANCHOR_END: functor_category

/-! ## A preorder example -/

-- ANCHOR: le_category
/-- The natural numbers ordered by `≤`, as a category: there is one morphism
`a ⟶ b` exactly when `a ≤ b` (`PLift` turns the proof into data). The instance
is local to this file. -/
local instance leCategory : Category ℕ where
  Hom a b := PLift (a ≤ b)
  id a := ⟨Nat.le_refl a⟩
  comp g f := ⟨Nat.le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A monotone function is a functor on `(ℕ, ≤)`. The functor laws hold by
`rfl`: any two proofs of the same inequality are equal. -/
def monotone (f : ℕ → ℕ) (mono : ∀ {a b : ℕ}, a ≤ b → f a ≤ f b) :
    CatFunctor ℕ ℕ where
  obj := f
  map h := ⟨mono h.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl
-- ANCHOR_END: le_category

-- ANCHOR: le_nat_trans
/-- Between monotone maps, a natural transformation is exactly a pointwise
inequality: naturality squares commute automatically in a preorder. -/
theorem natTrans_iff_le (F G : CatFunctor ℕ ℕ) :
    Nonempty (CatNatTrans F G) ↔ ∀ n, F.obj n ≤ G.obj n := by
  constructor
  · -- A natural transformation gives a morphism `F n ⟶ G n`, a proof of `≤`.
    rintro ⟨η⟩ n
    exact (η.app n).down
  · -- Conversely, the inequalities are the components, and every naturality
    -- square commutes because both paths are proofs of the same `≤`.
    intro h
    exact ⟨{ app := fun n => ⟨h n⟩, naturality := fun _ => rfl }⟩

def double : CatFunctor ℕ ℕ := monotone (fun n => 2 * n) (by omega)
def succ : CatFunctor ℕ ℕ := monotone (fun n => n + 1) (by omega)

/-- There is a natural transformation from the identity to `double`... -/
example : Nonempty (CatNatTrans (monotone id fun h => h) double) :=
  (natTrans_iff_le _ _).mpr fun n => show n ≤ 2 * n by omega

/-- ...but none from `succ` to `double`: the component at `0` would be a proof
of `1 ≤ 0`. -/
example : ¬ Nonempty (CatNatTrans succ double) := by
  rw [natTrans_iff_le]
  intro h
  have : 0 + 1 ≤ 2 * 0 := h 0
  omega
-- ANCHOR_END: le_nat_trans

end Ch18.General
