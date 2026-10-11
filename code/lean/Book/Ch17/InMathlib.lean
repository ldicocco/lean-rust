import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Nat.Basic

/-!
# Chapter 17 · Functors in Mathlib

Mathlib's `CategoryTheory.Functor` (`C ⥤ D`): a functor on `Type` written by
hand (the laws discharged automatically), `ofTypeFunctor` for core Lean's lawful
functors, composition `⋙` and the identity `𝟭`, and `Monotone.functor` for
preorders.

Like `Book/Ch16/InMathlib.lean`, this file does not import the book's
`Category` class, whose `⟶` would clash with Mathlib's.
-/

namespace Ch17.InMathlib

open CategoryTheory

-- ANCHOR: mathlib_functor
/-- `Option` as a Mathlib functor `Type ⥤ Type`. The fields `map_id` and
`map_comp` are omitted: Mathlib proves them automatically (`cat_disch`). -/
def optionFunctor : Type ⥤ Type where
  obj α := Option α
  map f := ↾(Option.map f)

/-- `F.obj` acts on objects, `F.map` on morphisms. -/
example : optionFunctor.obj ℕ = Option ℕ := rfl

example (f : ℕ → ℕ) : optionFunctor.map (↾f) (some 3) = some (f 3) := rfl

/-- The laws are available as `Functor.map_id` and `Functor.map_comp`, with
composition in diagrammatic order. -/
example {X Y Z : Type} (f : X ⟶ Y) (g : Y ⟶ Z) :
    optionFunctor.map (f ≫ g) = optionFunctor.map f ≫ optionFunctor.map g :=
  optionFunctor.map_comp f g
-- ANCHOR_END: mathlib_functor

-- ANCHOR: mathlib_of_type_functor
/-- Any lawful functor of core Lean gives a Mathlib functor. -/
example : Type ⥤ Type := ofTypeFunctor Option

example : (ofTypeFunctor Option).obj ℕ = Option ℕ := rfl

/-- Functors compose with `⋙` (first the left one), and `𝟭` is the identity. -/
example : (optionFunctor ⋙ ofTypeFunctor Option).obj ℕ = Option (Option ℕ) := rfl

example : (𝟭 Type ⋙ optionFunctor) = optionFunctor := rfl
-- ANCHOR_END: mathlib_of_type_functor

-- ANCHOR: mathlib_monotone
/-- A monotone function between preorders is a functor between them. -/
def doubling : ℕ ⥤ ℕ :=
  Monotone.functor (f := fun n => 2 * n) (fun _ _ h => Nat.mul_le_mul_left 2 h)

example : doubling.obj 5 = 10 := rfl

/-- Its action on morphisms is the monotonicity proof, wrapped by `homOfLE`. -/
example : (6 : ℕ) ≤ 10 := leOfHom (doubling.map (homOfLE (by decide : (3 : ℕ) ≤ 5)))
-- ANCHOR_END: mathlib_monotone

end Ch17.InMathlib
