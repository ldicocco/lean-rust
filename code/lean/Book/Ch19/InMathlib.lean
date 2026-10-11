import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Chapter 19 · Cartesian closed categories in Mathlib

Mathlib builds a cartesian closed category from two pieces: a monoidal
structure that is cartesian (`CartesianMonoidalCategory`) and a closed
structure for it (`MonoidalClosed`). `Type` has both.
-/

namespace Ch19.InMathlib

open CategoryTheory MonoidalCategory

-- ANCHOR: type_closed
/-- info: inferInstance : CartesianMonoidalCategory Type -/
#guard_msgs in
#check (inferInstance : CartesianMonoidalCategory Type)

/-- info: inferInstance : MonoidalClosed Type -/
#guard_msgs in
#check (inferInstance : MonoidalClosed Type)

/-- In `Type`, the monoidal product `⊗` is the cartesian product `×`. -/
example (X Y : Type) : (X ⊗ Y) = (X × Y) := rfl
-- ANCHOR_END: type_closed

-- ANCHOR: mathlib_curry
/--
info: @MonoidalClosed.curry : {C : Type u_2} →
  [inst : Category.{u_1, u_2} C] →
    [inst_1 : MonoidalCategory C] → {A X Y : C} → [inst_2 : Closed A] → (A ⊗ Y ⟶ X) → (Y ⟶ A ⟹ X)
-/
#guard_msgs in
#check @MonoidalClosed.curry

/--
info: @MonoidalClosed.uncurry_curry : ∀ {C : Type u_2} [inst : Category.{u_1, u_2} C] [inst_1 : MonoidalCategory C]
  {A X Y : C} [inst_2 : Closed A] (f : A ⊗ X ⟶ Y), MonoidalClosed.uncurry (MonoidalClosed.curry f) = f
-/
#guard_msgs in
#check @MonoidalClosed.uncurry_curry
-- ANCHOR_END: mathlib_curry

end Ch19.InMathlib
