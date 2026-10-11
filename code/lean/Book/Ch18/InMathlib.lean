import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.Monad

/-!
# Chapter 18 · Natural transformations and Yoneda in Mathlib

Mathlib's `NatTrans` (naturality written in diagrammatic order with `≫`),
`List.head?` as a Mathlib natural transformation between the functors that
Mathlib builds from Lean's lawful `List` and `Option`, and the type of
Mathlib's `yonedaEquiv`.
-/

namespace Ch18.InMathlib

open CategoryTheory

-- ANCHOR: nat_trans_naturality
/--
info: @NatTrans.naturality : ∀ {C : Type u_3} [inst : Category.{u_1, u_3} C] {D : Type u_4} [inst_1 : Category.{u_2, u_4} D]
  {F G : C ⥤ D} (self : NatTrans F G) ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ self.app Y = self.app X ≫ G.map f
-/
#guard_msgs in
#check @NatTrans.naturality
-- ANCHOR_END: nat_trans_naturality

-- ANCHOR: head_nat_trans
/-- `List.head?` as a morphism in Mathlib's functor category `Type ⥤ Type`.
`ofTypeFunctor` turns a lawful Lean functor into a Mathlib functor, and `↾f`
turns a function into a morphism of Mathlib's category of types. -/
def headNT : ofTypeFunctor List ⟶ ofTypeFunctor Option where
  app α := ↾(List.head? : List α → Option α)
  naturality := by
    intro α β f
    ext xs
    cases xs <;> rfl

/-- info: some 3 -/
#guard_msgs in
#eval headNT.app ℕ [3, 1, 2]
-- ANCHOR_END: head_nat_trans

-- ANCHOR: yoneda_equiv
/--
info: @yonedaEquiv : {C : Type u_2} →
  [inst : Category.{u_1, u_2} C] → {X : C} → {F : Cᵒᵖ ⥤ Type u_1} → (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X)
-/
#guard_msgs in
#check @yonedaEquiv

/--
info: @coyonedaEquiv : {C : Type u_2} →
  [inst : Category.{u_1, u_2} C] → {X : C} → {F : C ⥤ Type u_1} → (coyoneda.obj (Opposite.op X) ⟶ F) ≃ F.obj X
-/
#guard_msgs in
#check @coyonedaEquiv
-- ANCHOR_END: yoneda_equiv

end Ch18.InMathlib
