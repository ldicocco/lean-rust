import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Chapter 20 · Monads in Mathlib

Mathlib's `CategoryTheory.Monad`: an endofunctor with natural transformations
`η` and `μ` and three laws. A lawful Lean monad gives one on `Type`
(`ofTypeMonad`). Every adjunction gives a monad (`Adjunction.toMonad`); the
currying adjunction on `Type` gives the state monad. Conversely, every monad
comes from an adjunction (Eilenberg–Moore and Kleisli).
-/

namespace Ch20.InMathlib

open CategoryTheory MonoidalCategory

-- ANCHOR: mathlib_monad
variable {C : Type*} [Category C] (T : CategoryTheory.Monad C) (X : C)

/-- `T` is an endofunctor: it acts on objects and on morphisms. -/
example : C := T.obj X

/-- The unit `η : 𝟭 C ⟶ T` and the multiplication `μ : T ⋙ T ⟶ T` are natural
transformations (Chapter 18); here are their components at `X`. -/
example : X ⟶ T.obj X := T.η.app X
example : T.obj (T.obj X) ⟶ T.obj X := T.μ.app X

/-- The three laws, in diagrammatic order (`f ≫ g` is "first `f`, then `g`"). -/
example : T.map (T.μ.app X) ≫ T.μ.app X = T.μ.app (T.obj X) ≫ T.μ.app X :=
  T.assoc X
example : T.η.app (T.obj X) ≫ T.μ.app X = 𝟙 (T.obj X) := T.left_unit X
example : T.map (T.η.app X) ≫ T.μ.app X = 𝟙 (T.obj X) := T.right_unit X
-- ANCHOR_END: mathlib_monad

-- ANCHOR: of_type_monad
/-- A lawful Lean monad, seen as a monad on the category `Type`. -/
def optionMonad : CategoryTheory.Monad Type := ofTypeMonad Option

example (α : Type) : optionMonad.obj α = Option α := rfl
-- ANCHOR_END: of_type_monad

-- ANCHOR: adjunction_monad
/-- The currying adjunction of Chapter 19 on `Type`:
`(S ⊗ A ⟶ B) ≃ (A ⟶ (S ⟶ B))`. -/
example (S : Type) : tensorLeft S ⊣ coyoneda.obj (Opposite.op S) :=
  Types.tensorProductAdjunction S

/-- Every adjunction gives a monad: this one gives the state monad. -/
noncomputable def stateMonad (S : Type) : CategoryTheory.Monad Type :=
  (Types.tensorProductAdjunction S).toMonad

/-- On objects: a computation is a morphism from states to (state, result)
pairs. -/
example (S α : Type) : (stateMonad S).obj α = (S ⟶ S ⊗ α) := rfl

/-- The unit pairs the value with the unchanged state: it is `pure`. -/
example (S α : Type) :
    (stateMonad S).η.app α = ↾(fun (a : α) => ↾(fun (s : S) => (s, a))) := rfl

/-- The multiplication runs the outer computation, then the inner one from the
new state: it is `join`. -/
example (S α : Type) :
    (stateMonad S).μ.app α =
      ↾(fun (k : S ⟶ S ⊗ (S ⟶ S ⊗ α)) => ↾(fun (s : S) => (k s).2 (k s).1)) := rfl
-- ANCHOR_END: adjunction_monad

-- ANCHOR: monad_from_adjunction
/-- Conversely, every monad comes from an adjunction: the free-algebra functor
is left adjoint to the forgetful functor of its Eilenberg–Moore category ... -/
example : T.free ⊣ T.forget := T.adj
/-- ... and the monad of that adjunction is `T` again, up to isomorphism. -/
example : T.adj.toMonad ≅ T := Adjunction.adjToMonadIso T
/-- The Kleisli category gives another such adjunction. -/
example : Kleisli.Adjunction.toKleisli T ⊣ Kleisli.Adjunction.fromKleisli T :=
  Kleisli.Adjunction.adj T
-- ANCHOR_END: monad_from_adjunction

end Ch20.InMathlib
