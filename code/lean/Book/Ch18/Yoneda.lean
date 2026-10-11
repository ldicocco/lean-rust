import Book.Ch18.Natural
import Mathlib.Logic.Equiv.Defs

/-!
# Chapter 18 · The Yoneda lemma for functors on types

For a lawful functor `F`, the natural families `(β : Type) → (α → β) → F β`
are in bijection with `F α`. The special case `F = Ident` is continuation-
passing style: a value is the same thing as "a way to hand it to any
continuation".
-/

namespace Ch18

open TypeFunctor

-- ANCHOR: cps
/-- A value of type `α` in continuation-passing style: give me any
continuation `k : α → β` and I will produce a `β`. -/
def Cps (α : Type) : Type 1 := (β : Type) → (α → β) → β

/-- Pass the value to the continuation. -/
def toCps {α : Type} (a : α) : Cps α := fun _ k => k a

/-- Run with the identity continuation to get the value back. -/
def fromCps {α : Type} (c : Cps α) : α := c α id

theorem fromCps_toCps {α : Type} (a : α) : fromCps (toCps a) = a := rfl

/-- info: 42 -/
#guard_msgs in
#eval fromCps (toCps 42)

/-- info: "42!" -/
#guard_msgs in
#eval toCps 42 String (fun n => toString n ++ "!")
-- ANCHOR_END: cps

-- ANCHOR: yoneda_structure
/-- The left-hand side of the Yoneda lemma: a family of functions
`(α → β) → F β`, one for each type `β`, that is natural in `β`. -/
structure Yoneda (F : Type → Type) [TypeFunctor F] (α : Type) : Type 1 where
  run : (β : Type) → (α → β) → F β
  natural : ∀ {β γ : Type} (k : α → β) (g : β → γ),
    run γ (g ∘ k) = map g (run β k)
-- ANCHOR_END: yoneda_structure

variable {F : Type → Type} [TypeFunctor F] {α : Type}

-- ANCHOR: yoneda_maps
/-- From `F α` to the natural family: map the continuation over `x`. The
family is natural because `map` preserves composition. -/
def Yoneda.lift (x : F α) : Yoneda F α where
  run _ k := map k x
  natural k g := map_comp g k x

/-- From the natural family back to `F α`: use the identity continuation. -/
def Yoneda.lower (y : Yoneda F α) : F α := y.run α id
-- ANCHOR_END: yoneda_maps

-- ANCHOR: yoneda_round_trips
/-- Lowering a lifted value gives it back: this is the identity law of `F`. -/
theorem Yoneda.lower_lift (x : F α) : (Yoneda.lift x).lower = x :=
  map_id x

/-- Lifting a lowered family gives it back: this is naturality. Every
component `run β k` is determined by the single value `run α id`. -/
theorem Yoneda.lift_lower (y : Yoneda F α) : Yoneda.lift y.lower = y := by
  cases y with
  | mk run natural =>
    -- Goal: ⟨fun β k => map k (run α id), _⟩ = ⟨run, natural⟩
    have h : (fun β (k : α → β) => map k (run α id)) = run := by
      funext β k
      -- `k ∘ id` is `k` by definition, so naturality at `id` and `k` gives
      -- run β k = map k (run α id).
      exact (natural id k).symm
    simp only [Yoneda.lift, Yoneda.lower, h]
-- ANCHOR_END: yoneda_round_trips

-- ANCHOR: yoneda_equiv
/-- **The Yoneda lemma** (for lawful functors on types). -/
def yonedaEquiv : Yoneda F α ≃ F α where
  toFun := Yoneda.lower
  invFun := Yoneda.lift
  left_inv := Yoneda.lift_lower
  right_inv := Yoneda.lower_lift
-- ANCHOR_END: yoneda_equiv

-- ANCHOR: yoneda_examples
/-- A list, seen as "whatever you map over me". -/
def digits : Yoneda List ℕ := Yoneda.lift [3, 1, 2]

/-- info: ["3", "1", "2"] -/
#guard_msgs in
#eval digits.run String toString

/-- info: [3, 1, 2] -/
#guard_msgs in
#eval yonedaEquiv digits

/-- CPS is the case `F = Ident`: natural CPS values are plain values. -/
def cpsEquiv : Yoneda Ident α ≃ α := yonedaEquiv
-- ANCHOR_END: yoneda_examples

-- ANCHOR: reader
/-- The functor `γ → ·` (often called `Reader γ`): `map` is post-composition. -/
def Reader (γ β : Type) : Type := γ → β

instance (γ : Type) : TypeFunctor (Reader γ) where
  map g r := fun c => g (r c)
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- The Yoneda embedding, for types: natural transformations from `α → ·` to
`γ → ·` are the same as plain functions `γ → α`. -/
def yonedaEmbedding (γ : Type) : Yoneda (Reader γ) α ≃ (γ → α) := yonedaEquiv
-- ANCHOR_END: reader

end Ch18
