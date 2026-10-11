import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Book.Ch11.Iso

/-!
# Chapter 11 · Cardinalities

Counting the values of finite types with Mathlib's `Fintype.card`: the counting
laws for products, sums, functions and `Option`, checked on concrete types; and
the link between isomorphism and equal cardinality.
-/

namespace Ch11

open Ch11.Iso

-- ANCHOR: card_eval
/-- info: 2 -/
#guard_msgs in
#eval Fintype.card Bool

/-- info: 6 -/
#guard_msgs in
#eval Fintype.card (Bool × Option Bool)

/-- info: 9 -/
#guard_msgs in
#eval Fintype.card (Bool → Option Bool)
-- ANCHOR_END: card_eval

-- ANCHOR: card_laws
example (α β : Type) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  Fintype.card_prod α β

example (α β : Type) [Fintype α] [Fintype β] :
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β :=
  Fintype.card_sum

example (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α :=
  Fintype.card_fun

example (α : Type) [Fintype α] : Fintype.card (Option α) = Fintype.card α + 1 :=
  Fintype.card_option
-- ANCHOR_END: card_laws

-- ANCHOR: card_concrete
example : Fintype.card (Bool × Option Bool) = 6 := by simp
example : Fintype.card (Bool ⊕ Unit) = 3 := by simp
example : Fintype.card (Bool → Option Bool) = 9 := by simp
example : Fintype.card (Option Bool → Bool) = 8 := by simp
example : Fintype.card (Empty → Bool) = 1 := by simp  -- the empty function
example : Fintype.card (Bool → Empty) = 0 := by simp  -- no function at all
example : Fintype.card (Empty → Empty) = 1 := by simp -- 0 ^ 0 = 1
-- ANCHOR_END: card_concrete

-- ANCHOR: card_iso
/-- Isomorphic types have the same number of values. -/
theorem card_eq_of_iso {α β : Type} [Fintype α] [Fintype β] (i : α ≅ β) :
    Fintype.card α = Fintype.card β :=
  Fintype.card_congr i.toEquiv

/-- Distributivity of types implies distributivity of numbers. -/
theorem mul_add_from_types (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] :
    Fintype.card α * (Fintype.card β + Fintype.card γ) =
      Fintype.card α * Fintype.card β + Fintype.card α * Fintype.card γ := by
  have h := card_eq_of_iso (distrib α β γ)
  -- h : card (α × (β ⊕ γ)) = card ((α × β) ⊕ (α × γ))
  simpa [Fintype.card_prod, Fintype.card_sum] using h
-- ANCHOR_END: card_iso

-- ANCHOR: card_eq_iff
/-- For finite types the converse holds too: the same number of values means
isomorphic. Mathlib's statement: -/
example (α β : Type) [Fintype α] [Fintype β] :
    Fintype.card α = Fintype.card β ↔ Nonempty (α ≃ β) :=
  Fintype.card_eq

/-- So `Bool × Bool` and `Option (Option Bool)` are isomorphic (both have 4
values), even though nobody wrote the isomorphism down. -/
example : Nonempty (Bool × Bool ≃ Option (Option Bool)) :=
  Fintype.card_eq.mp (by simp)
-- ANCHOR_END: card_eq_iff

end Ch11
