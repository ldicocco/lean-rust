import Mathlib.Data.Nat.Notation

/-!
# Chapter 11 · Positivity

Lean accepts a recursive type only if the type being defined occurs *strictly
positively* in its constructors: never to the left of an arrow. This file shows
the error for a negative occurrence, some recursive types that are accepted,
and the reason for the rule: a negative type would let us write a diagonal
argument that proves `False`.
-/

namespace Ch11

-- ANCHOR: bad
/--
error: (kernel) arg #1 of 'Ch11.Bad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad where
  | mk : (Bad → ℕ) → Bad
-- ANCHOR_END: bad

-- ANCHOR: good
/-- Infinitely branching trees: `Tree` occurs to the right of the arrow, which is
fine. A node holds one subtree for every natural number. -/
inductive Tree where
  | leaf : Tree
  | node : (ℕ → Tree) → Tree

/-- Rose trees: a node holds a list of subtrees. `Rose` occurs inside `List`,
which Lean checks is itself positive in its parameter. -/
inductive Rose where
  | node : String → List Rose → Rose
-- ANCHOR_END: good

-- ANCHOR: hidden_negative
/-- A negative occurrence hidden behind a type constructor is found too. -/
structure Pred (α : Type) where
  test : α → Bool

/--
error: (kernel) arg #1 of '_nested.Ch11.Pred_1.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Sneaky where
  | mk : Pred Sneaky → Sneaky
-- ANCHOR_END: hidden_negative

-- ANCHOR: diagonal_false
/-- Suppose some type `B` had a constructor `mk : (B → False) → B` and, as every
inductive type does, a way `unmk` to take a value apart again. Then we could
prove `False`. -/
theorem no_negative_false (B : Type) (mk : (B → False) → B) (unmk : B → B → False) :
    False :=
  let f : B → False := fun b => unmk b b  -- "b applied to itself"
  f (mk f)                                -- f applied to (a code for) itself
-- ANCHOR_END: diagonal_false

-- ANCHOR: diagonal_nat
/-- The same diagonal argument for `Bad`: if `mk` and `unmk` existed, with the
computation rule `unmk (mk f) = f`, then some number would equal its successor. -/
theorem no_bad (B : Type) (mk : (B → ℕ) → B) (unmk : B → B → ℕ)
    (unmk_mk : ∀ f, unmk (mk f) = f) : False := by
  -- the diagonal function: apply a value to itself, and add one
  let f : B → ℕ := fun b => unmk b b + 1
  have h : f (mk f) = f (mk f) + 1 :=
    calc f (mk f) = unmk (mk f) (mk f) + 1 := rfl
      _ = f (mk f) + 1 := by rw [unmk_mk]
  -- n = n + 1 is impossible for natural numbers
  omega
-- ANCHOR_END: diagonal_nat

end Ch11
