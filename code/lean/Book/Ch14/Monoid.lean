/-!
# Chapter 14 · Monoids as a type class

The class `Monoid` (operations only, like the Rust trait), instances for
numbers, strings, lists and pairs, the generic `mconcat`, and the class
`LawfulMonoid`, whose instances must *prove* the monoid laws. Theorems that
hold for every lawful monoid: the left and right folds agree, and `mconcat`
can be computed batch by batch. Subtraction is shown not to be a lawful
monoid. The chapter's walkthrough (statistics of measurements) closes the file.

Our `Monoid` lives in the namespace `Ch14`; it is unrelated to Mathlib's
`Monoid` (see `MathlibMonoid.lean`), which this file does not import.
-/

namespace Ch14

-- ANCHOR: monoid_class
/-- A monoid, operations only: the counterpart of the Rust trait `Monoid`. -/
class Monoid (α : Type) where
  /-- The neutral element. -/
  empty : α
  /-- The operation. -/
  combine : α → α → α

/-- `a ⋄ b` is `Monoid.combine a b`. -/
scoped infixl:70 " ⋄ " => Monoid.combine
-- ANCHOR_END: monoid_class

open Monoid

-- ANCHOR: instances
instance instMonoidNat : Monoid Nat where
  empty := 0
  combine a b := a + b

instance instMonoidString : Monoid String where
  empty := ""
  combine a b := a ++ b

instance instMonoidList {α : Type} : Monoid (List α) where
  empty := []
  combine xs ys := xs ++ ys

/-- An instance with a context: a pair is a monoid if both components are. -/
instance instMonoidProd {α β : Type} [Monoid α] [Monoid β] : Monoid (α × β) where
  empty := (empty, empty)
  combine p q := (p.1 ⋄ q.1, p.2 ⋄ q.2)
-- ANCHOR_END: instances

-- ANCHOR: mconcat
/-- Combine all the elements of a list: `x₁ ⋄ (x₂ ⋄ (... ⋄ empty))`. -/
def mconcat {α : Type} [Monoid α] : List α → α
  | [] => empty
  | x :: xs => x ⋄ mconcat xs
-- ANCHOR_END: mconcat

-- ANCHOR: mconcat_eval
/-- info: 14 -/
#guard_msgs in
#eval mconcat [3, 1, 4, 1, 5]

/-- info: "dictionary-passing" -/
#guard_msgs in
#eval mconcat ["dictionary", "-", "passing"]

/-- info: (14, "abc") -/
#guard_msgs in
#eval mconcat [(3, "a"), (1, "b"), (10, "c")]
-- ANCHOR_END: mconcat_eval

-- ANCHOR: lawful_class
/-- A lawful monoid: the operations, plus proofs of the three laws. Every
instance must supply the proofs; Lean checks them like any other field. -/
class LawfulMonoid (α : Type) extends Monoid α where
  combine_assoc : ∀ a b c : α, (a ⋄ b) ⋄ c = a ⋄ (b ⋄ c)
  empty_combine : ∀ a : α, empty ⋄ a = a
  combine_empty : ∀ a : α, a ⋄ empty = a
-- ANCHOR_END: lawful_class

-- ANCHOR: lawful_print
/--
info: class Ch14.LawfulMonoid (α : Type) : Type
number of parameters: 1
parents:
  Ch14.LawfulMonoid.toMonoid : Monoid α
fields:
  Ch14.Monoid.empty : α
  Ch14.Monoid.combine : α → α → α
  Ch14.LawfulMonoid.combine_assoc : ∀ (a b c : α), a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
  Ch14.LawfulMonoid.empty_combine : ∀ (a : α), empty ⋄ a = a
  Ch14.LawfulMonoid.combine_empty : ∀ (a : α), a ⋄ empty = a
constructor:
  Ch14.LawfulMonoid.mk {α : Type} [toMonoid : Monoid α] (combine_assoc : ∀ (a b c : α), a ⋄ b ⋄ c = a ⋄ (b ⋄ c))
    (empty_combine : ∀ (a : α), empty ⋄ a = a) (combine_empty : ∀ (a : α), a ⋄ empty = a) : LawfulMonoid α
field notation resolution order:
  Ch14.LawfulMonoid, Ch14.Monoid
-/
#guard_msgs in
#print LawfulMonoid
-- ANCHOR_END: lawful_print

-- ANCHOR: lawful_instances
/-- Addition on `Nat`: the three laws are library theorems. -/
instance instLawfulNat : LawfulMonoid Nat where
  toMonoid := instMonoidNat
  combine_assoc := Nat.add_assoc
  empty_combine := Nat.zero_add
  combine_empty := Nat.add_zero

instance instLawfulString : LawfulMonoid String where
  toMonoid := instMonoidString
  combine_assoc _ _ _ := String.append_assoc
  empty_combine _ := String.empty_append
  combine_empty _ := String.append_empty

instance instLawfulList {α : Type} : LawfulMonoid (List α) where
  toMonoid := instMonoidList
  combine_assoc := List.append_assoc
  empty_combine := List.nil_append
  combine_empty := List.append_nil
-- ANCHOR_END: lawful_instances

-- ANCHOR: lawful_prod
/-- Pairs of lawful monoids are lawful: each law holds componentwise. -/
instance instLawfulProd {α β : Type} [LawfulMonoid α] [LawfulMonoid β] :
    LawfulMonoid (α × β) where
  toMonoid := instMonoidProd
  combine_assoc p q r := by
    -- Unfold the pair operation: the goal becomes an equation between pairs.
    show ((p.1 ⋄ q.1) ⋄ r.1, (p.2 ⋄ q.2) ⋄ r.2) = (p.1 ⋄ (q.1 ⋄ r.1), p.2 ⋄ (q.2 ⋄ r.2))
    -- Rewrite each component with the associativity law of its own monoid.
    rw [LawfulMonoid.combine_assoc p.1, LawfulMonoid.combine_assoc p.2]
  empty_combine p := by
    show (empty ⋄ p.1, empty ⋄ p.2) = p
    rw [LawfulMonoid.empty_combine, LawfulMonoid.empty_combine]
  combine_empty p := by
    show (p.1 ⋄ empty, p.2 ⋄ empty) = p
    rw [LawfulMonoid.combine_empty, LawfulMonoid.combine_empty]
-- ANCHOR_END: lawful_prod

section Laws

variable {α : Type} [LawfulMonoid α]

-- ANCHOR: mconcat_append
/-- `mconcat` can be computed in two batches and the results combined.
This is the law that makes splitting work across threads correct. -/
theorem mconcat_append (xs ys : List α) :
    mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys := by
  induction xs with
  | nil =>
    -- Goal: mconcat ([] ++ ys) = mconcat [] ⋄ mconcat ys,
    -- that is, mconcat ys = empty ⋄ mconcat ys.
    show mconcat ys = empty ⋄ mconcat ys
    rw [LawfulMonoid.empty_combine]
  | cons x xs ih =>
    -- ih   : mconcat (xs ++ ys) = mconcat xs ⋄ mconcat ys
    -- Goal : x ⋄ mconcat (xs ++ ys) = (x ⋄ mconcat xs) ⋄ mconcat ys
    show x ⋄ mconcat (xs ++ ys) = (x ⋄ mconcat xs) ⋄ mconcat ys
    rw [ih, LawfulMonoid.combine_assoc]
-- ANCHOR_END: mconcat_append

-- ANCHOR: mconcat_batches
/-- Combining the batch results gives the same value as combining everything
at once: the Lean version of `mconcat_batches` in the Rust example. -/
theorem mconcat_batches (batches : List (List α)) :
    mconcat (batches.map mconcat) = mconcat batches.flatten := by
  induction batches with
  | nil => rfl
  | cons b bs ih =>
    -- Goal: mconcat b ⋄ mconcat (bs.map mconcat) = mconcat (b ++ bs.flatten)
    show mconcat b ⋄ mconcat (bs.map mconcat) = mconcat (b ++ bs.flatten)
    rw [ih, mconcat_append]
-- ANCHOR_END: mconcat_batches

-- ANCHOR: foldl_eq
/-- A left fold started at `a` equals `a` combined with the right fold. -/
theorem foldl_combine (xs : List α) (a : α) :
    xs.foldl (· ⋄ ·) a = a ⋄ mconcat xs := by
  induction xs generalizing a with
  | nil =>
    -- Goal: a = a ⋄ empty
    show a = a ⋄ empty
    rw [LawfulMonoid.combine_empty]
  | cons x xs ih =>
    -- Goal: xs.foldl (· ⋄ ·) (a ⋄ x) = a ⋄ (x ⋄ mconcat xs)
    show xs.foldl (· ⋄ ·) (a ⋄ x) = a ⋄ (x ⋄ mconcat xs)
    rw [ih (a ⋄ x), LawfulMonoid.combine_assoc]

/-- For a lawful monoid, folding from the left and from the right agree. -/
theorem foldl_eq_mconcat (xs : List α) :
    xs.foldl (· ⋄ ·) empty = mconcat xs := by
  rw [foldl_combine, LawfulMonoid.empty_combine]
-- ANCHOR_END: foldl_eq

end Laws

-- ANCHOR: sub_unlawful
/-- Subtraction with `0`: the types are right, so `Monoid` accepts it. -/
example : Monoid Int where
  empty := 0
  combine a b := a - b

/-- But no lawful monoid on `Int` can have subtraction as its operation.
A class is a structure, so we can quantify over all its instances. -/
theorem sub_not_lawful (m : LawfulMonoid Int)
    (h : ∀ a b : Int, m.combine a b = a - b) : False := by
  -- Instantiate associativity at a = 0, b = 0, c = 1.
  have assoc := m.combine_assoc 0 0 1
  -- It says (0 - 0) - 1 = 0 - (0 - 1), that is, -1 = 1.
  rw [h, h, h, h] at assoc
  omega
-- ANCHOR_END: sub_unlawful

-- ANCHOR: sub_attempt
/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  d ≥ 1
where
 d := c
---
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 1
where
 b := a
-/
#guard_msgs in
example : LawfulMonoid Int where
  empty := 0
  combine a b := a - b
  combine_assoc a b c := by
    show a - b - c = a - (b - c)
    omega
  empty_combine a := by
    show 0 - a = a
    omega
  combine_empty a := by
    show a - 0 = a
    omega
-- ANCHOR_END: sub_attempt

end Ch14
