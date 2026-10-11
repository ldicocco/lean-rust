import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Basic

/-!
# Chapter 27 · Coercions and subtypes in Lean

Lean has no subtyping: a term has a type, and no rule lets it be used at a
bigger one. What looks like subtyping is a *coercion*: the elaborator inserts a
function call, marked `↑`. Lean's *subtypes* `{x // p x}` are something else
again: refinements, whose values are pairs of a value and a proof.
-/

namespace Ch27

-- ANCHOR: coe_nat_int
/-- A function on integers. -/
def double (z : ℤ) : ℤ := 2 * z

/-- info: double ↑3 : ℤ -/
#guard_msgs in
#check double (3 : ℕ)

/-- info: fun n => double ↑n : ℕ → ℤ -/
#guard_msgs in
#check fun (n : ℕ) => double n

/-- The `↑` is an ordinary function, `Int.ofNat`. -/
example (n : ℕ) : (n : ℤ) = Int.ofNat n := rfl
-- ANCHOR_END: coe_nat_int

-- ANCHOR: no_coe_back
/--
error: Type mismatch
  z
has type
  ℤ
but is expected to have type
  ℕ
-/
#guard_msgs in
def toNat (z : ℤ) : ℕ := z
-- ANCHOR_END: no_coe_back

-- ANCHOR: custom_coe
/-- An amount of money, in cents. -/
structure Cents where
  amount : ℕ

/-- Cents can be used where an integer is expected. -/
instance : Coe Cents ℤ where
  coe c := c.amount

/-- The sum of a list of signed amounts. -/
def balance (deltas : List ℤ) : ℤ := deltas.sum

/-- info: fun c => double ↑c.amount : Cents → ℤ -/
#guard_msgs in
#check fun (c : Cents) => double c

/-- info: 150 -/
#guard_msgs in
#eval balance [Cents.mk 250, -100]
-- ANCHOR_END: custom_coe

-- ANCHOR: subtype
/-- The even natural numbers, as a subtype: each value is a pair of a number
and a proof that it is even. -/
abbrev Even := {n : ℕ // n % 2 = 0}

def four : Even := ⟨4, rfl⟩

/-- info: 5 -/
#guard_msgs in
#eval four.val + 1

/-- The proof travels with the value, and can be used. -/
theorem four_even : four.val % 2 = 0 := four.property
-- ANCHOR_END: subtype

-- ANCHOR: no_lift
/--
error: Type mismatch
  xs
has type
  List Even
but is expected to have type
  List ℕ
-/
#guard_msgs in
def evens (xs : List Even) : List ℕ := xs

/-- What works is an explicit map, which builds a new list. -/
def evens' (xs : List Even) : List ℕ := xs.map Subtype.val
-- ANCHOR_END: no_lift

end Ch27
