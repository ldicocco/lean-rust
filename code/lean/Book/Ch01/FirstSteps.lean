import Mathlib.Tactic.Ring

/-!
# Chapter 1 · First steps in Lean

Evaluating and checking expressions, a first function, the typing rule for
`if` (Lean's version of the Rust error in `ch01_if_branches`), a first theorem
(Gauss's formula, proved for every `n`), a false claim that Lean rejects,
indexing that requires a proof, and `#print axioms`.
-/

namespace Ch01

-- ANCHOR: eval_check
/-- info: 5 -/
#guard_msgs in
#eval 2 + 3

/-- info: 2 + 3 : ℕ -/
#guard_msgs in
#check 2 + 3

/-- info: fun n => n + 1 : ℕ → ℕ -/
#guard_msgs in
#check fun (n : ℕ) => n + 1
-- ANCHOR_END: eval_check

-- ANCHOR: add
/-- The same judgment as Rust's `fn add(x: i32, y: i32) -> i32`. -/
def add (x y : ℤ) : ℤ := x + y
-- ANCHOR_END: add

-- ANCHOR: add_check
/-- info: Ch01.add (x y : ℤ) : ℤ -/
#guard_msgs in
#check add

/-- info: 5 -/
#guard_msgs in
#eval add 2 3
-- ANCHOR_END: add_check

-- ANCHOR: if_branches
/--
error: Application type mismatch: The argument
  "not yet"
has type
  String
but is expected to have type
  ℕ
in the application
  if ready = true then 1 else "not yet"
-/
#guard_msgs in
def status (ready : Bool) : ℕ := if ready then 1 else "not yet"
-- ANCHOR_END: if_branches

-- ANCHOR: sum_to
/-- The sum `0 + 1 + ... + n`, defined by recursion on `n`. -/
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
-- ANCHOR_END: sum_to

-- ANCHOR: sum_to_eval
/-- info: 5050 -/
#guard_msgs in
#eval sumTo 100
-- ANCHOR_END: sum_to_eval

-- ANCHOR: gauss
/-- Gauss's formula, for every natural number `n`. (Stated with `2 * ...` on
the left to avoid division, which on `ℕ` rounds down.) -/
theorem gauss (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero =>
    -- Goal: 2 * sumTo 0 = 0 * (0 + 1). Both sides compute to 0.
    rfl
  | succ k ih =>
    -- ih   : 2 * sumTo k = k * (k + 1)
    -- Goal : 2 * sumTo (k + 1) = (k + 1) * (k + 1 + 1)
    rw [sumTo, mul_add, ih]
    -- Goal : 2 * (k + 1) + k * (k + 1) = (k + 1) * (k + 1 + 1)
    ring
-- ANCHOR_END: gauss

-- ANCHOR: examples
example : sumTo 3 = 6 := rfl

example : sumTo 10 = 55 := by decide
-- ANCHOR_END: examples

-- ANCHOR: false_claim
/--
error: Tactic `decide` proved that the proposition
  sumTo 3 = 7
is false
-/
#guard_msgs in
example : sumTo 3 = 7 := by decide
-- ANCHOR_END: false_claim

-- ANCHOR: first
/-- The first element of an array. The second argument is a *proof* that the
array is not empty, so the indexing `xs[0]` cannot fail. -/
def first (xs : Array ℕ) (h : 0 < xs.size) : ℕ := xs[0]

/-- info: 5 -/
#guard_msgs in
#eval first #[5, 6] (by decide)
-- ANCHOR_END: first

-- ANCHOR: first_unproved
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array ℕ
⊢ 0 < xs.size
-/
#guard_msgs in
def firstOrCrash (xs : Array ℕ) : ℕ := xs[0]
-- ANCHOR_END: first_unproved

-- ANCHOR: and_swap
/-- A proposition and its proof. Compare with `swap` in `ch01_first_types.rs`. -/
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
-- ANCHOR_END: and_swap

-- ANCHOR: gauss_auto
/-- The same theorem, with the arithmetic left to the `grind` tactic. -/
theorem gauss' (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumTo]; grind
-- ANCHOR_END: gauss_auto

-- ANCHOR: axioms
/-- info: 'Ch01.gauss' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gauss

/-- info: 'Ch01.gauss'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gauss'

/-- info: 'Ch01.and_swap' does not depend on any axioms -/
#guard_msgs in
#print axioms and_swap
-- ANCHOR_END: axioms

end Ch01
