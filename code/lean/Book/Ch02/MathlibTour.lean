import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Chapter 2 · A first tour of Mathlib

The notation Mathlib adds (`ℕ`, `ℤ`, `ℚ`), the four tactics the book uses most
(`ring`, `linarith`, `norm_num`, `positivity`), finding lemmas with `exact?`
and `apply?`, and Mathlib's naming conventions. The file imports only the four
tactic modules it uses, not the whole library.
-/

namespace Ch02

-- ANCHOR: notation
/-- info: 3 : ℕ -/
#guard_msgs in
#check (3 : Nat)

/-- info: -3 : ℤ -/
#guard_msgs in
#check (-3 : Int)

/-- info: 1 / 3 : ℚ -/
#guard_msgs in
#check (1 / 3 : ℚ)

example : ℕ = Nat := rfl
-- ANCHOR_END: notation

-- ANCHOR: ring
/-- `ring` proves equations that hold in every commutative ring (or semiring,
such as `ℕ`): it normalizes both sides as polynomials and compares them. -/
theorem square_of_sum (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- Two fills at the same price cost the same as one fill of the total. -/
theorem cost_split (price q₁ q₂ : ℕ) : price * q₁ + price * q₂ = price * (q₁ + q₂) := by
  ring
-- ANCHOR_END: ring

-- ANCHOR: linarith
/-- `linarith` proves a linear inequality from linear hypotheses. Here, over
the rationals: the mid price lies strictly between the bid and the ask. -/
theorem mid_between (bid ask : ℚ) (h : bid < ask) :
    bid < (bid + ask) / 2 ∧ (bid + ask) / 2 < ask := by
  constructor   -- split the ∧ into two goals
  · linarith
  · linarith
-- ANCHOR_END: linarith

-- ANCHOR: omega_rationals
/--
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
example (bid ask : ℚ) (h : bid < ask) : bid < (bid + ask) / 2 := by
  omega
-- ANCHOR_END: omega_rationals

-- ANCHOR: norm_num
/-- `norm_num` evaluates and normalizes numerical expressions: the spread of
the demo book, in dollars. -/
example : (10125 : ℚ) / 100 - 10075 / 100 = 1 / 2 := by
  norm_num

example : (2 : ℤ) ^ 10 - 24 = 1000 := by
  norm_num
-- ANCHOR_END: norm_num

-- ANCHOR: positivity
/-- `positivity` proves goals of the form `0 < e` or `0 ≤ e` by looking at the
shape of `e`: squares are nonnegative, sums of nonnegatives are, and so on. -/
example (x : ℤ) (n : ℕ) : 0 < x ^ 2 + n + 1 := by
  positivity
-- ANCHOR_END: positivity

-- ANCHOR: exact_search
/--
info: Try this:
  [apply] exact Nat.mul_le_mul_left price h
-/
#guard_msgs in
example (price qty : ℕ) (h : qty ≤ 100) : price * qty ≤ price * 100 := by
  exact?
-- ANCHOR_END: exact_search

-- ANCHOR: exact_found
/-- The proof `exact?` found, pasted in. -/
theorem cost_le_cap (price qty : ℕ) (h : qty ≤ 100) : price * qty ≤ price * 100 :=
  Nat.mul_le_mul_left price h
-- ANCHOR_END: exact_found

-- ANCHOR: names
/-- info: Nat.add_comm (n m : ℕ) : n + m = m + n -/
#guard_msgs in
#check Nat.add_comm

/-- info: add_comm.{u_1} {G : Type u_1} [AddCommMagma G] (a b : G) : a + b = b + a -/
#guard_msgs in
#check add_comm

/-- info: Nat.lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k -/
#guard_msgs in
#check Nat.lt_of_lt_of_le

/-- info: Nat.succ_le_iff {m n : ℕ} : m.succ ≤ n ↔ m < n -/
#guard_msgs in
#check Nat.succ_le_iff
-- ANCHOR_END: names

-- ANCHOR: mul_le_mul
/--
info: mul_le_mul.{u_1} {α : Type u_1} [Mul α] [Zero α] [Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b)
  (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d
-/
#guard_msgs in
#check mul_le_mul
-- ANCHOR_END: mul_le_mul

end Ch02
