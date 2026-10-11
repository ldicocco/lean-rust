import Mathlib.Tactic.Ring

/-!
# Chapter 31 · Termination

Structural recursion, well-founded recursion with a measure (`termination_by`)
and a hand-written decrease proof (`decreasing_by`), lexicographic measures,
`partial` functions (which run but cannot be reasoned about) and fuel (which
makes a possibly non-terminating search total), and proofs by functional
induction (`fun_induction`) about a function defined by well-founded recursion.
-/

namespace Ch31

-- ANCHOR: structural
/-- Structural recursion: the recursive call is on `xs`, a piece of the
argument `x :: xs`. Lean accepts this without further ado. -/
def total : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + total xs
-- ANCHOR_END: structural

-- ANCHOR: log2
/-- The number of times `n` can be halved before it drops below 2. The call is
on `n / 2`, which is not a piece of `n`, so the recursion is not structural. -/
def log2 (n : ℕ) : ℕ := if n < 2 then 0 else 1 + log2 (n / 2)
-- ANCHOR_END: log2

-- ANCHOR: log2_suggest
/--
info: Try this:
  [apply] termination_by n
-/
#guard_msgs in
def log2' (n : ℕ) : ℕ := if n < 2 then 0 else 1 + log2' (n / 2)
termination_by?
-- ANCHOR_END: log2_suggest

-- ANCHOR: gcd_fail
/--
error: fail to show termination for
  Ch31.gcdBad
with errors
failed to infer structural recursion:
Cannot use parameter a:
  failed to eliminate recursive application
    gcdBad b (a % b)
Cannot use parameter b:
  failed to eliminate recursive application
    gcdBad b (a % b)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            a b
1) 61:49-65 ? ?
Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
def gcdBad (a b : ℕ) : ℕ := if b = 0 then a else gcdBad b (a % b)
-- ANCHOR_END: gcd_fail

-- ANCHOR: gcd
/-- Euclid's algorithm. The measure is `b`; the proof that it decreases is
`a % b < b`, which holds because `b ≠ 0` in the branch that recurses. -/
def euclid (a b : ℕ) : ℕ := if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by
  -- goal: a % b < b, with `h✝ : ¬b = 0` in the context
  apply Nat.mod_lt     -- `Nat.mod_lt : y > 0 → x % y < y`; remaining goal: b > 0
  omega                -- follows from `¬b = 0`
-- ANCHOR_END: gcd

-- ANCHOR: gcd_eval
/-- info: (6, 1, 21) -/
#guard_msgs in
#eval (euclid 48 18, euclid 17 5, euclid 0 21)
-- ANCHOR_END: gcd_eval

-- ANCHOR: ackermann
/-- Ackermann's function: neither argument decreases on every call, but the
pair does, in lexicographic order. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
-- ANCHOR_END: ackermann

-- ANCHOR: ackermann_eval
/-- info: [3, 5, 5, 61] -/
#guard_msgs in
#eval [ack 1 1, ack 2 1, ack 3 0, ack 3 3]
-- ANCHOR_END: ackermann_eval

-- ANCHOR: collatz
/-- Nobody knows whether this terminates for every `n` (the Collatz
conjecture), so no measure can be given. `partial` skips the check. -/
partial def collatz (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)

/-- info: 111 -/
#guard_msgs in
#eval collatz 27
-- ANCHOR_END: collatz

-- ANCHOR: collatz_opaque
/--
error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  collatz 6 = 8
-/
#guard_msgs in
example : collatz 6 = 8 := rfl
-- ANCHOR_END: collatz_opaque

-- ANCHOR: collatz_fuel
/-- The same search with fuel: at most `fuel` steps, then give up with
`none`. Structural recursion on `fuel`, so the function is total, and Lean can
compute with it inside proofs. -/
def collatzFuel : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, n =>
    if n ≤ 1 then some 0
    else (collatzFuel fuel (if n % 2 = 0 then n / 2 else 3 * n + 1)).map (· + 1)

example : collatzFuel 10 6 = some 8 := by decide
example : collatzFuel 5 6 = none := by decide
-- ANCHOR_END: collatz_fuel

-- ANCHOR: log2_induct
/--
info: Ch31.log2.induct (motive : ℕ → Prop) (case1 : ∀ (x : ℕ), x < 2 → motive x)
  (case2 : ∀ (x : ℕ), ¬x < 2 → motive (x / 2) → motive x) (n : ℕ) : motive n
-/
#guard_msgs in
#check log2.induct
-- ANCHOR_END: log2_induct

-- ANCHOR: pow_log2
/-- `log2` really is a logarithm: `2 ^ log2 n ≤ n` for every positive `n`. -/
theorem pow_log2_le (n : ℕ) (h : 1 ≤ n) : 2 ^ log2 n ≤ n := by
  fun_induction log2 n with
  | case1 n hlt =>
    -- `log2 n` was unfolded to `0`; goal: 2 ^ 0 ≤ n
    simp only [pow_zero]
    exact h
  | case2 n hge ih =>
    -- ih   : 1 ≤ n / 2 → 2 ^ log2 (n / 2) ≤ n / 2
    -- goal : 2 ^ (1 + log2 (n / 2)) ≤ n
    calc 2 ^ (1 + log2 (n / 2))
        = 2 * 2 ^ log2 (n / 2) := by ring
      _ ≤ 2 * (n / 2) := by
          have h2 := ih (by omega)   -- n ≥ 2, so n / 2 ≥ 1
          omega
      _ ≤ n := by omega
-- ANCHOR_END: pow_log2

end Ch31
