import Book.Ch02.Basics

/-!
# Chapter 2 · `do` notation, `IO` and totality

`do` blocks in `IO`, `Except` and `Id`; `let mut`, `for` and early `return`
(sugar for pure code, as a theorem shows); the termination checker, `partial`
and `termination_by`.
-/

namespace Ch02

-- ANCHOR: greet
/-- An `IO` action: a description of effects, run by `#eval` or by `main`. -/
def greet (name : String) : IO Unit := do
  IO.println s!"hello, {name}"
  if name.length > 3 then
    IO.println "that is a long name"

/--
info: hello, Grace
that is a long name
-/
#guard_msgs in
#eval greet "Grace"
-- ANCHOR_END: greet

-- ANCHOR: parse_nat
/-- Parse a decimal number. In a `do` block for `Except`, `←` runs a fallible
step and stops at the first error, like Rust's `?`; `throw` is `return Err(..)`. -/
def parseNat (s : String) : Except ParseError Nat := do
  if s.isEmpty then throw .empty
  let mut n := 0
  for c in s.toList do
    let d ← parseDigit c
    n := 10 * n + d
  return n

/-- info: Except.ok 2024 -/
#guard_msgs in
#eval parseNat "2024"

/-- info: Except.error (Ch02.ParseError.notADigit 'O') -/
#guard_msgs in
#eval parseNat "2O24"
-- ANCHOR_END: parse_nat

-- ANCHOR: sum_squares
/-- A loop with a mutable accumulator, inside `Id.run do`: the function is
pure, and its type says so. -/
def sumSquares (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x * x
  return total

/-- info: 14 -/
#guard_msgs in
#eval sumSquares [1, 2, 3]

/-- The loop is a left fold in disguise, and Lean can prove it. -/
theorem sumSquares_eq_foldl (xs : List Nat) :
    sumSquares xs = xs.foldl (fun total x => total + x * x) 0 := by
  simp [sumSquares]
-- ANCHOR_END: sum_squares

-- ANCHOR: early_return
/-- Early `return` from inside a loop. -/
def firstNegative (xs : List Int) : Option Int := Id.run do
  for x in xs do
    if x < 0 then return some x
  return none

/-- info: some (-1) -/
#guard_msgs in
#eval firstNegative [3, -1, -5]
-- ANCHOR_END: early_return

-- ANCHOR: collatz_rejected
/--
error: fail to show termination for
  Ch02.collatz
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    collatz (n / 2)


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝¹ : ¬n ≤ 1
h✝ : ¬(n % 2 == 0) = true
⊢ 3 * n + 1 < n
-/
#guard_msgs in
def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)
-- ANCHOR_END: collatz_rejected

-- ANCHOR: collatz_partial
/-- Nobody knows whether this terminates for every `n`, so it must be
`partial`. Lean compiles and runs it, but will not unfold it in proofs. -/
partial def collatzSteps (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

/-- info: 111 -/
#guard_msgs in
#eval collatzSteps 27
-- ANCHOR_END: collatz_partial

-- ANCHOR: bogus
/--
error: fail to show termination for
  Ch02.bogus
with errors
failed to infer structural recursion:
Not considering parameter n of Ch02.bogus:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, `Ch02.bogus` does not take any (non-fixed) arguments
-/
#guard_msgs in
def bogus (n : Nat) : Nat := bogus n + 1
-- ANCHOR_END: bogus

-- ANCHOR: automatic_termination
/-- Not structural (`n / 10` is not a sub-term of `n`), but Lean finds and
proves the decreasing measure on its own. -/
def digits (n : Nat) : List Nat :=
  if n < 10 then [n] else digits (n / 10) ++ [n % 10]

/-- Binary search for the first `n` in `[lo, hi)` where `ok` holds (for a
monotone `ok`). Lean guesses the measure `hi - lo` by itself. -/
def search (lo hi : Nat) (ok : Nat → Bool) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if ok mid then search lo mid ok else search (mid + 1) hi ok
  else lo

/-- info: ([2, 0, 2, 4], 8) -/
#guard_msgs in
#eval (digits 2024, search 0 100 (fun n => n * n ≥ 50))
-- ANCHOR_END: automatic_termination

-- ANCHOR: gcd
/-- Euclid's algorithm. Lean cannot guess why it terminates, so we say which
argument decreases (`termination_by`) and prove that it does (`decreasing_by`). -/
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by
  -- Goal: a % b < b, knowing ¬b = 0.
  apply Nat.mod_lt   -- a % b < b holds whenever b > 0;
  omega              -- and b > 0 follows from ¬b = 0.

/-- info: 6 -/
#guard_msgs in
#eval gcd 12 18
-- ANCHOR_END: gcd

end Ch02
