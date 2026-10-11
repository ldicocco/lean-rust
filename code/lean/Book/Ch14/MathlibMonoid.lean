import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Chapter 14 · In Mathlib: `Monoid`

Mathlib's `Monoid` class: written multiplicatively (`*` and `1`), assembled
from smaller classes with `extends`, with a default method (`npow`) and
default proofs. An instance for a type of our own, the library theorems it
unlocks, and `Multiplicative` as Mathlib's answer to "two monoids on ℕ".

This file does not import `Book.Ch14.Monoid`, so `Monoid` below is Mathlib's.
-/

namespace Ch14.InMathlib

-- ANCHOR: print_monoid
/--
info: class Monoid.{u_2} (M : Type u_2) : Type u_2
number of parameters: 1
parents:
  Monoid.toOne : One M
  Monoid.toMul : Mul M
  Monoid.toSemigroup : Semigroup M
  Monoid.toMulOneClass : MulOneClass M
  Monoid.toNPow : NPow M
fields:
  One.one : M
  Mul.mul : M → M → M
  Semigroup.mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c)
  MulOneClass.one_mul : ∀ (a : M), 1 * a = a
  MulOneClass.mul_one : ∀ (a : M), a * 1 = a
  NPow.npow : ℕ → M → M :=
    npowRecAuto
  Monoid.npow_zero : ∀ (x : M), x ^ 0 = 1 := by
    intros; rfl
  Monoid.npow_succ : ∀ (n : ℕ) (x : M), x ^ (n + 1) = x ^ n * x := by
    intros; rfl
constructor:
  Monoid.mk.{u_2} {M : Type u_2} [toOne : One M] [toMul : Mul M] (mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c))
    (one_mul : ∀ (a : M), 1 * a = a) (mul_one : ∀ (a : M), a * 1 = a) [toNPow : NPow M]
    (npow_zero : ∀ (x : M), x ^ 0 = 1 := by intros; rfl)
    (npow_succ : ∀ (n : ℕ) (x : M), x ^ (n + 1) = x ^ n * x := by intros; rfl) : Monoid M
field notation resolution order:
  Monoid, One, Mul, Semigroup, MulOneClass, NPow, MulOne
-/
#guard_msgs in
#print Monoid
-- ANCHOR_END: print_monoid

-- ANCHOR: stopwatch
/-- Elapsed times, combined by adding them up. -/
structure Stopwatch where
  ms : ℕ
  deriving Repr

/-- The instance gives `one`, `mul` and the three laws. `npow` and its two
laws are not given: the defaults are used. -/
instance : Monoid Stopwatch where
  one := ⟨0⟩
  mul a b := ⟨a.ms + b.ms⟩
  mul_assoc a b c := by
    show Stopwatch.mk (a.ms + b.ms + c.ms) = Stopwatch.mk (a.ms + (b.ms + c.ms))
    rw [Nat.add_assoc]
  one_mul a := by
    show Stopwatch.mk (0 + a.ms) = a
    rw [Nat.zero_add]
  mul_one _ := rfl
-- ANCHOR_END: stopwatch

-- ANCHOR: stopwatch_use
/-- info: { ms := 6 } -/
#guard_msgs in
#eval [Stopwatch.mk 1, ⟨2⟩, ⟨3⟩].prod

/-- info: { ms := 15 } -/
#guard_msgs in
#eval (⟨5⟩ : Stopwatch) ^ 3

/-- Library theorems about every monoid now apply to `Stopwatch`. -/
example (a b c : Stopwatch) : a * b * c = a * (b * c) := mul_assoc a b c

example (x : Stopwatch) (m n : ℕ) : x ^ (m + n) = x ^ m * x ^ n := pow_add x m n

example (xs ys : List Stopwatch) : (xs ++ ys).prod = xs.prod * ys.prod :=
  List.prod_append
-- ANCHOR_END: stopwatch_use

-- ANCHOR: multiplicative
/-- info: Nat.instMonoid -/
#guard_msgs in
#synth Monoid ℕ

/-- info: Nat.instAddMonoid -/
#guard_msgs in
#synth AddMonoid ℕ

/-- info: 24 -/
#guard_msgs in
#eval ([2, 3, 4] : List ℕ).prod

/-- info: 9 -/
#guard_msgs in
#eval ([2, 3, 4] : List ℕ).sum

-- `Multiplicative ℕ` is a copy of `ℕ` whose `*` is the addition of `ℕ`:
-- a newtype, as `Sum` was in the Rust example.
/-- info: 9 -/
#guard_msgs in
#eval ([.ofAdd 2, .ofAdd 3, .ofAdd 4] : List (Multiplicative ℕ)).prod
-- ANCHOR_END: multiplicative

end Ch14.InMathlib
