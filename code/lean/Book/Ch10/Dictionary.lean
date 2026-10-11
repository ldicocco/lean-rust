import Mathlib.Data.Nat.Notation

/-!
# Chapter 10 · The Curry–Howard dictionary

The connectives of propositional logic and the type formers of Lean, side by
side: every theorem here has a twin program on data, and both are written as
ordinary terms. Then quantifiers as dependent functions and pairs, proof
detours as β-redexes, and why Lean, unlike Rust, is consistent as a logic.
-/

namespace Ch10

variable (p q r : Prop)
variable (α β γ : Type)

/-! ## Conjunction is the product -/

-- ANCHOR: conjunction
/-- ∧-introduction: a pair of proofs. -/
theorem and_intro (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

/-- ∧-elimination: a projection. -/
theorem and_left : p ∧ q → p := fun h => h.1

/-- p ∧ q → q ∧ p -/
theorem and_swap : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩

/-- The same program on data: a pair of values, swapped. -/
def swap : α × β → β × α := fun ⟨a, b⟩ => ⟨b, a⟩
-- ANCHOR_END: conjunction

-- ANCHOR: conjunction_check
/-- info: Ch10.and_swap (p q : Prop) : p ∧ q → q ∧ p -/
#guard_msgs in
#check and_swap

/-- info: Ch10.swap (α β : Type) : α × β → β × α -/
#guard_msgs in
#check swap
-- ANCHOR_END: conjunction_check

/-! ## Disjunction is the sum -/

-- ANCHOR: disjunction
/-- ∨-elimination is a `match` with one arm per side. -/
theorem or_swap : p ∨ q → q ∨ p := fun h =>
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

/-- The same program on data, with `Sum` (Rust's `Either`, or `Result`). -/
def sumSwap : α ⊕ β → β ⊕ α := fun s =>
  match s with
  | .inl a => .inr a
  | .inr b => .inl b
-- ANCHOR_END: disjunction

/-! ## Implication is the function type -/

-- ANCHOR: implication
/-- →-elimination, modus ponens: application. -/
theorem modus_ponens : (p → q) → p → q := fun f hp => f hp

/-- Hypothetical syllogism: composition. -/
theorem syllogism : (p → q) → (q → r) → (p → r) := fun f g hp => g (f hp)

/-- Currying, in both directions: an `Iff` is a pair of implications. -/
theorem curry_iff : (p ∧ q → r) ↔ (p → q → r) :=
  ⟨fun f hp hq => f ⟨hp, hq⟩, fun g ⟨hp, hq⟩ => g hp hq⟩

/-- Distributivity of ∧ over ∨. -/
theorem distrib : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := fun ⟨hp, hqr⟩ =>
  match hqr with
  | .inl hq => .inl ⟨hp, hq⟩
  | .inr hr => .inr ⟨hp, hr⟩
-- ANCHOR_END: implication

/-! ## Truth, falsity and negation -/

-- ANCHOR: negation
/-- ⊤ is the proposition with one trivial proof, like the unit type. -/
theorem truth : True := trivial

/-- Ex falso quodlibet: `False` has no constructors, so a `match` on a proof
of `False` needs no arms. -/
theorem ex_falso : False → p := fun h => nomatch h

/-- The same for data: `Empty` is Lean's `enum Void {}`. -/
def emptyElim : Empty → α := fun e => nomatch e

/-- `¬p` is *defined* as `p → False`. -/
example : (¬p) = (p → False) := rfl

theorem double_negation_intro : p → ¬¬p := fun hp hnp => hnp hp

theorem contrapositive : (p → q) → ¬q → ¬p := fun f hnq hp => hnq (f hp)

theorem non_contradiction : ¬(p ∧ ¬p) := fun ⟨hp, hnp⟩ => hnp hp
-- ANCHOR_END: negation

/-! ## Contraction is free in Lean -/

-- ANCHOR: contraction
/-- ¬(p ∨ q) → ¬p ∧ ¬q. The hypothesis `h` is used twice, and nothing has to
be said about it: Lean's logic has contraction built in. -/
theorem de_morgan : ¬(p ∨ q) → ¬p ∧ ¬q :=
  fun h => ⟨fun hp => h (.inl hp), fun hq => h (.inr hq)⟩

/-- p → p ∧ p, and its twin on data, α → α × α. Both use their argument twice. -/
theorem dup : p → p ∧ p := fun hp => ⟨hp, hp⟩

def dupData : α → α × α := fun a => (a, a)
-- ANCHOR_END: contraction

/-! ## Quantifiers -/

-- ANCHOR: forall
/-- ∀ over values: a *dependent* function. Given `n`, it returns a proof about
that very `n`; the result type depends on the argument. -/
theorem add_zero_all : ∀ n : ℕ, n + 0 = n :=
  fun n => show n + 0 = n from rfl

/-- info: add_zero_all 5 : 5 + 0 = 5 -/
#guard_msgs in
#check add_zero_all 5

/-- ∀ over types: a generic function, Rust's `fn identity<A>(a: A) -> A`. -/
def identity (α : Type) : α → α := fun a => a

/-- ∀ over propositions: the same program, read as a theorem. -/
theorem self_implication : ∀ (p : Prop), p → p := fun _ hp => hp
-- ANCHOR_END: forall

-- ANCHOR: exists
/-- ∃ is a dependent pair: a witness, and a proof about that witness. -/
theorem exists_big : ∃ n : ℕ, n > 100 := ⟨101, by decide⟩

/-- Using an existential: take the pair apart and use both components. -/
theorem exists_bigger (h : ∃ n : ℕ, n > 100) : ∃ m : ℕ, m > 101 := by
  obtain ⟨n, hn⟩ := h      -- n : ℕ, hn : n > 100
  exact ⟨n + 1, by omega⟩  -- the new witness is n + 1
-- ANCHOR_END: exists

/-! ## Normalization is computation -/

-- ANCHOR: detour
/-- A program with a detour: build a pair, then immediately take it apart. As
a proof, this is ∧-introduction followed at once by ∧-elimination. -/
def detour (a : α) : α := (fun pair : α × α => pair.1) (a, a)

-- `#reduce` normalizes: the β-redex and the projection disappear.
/-- info: fun α a => a -/
#guard_msgs in
#reduce detour

/-- The same detour as a proof. -/
theorem detour_proof (hp : p) : p := (fun h : p ∧ p => h.1) ⟨hp, hp⟩
-- ANCHOR_END: detour

/-! ## Lean is consistent: totality -/

-- ANCHOR: no_loop
-- The Rust "proof" `fn by_recursion<A>() -> A { by_recursion() }`, in Lean:
-- rejected, because Lean cannot see why it would terminate.
/--
error: fail to show termination for
  Ch10.byRecursion
with errors
failed to infer structural recursion:
Not considering parameter p of Ch10.byRecursion:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, `Ch10.byRecursion` does not take any (non-fixed) arguments
-/
#guard_msgs in
def byRecursion (p : Prop) : p := byRecursion p
-- ANCHOR_END: no_loop

-- ANCHOR: partial
/-- `partial` turns off the termination check, but only for types that have a
value anyway: then the loop cannot be the only "proof". -/
partial def spin (n : ℕ) : ℕ := spin (n + 1)

-- A `partial` definition is opaque: Lean knows its type and nothing else.
/-- info: opaque Ch10.spin : ℕ → ℕ -/
#guard_msgs in
#print spin

-- For `False` there is no value to fall back on, and `partial` is refused.
/--
error: failed to compile 'partial' definition `Ch10.loopProof`, could not prove that the type
  ∀ (n : ℕ), False
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
partial def loopProof (n : ℕ) : False := loopProof n
-- ANCHOR_END: partial

-- ANCHOR: sorry
-- `sorry` proves anything, like Rust's `todo!()`. Lean warns, and remembers.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem cheat : False := sorry

/-- info: 'Ch10.cheat' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms cheat

/-- info: 'Ch10.de_morgan' does not depend on any axioms -/
#guard_msgs in
#print axioms de_morgan
-- ANCHOR_END: sorry

end Ch10
