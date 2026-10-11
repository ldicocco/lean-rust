import Mathlib.Data.Nat.Find

/-!
# Chapter 10 · `Prop` and `Type`

The two worlds of Lean: propositions, whose proofs are irrelevant, and types,
whose values are data. Impredicativity of `Prop`; `Exists`, `Sigma`, `PSigma`
and `Subtype`; the elimination restriction that keeps a witness from leaking
out of a proof; `theorem` vs `def`; `Nat.le` as an inductive family; and the
term behind a tactic proof.
-/

namespace Ch10

/-! ## Two universes -/

-- ANCHOR: universes
/-- info: 2 + 2 = 4 : Prop -/
#guard_msgs in
#check 2 + 2 = 4

/-- info: ℕ : Type -/
#guard_msgs in
#check ℕ

/-- info: Prop : Type -/
#guard_msgs in
#check Prop

/-- info: Type : Type 1 -/
#guard_msgs in
#check Type
-- ANCHOR_END: universes

-- ANCHOR: bool_vs_prop
/-- A `Bool` is data: two different values that a program can inspect. -/
example : true ≠ false := by decide

/-- A proposition is a type whose values are proofs, and any two proofs of
the same proposition are equal, by definition: `rfl` proves it. -/
theorem proof_irrelevance (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl
-- ANCHOR_END: bool_vs_prop

-- ANCHOR: irrelevance_example
/-- Two proofs of `3 ≤ 5`, built differently (one by a decision procedure, one
by arithmetic), are the same proof as far as Lean is concerned. -/
example : (by decide : 3 ≤ 5) = (by omega : 3 ≤ 5) := rfl
-- ANCHOR_END: irrelevance_example

/-! ## Impredicativity -/

-- ANCHOR: impredicative
-- Quantifying over all propositions still gives a proposition...
/-- info: ∀ (p : Prop), p → p : Prop -/
#guard_msgs in
#check ∀ p : Prop, p → p

-- ...but quantifying over all types gives something bigger than a type.
/-- info: (α : Type) → α → α : Type 1 -/
#guard_msgs in
#check (α : Type) → α → α
-- ANCHOR_END: impredicative

/-! ## Four kinds of pairs -/

-- ANCHOR: pairs
/-- info: ∃ n, n > 3 : Prop -/
#guard_msgs in
#check ∃ n : ℕ, n > 3

/-- info: { n // n > 3 } : Type -/
#guard_msgs in
#check {n : ℕ // n > 3}

/-- info: (n : ℕ) ×' n > 3 : Type -/
#guard_msgs in
#check (n : ℕ) ×' n > 3

/-- info: (n : ℕ) × Fin n : Type -/
#guard_msgs in
#check (n : ℕ) × Fin n
-- ANCHOR_END: pairs

-- ANCHOR: subtype
/-- A number greater than 3, with the proof attached. -/
def four : {n : ℕ // n > 3} := ⟨4, by decide⟩

/-- The witness of a `Subtype` is data, and a program can return it. -/
def Subtype.witness (x : {n : ℕ // n > 3}) : ℕ := x.val

/-- info: 4 -/
#guard_msgs in
#eval Subtype.witness four

/-- Two elements of a subtype are equal as soon as their values are: the
proofs are irrelevant. -/
example (x y : {n : ℕ // n > 3}) (h : x.val = y.val) : x = y := Subtype.ext h

/-- A dependent pair whose second component is data: a length, and an index
below it. -/
def lastIndex : (n : ℕ) × Fin (n + 1) := ⟨3, 3⟩
-- ANCHOR_END: subtype

/-! ## The elimination restriction -/

-- ANCHOR: no_witness
/--
error: Invalid projection: Cannot project a value of non-propositional type
  ℕ
from the expression
  h
which has propositional type
  ∃ n, n > 3
-/
#guard_msgs in
def witness (h : ∃ n : ℕ, n > 3) : ℕ := h.1
-- ANCHOR_END: no_witness

-- ANCHOR: why_restriction
/-- Why the restriction is necessary: these two proofs have different
witnesses... -/
theorem proofWith4 : ∃ n : ℕ, n > 3 := ⟨4, by decide⟩
theorem proofWith5 : ∃ n : ℕ, n > 3 := ⟨5, by decide⟩

/-- ...and yet they are equal, by proof irrelevance. A function that returned
the witness would map equal arguments to 4 and to 5. -/
example : proofWith4 = proofWith5 := rfl
-- ANCHOR_END: why_restriction

-- ANCHOR: inside_proofs
/-- Inside a proof, taking an `Exists` apart is fine: the result is a proof
too, so the witness cannot escape into data. -/
theorem exists_gt_two (h : ∃ n : ℕ, n > 3) : ∃ n : ℕ, n > 2 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩
-- ANCHOR_END: inside_proofs

-- ANCHOR: small_elim
/-- The exceptions: a proposition with at most one constructor whose fields
are all proofs (or appear in the type) can be eliminated into data, because
there is nothing to leak. `False` has no constructors... -/
def fromFalse (h : False) : ℕ := h.elim

/-- ...and `And` has one, with two proof fields. -/
def fromAnd (p q : Prop) (h : p ∧ q) : ℕ :=
  match h with
  | ⟨_, _⟩ => 42
-- ANCHOR_END: small_elim

-- ANCHOR: escape_hatches
/-- Classical choice picks *some* witness, but no program can compute it. -/
noncomputable def someWitness (h : ∃ n : ℕ, n > 3) : ℕ := Classical.choose h

theorem someWitness_spec (h : ∃ n : ℕ, n > 3) : someWitness h > 3 :=
  Classical.choose_spec h

/-- For a decidable property of natural numbers, the witness can be *found*:
`Nat.find` searches 0, 1, 2, ... and the proof of existence guarantees that the
search stops. -/
def firstAbove3 : ℕ := Nat.find proofWith5

/-- info: 4 -/
#guard_msgs in
#eval firstAbove3
-- ANCHOR_END: escape_hatches

/-! ## `theorem` vs `def` -/

-- ANCHOR: theorem_vs_def
/--
error: type of theorem `Ch10.three` is not a proposition
  ℕ
-/
#guard_msgs in
theorem three : ℕ := 3

/--
warning: Definition `twoPlusTwo` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
-/
#guard_msgs in
def twoPlusTwo : 2 + 2 = 4 := rfl
-- ANCHOR_END: theorem_vs_def

/-! ## An inductive family -/

-- ANCHOR: nat_le
/--
info: protected inductive Nat.le : ℕ → ℕ → Prop
number of parameters: 1
constructors:
Nat.le.refl : ∀ {n : ℕ}, n.le n
Nat.le.step : ∀ {n m : ℕ}, n.le m → n.le m.succ
-/
#guard_msgs in
#print Nat.le

/-- `3 ≤ 5`, built from the constructors: reflexivity gives `3 ≤ 3`, and two
steps give `3 ≤ 4` and `3 ≤ 5`. -/
theorem three_le_five : 3 ≤ 5 := Nat.le.step (Nat.le.step Nat.le.refl)

/-- No constructor can build `5 ≤ 3`: `cases` tries both and finds that each
would need a smaller instance of the same impossible fact, down to `5 ≤ 0`. -/
theorem not_five_le_three : ¬ 5 ≤ 3 := by
  intro h
  cases h with
  | step h => cases h with
    | step h => cases h with
      | step h => cases h
-- ANCHOR_END: nat_le

/-! ## The term behind a tactic proof -/

-- ANCHOR: print_tactic
theorem and_swap_tactics (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

/--
info: theorem Ch10.and_swap_tactics : ∀ (p q : Prop), p ∧ q → q ∧ p :=
fun p q h => And.casesOn h fun hp hq => ⟨hq, hp⟩
-/
#guard_msgs in
#print and_swap_tactics
-- ANCHOR_END: print_tactic

end Ch10
