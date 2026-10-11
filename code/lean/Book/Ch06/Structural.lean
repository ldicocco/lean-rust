import Mathlib.Data.Finset.Insert
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Tactic.Tauto

/-!
# Chapter 6 · The structural rules

The natural-deduction system of Chapter 4, redefined here, with contexts as
lists. Exchange, weakening and contraction are not rules of the system, yet
they hold: we prove them *admissible* by induction on derivations, through one
general lemma (derivability is monotone in the context). We also contrast
admissible rules with derivable ones, and lists of hypotheses with multisets
and sets.
-/

namespace Ch06

-- ANCHOR: formula
/-- Propositional formulas, as in Chapter 4. -/
inductive Formula where
  | atom (name : String)
  | top
  | bot
  | conj (A B : Formula)
  | disj (A B : Formula)
  | imp (A B : Formula)
  deriving DecidableEq, Repr
-- ANCHOR_END: formula

open Formula

-- ANCHOR: proves
/-- `Proves Γ A`: the sequent `Γ ⊢ A` is derivable in natural deduction.
Lean lists grow at the front, so the rules write `A :: Γ` for what the
mathematics writes `Γ, A`. -/
inductive Proves : List Formula → Formula → Prop where
  | hyp {Γ A} : A ∈ Γ → Proves Γ A
  | topI {Γ} : Proves Γ top
  | botE {Γ C} : Proves Γ bot → Proves Γ C
  | conjI {Γ A B} : Proves Γ A → Proves Γ B → Proves Γ (conj A B)
  | conjE₁ {Γ A B} : Proves Γ (conj A B) → Proves Γ A
  | conjE₂ {Γ A B} : Proves Γ (conj A B) → Proves Γ B
  | disjI₁ {Γ A B} : Proves Γ A → Proves Γ (disj A B)
  | disjI₂ {Γ A B} : Proves Γ B → Proves Γ (disj A B)
  | disjE {Γ A B C} :
      Proves Γ (disj A B) → Proves (A :: Γ) C → Proves (B :: Γ) C → Proves Γ C
  | impI {Γ A B} : Proves (A :: Γ) B → Proves Γ (imp A B)
  | impE {Γ A B} : Proves Γ (imp A B) → Proves Γ A → Proves Γ B
-- ANCHOR_END: proves

section Examples

variable (A B : Formula)

-- ANCHOR: examples
/-- `A ∧ B ⊢ B ∧ A`. Both premises of `conjI` receive the whole context, and
each of them uses the hypothesis `A ∧ B`: two uses of one assumption. -/
example : Proves [conj A B] (conj B A) :=
  .conjI (.conjE₂ (.hyp List.mem_cons_self)) (.conjE₁ (.hyp List.mem_cons_self))

/-- `A ⊢ A ∧ A`: one assumption, used twice. -/
example : Proves [A] (conj A A) :=
  .conjI (.hyp (by simp)) (.hyp (by simp))

/-- `A, B ⊢ A`: the assumption `B` is never used. -/
example : Proves [A, B] A :=
  .hyp (by simp)

/-- `⊢ A → B → A`: after two `impI` steps the context is `[B, A]`, and the
hypothesis rule picks `A` out of it, ignoring `B`. -/
example : Proves [] (imp A (imp B A)) :=
  .impI (.impI (.hyp (by simp)))
-- ANCHOR_END: examples

end Examples

-- ANCHOR: mono
/-- Derivability is monotone in the context: if every hypothesis of `Γ` is
also a hypothesis of `Δ`, everything provable from `Γ` is provable from `Δ`.
The proof transforms the derivation of `Γ ⊢ C`, rule by rule, into a
derivation of `Δ ⊢ C`. -/
theorem Proves.mono {Γ Δ : List Formula} {C : Formula}
    (h : Proves Γ C) (sub : Γ ⊆ Δ) : Proves Δ C := by
  induction h generalizing Δ with
  | hyp mem =>
    -- The only place where the context is inspected: `A ∈ Γ` and `Γ ⊆ Δ`.
    exact .hyp (sub mem)
  | topI => exact .topI
  | botE _ ih => exact .botE (ih sub)
  | conjI _ _ ih₁ ih₂ => exact .conjI (ih₁ sub) (ih₂ sub)
  | conjE₁ _ ih => exact .conjE₁ (ih sub)
  | conjE₂ _ ih => exact .conjE₂ (ih sub)
  | disjI₁ _ ih => exact .disjI₁ (ih sub)
  | disjI₂ _ ih => exact .disjI₂ (ih sub)
  | disjE _ _ _ ih ihA ihB =>
    -- The branches have one more hypothesis on both sides: `A :: Γ ⊆ A :: Δ`.
    exact .disjE (ih sub) (ihA (List.cons_subset_cons _ sub))
      (ihB (List.cons_subset_cons _ sub))
  | impI _ ih =>
    -- Same here: the premise lives in `A :: Γ`, so we extend `sub` by `A`.
    exact .impI (ih (List.cons_subset_cons _ sub))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ sub) (ih₂ sub)
-- ANCHOR_END: mono

section Structural

variable {Γ Γ₁ Γ₂ : List Formula} {A B C : Formula}

-- ANCHOR: weakening
/-- Weakening: an extra hypothesis never hurts. -/
theorem weakening (h : Proves Γ C) : Proves (A :: Γ) C :=
  h.mono (List.subset_cons_self A Γ)
-- ANCHOR_END: weakening

-- ANCHOR: exchange
/-- Exchange: two neighboring hypotheses may swap places, anywhere in the
context. -/
theorem exchange (h : Proves (Γ₁ ++ A :: B :: Γ₂) C) :
    Proves (Γ₁ ++ B :: A :: Γ₂) C :=
  h.mono (by
    intro X hX
    -- hX : X ∈ Γ₁ ++ A :: B :: Γ₂,   goal : X ∈ Γ₁ ++ B :: A :: Γ₂
    simp only [List.mem_append, List.mem_cons] at hX ⊢
    tauto)
-- ANCHOR_END: exchange

-- ANCHOR: contraction
/-- Contraction: two copies of a hypothesis can be merged into one. -/
theorem contraction (h : Proves (A :: A :: Γ) C) : Proves (A :: Γ) C :=
  h.mono (by
    intro X hX
    simp only [List.mem_cons] at hX ⊢
    tauto)
-- ANCHOR_END: contraction

-- ANCHOR: same_elements
/-- Contexts with the same elements prove the same formulas: for this system,
a context might as well be a *set*. -/
theorem proves_iff_of_same_elements {Γ Δ : List Formula}
    (h₁ : Γ ⊆ Δ) (h₂ : Δ ⊆ Γ) : Proves Γ C ↔ Proves Δ C :=
  ⟨fun h => h.mono h₁, fun h => h.mono h₂⟩
-- ANCHOR_END: same_elements

-- ANCHOR: derivable
/-- A *derivable* rule: from `Γ ⊢ A ∧ B` conclude `Γ ⊢ B ∧ A`. The proof is a
fixed combination of primitive rules (a macro); it never looks inside `h`. -/
theorem conj_comm_rule (h : Proves Γ (conj A B)) : Proves Γ (conj B A) :=
  .conjI (.conjE₂ h) (.conjE₁ h)
-- ANCHOR_END: derivable

-- ANCHOR: admissible_use
/-- Double-negation introduction as a rule: from `Γ ⊢ A` conclude
`Γ ⊢ (A → ⊥) → ⊥`. The derivation of `A` is needed in the bigger context
`(A → ⊥) :: Γ`, and no fixed combination of primitive rules can move it
there: we call the admissible `weakening`, which rebuilds `h` by induction. -/
theorem dni_rule (h : Proves Γ A) : Proves Γ (imp (imp A bot) bot) :=
  .impI (.impE (.hyp List.mem_cons_self) (weakening h))
-- ANCHOR_END: admissible_use

end Structural

-- ANCHOR: lists_multisets_sets
-- As lists, order and multiplicity both matter:
example : [atom "A", atom "B"] ≠ [atom "B", atom "A"] := by decide
example : [atom "A", atom "A"] ≠ [atom "A"] := by decide

-- As multisets, order is forgotten (exchange is built in) but
-- multiplicity is not:
example (A B : Formula) (Γ : Multiset Formula) :
    A ::ₘ B ::ₘ Γ = B ::ₘ A ::ₘ Γ :=
  Multiset.cons_swap A B Γ
example : ({atom "A", atom "A"} : Multiset Formula) ≠ {atom "A"} := by decide

-- As sets, both are forgotten (exchange and contraction are built in):
example (A B : Formula) : ({A, B} : Finset Formula) = {B, A} :=
  Finset.pair_comm A B
example (A : Formula) (Γ : Finset Formula) : insert A (insert A Γ) = insert A Γ :=
  Finset.insert_idem A Γ
-- ANCHOR_END: lists_multisets_sets

end Ch06
