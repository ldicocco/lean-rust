import Book.Ch09.Syntax
import Mathlib.Logic.Relation

/-!
# Chapter 9 · Semantics

Values, the small-step call-by-value reduction relation as an inductive
predicate, its reflexive-transitive closure, stuck terms, and the first
theorem about the semantics: evaluation is deterministic.
-/

namespace Ch09

open Term

-- ANCHOR: value
/-- Values: the terms that are finished computing. -/
inductive Value : Term → Prop
  | lam {τ : Ty} {t : Term} : Value (.lam τ t)
  | tt : Value .tt
  | ff : Value .ff
  | lit {n : Nat} : Value (.lit n)
-- ANCHOR_END: value

-- ANCHOR: step
/-- One step of call-by-value evaluation. The *congruence* rules (`appL`, `appR`,
`ite`, `addL`, `addR`, `isZero`) say where to look for work; the *computation*
rules (`beta`, `iteTrue`, `iteFalse`, `addLit`, `isZeroZero`, `isZeroSucc`) do
the work. -/
inductive Step : Term → Term → Prop
  | appL {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | appR {v₁ t₂ t₂' : Term} :
      Value v₁ → Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')
  | beta {τ : Ty} {body v : Term} :
      Value v → Step (.app (.lam τ body) v) (instantiate body v)
  | ite {c c' t e : Term} :
      Step c c' → Step (.ite c t e) (.ite c' t e)
  | iteTrue {t e : Term} : Step (.ite .tt t e) t
  | iteFalse {t e : Term} : Step (.ite .ff t e) e
  | addL {t₁ t₁' t₂ : Term} :
      Step t₁ t₁' → Step (.add t₁ t₂) (.add t₁' t₂)
  | addR {v₁ t₂ t₂' : Term} :
      Value v₁ → Step t₂ t₂' → Step (.add v₁ t₂) (.add v₁ t₂')
  | addLit {m n : Nat} : Step (.add (.lit m) (.lit n)) (.lit (m + n))
  | isZero {t t' : Term} : Step t t' → Step (.isZero t) (.isZero t')
  | isZeroZero : Step (.isZero (.lit 0)) .tt
  | isZeroSucc {n : Nat} : Step (.isZero (.lit (n + 1))) .ff
-- ANCHOR_END: step

-- ANCHOR: steps
/-- Zero or more steps: the reflexive-transitive closure of `Step`. -/
inductive Steps : Term → Term → Prop
  | refl {t : Term} : Steps t t
  | step {t t' t'' : Term} : Step t t' → Steps t' t'' → Steps t t''
-- ANCHOR_END: steps

-- ANCHOR: steps_trans
/-- Two runs, one after the other, form a run. -/
theorem Steps.trans {t₁ t₂ t₃ : Term} (h₁₂ : Steps t₁ t₂) (h₂₃ : Steps t₂ t₃) :
    Steps t₁ t₃ := by
  induction h₁₂ with
  | refl => exact h₂₃
  | step hstep _ ih => exact .step hstep (ih h₂₃)
-- ANCHOR_END: steps_trans

-- ANCHOR: stuck
/-- A term is stuck when it is not a value and no rule applies to it. -/
def Stuck (t : Term) : Prop := ¬ Value t ∧ ∀ t', ¬ Step t t'
-- ANCHOR_END: stuck

/-! ## Evaluating a program by hand -/

-- ANCHOR: run_incr
/-- `(λ:nat. #0 + 1) 41` takes two steps to reach `42`. Each step is a rule
instance; `.step` chains them and `.refl` ends the run. -/
example : Steps incr41 (.lit 42) :=
  .step (.beta .lit)            -- (λ:nat. #0 + 1) 41  ⟶  41 + 1
    (.step .addLit              -- 41 + 1              ⟶  42
      .refl)
-- ANCHOR_END: run_incr

-- ANCHOR: stuck_example
/-- `true + 1` is stuck: it is not a value, and no rule has a conclusion of the
form `true + 1 ⟶ _`. -/
theorem stuck_example : Stuck (.add .tt (.lit 1)) := by
  constructor
  · -- Not a value: no constructor of `Value` builds an `add`.
    intro h
    cases h
  · -- No step: try every rule whose conclusion starts with `add`.
    intro t' h
    cases h with
    | addL h₁ => cases h₁    -- `true` would have to step: no rule for that
    | addR _ h₂ => cases h₂  -- `1` would have to step: no rule for that
-- ANCHOR_END: stuck_example

/-! ## Determinism -/

-- ANCHOR: value_no_step
/-- Values do not step: no rule has a value on its left-hand side. -/
theorem Value.no_step {v t : Term} (hv : Value v) : ¬ Step v t := by
  intro h
  cases hv <;> cases h
-- ANCHOR_END: value_no_step

-- ANCHOR: deterministic
-- ANCHOR: deterministic_head
/-- Evaluation is deterministic: a term has at most one next step. -/
theorem Step.deterministic {t t₁ t₂ : Term} (h₁ : Step t t₁) (h₂ : Step t t₂) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | appL h ih =>
    cases h₂ with
    | appL h' => rw [ih h']
    | appR hv _ => exact absurd h (hv.no_step)
    | beta _ => exact absurd h Value.lam.no_step
  | appR hv h ih =>
    cases h₂ with
    | appL h' => exact absurd h' hv.no_step
    | appR _ h' => rw [ih h']
    | beta hv' => exact absurd h hv'.no_step
  | beta hv =>
    cases h₂ with
    | appL h' => exact absurd h' Value.lam.no_step
    | appR _ h' => exact absurd h' hv.no_step
    | beta _ => rfl
  -- ANCHOR_END: deterministic_head
  | ite h ih =>
    cases h₂ with
    | ite h' => rw [ih h']
    | iteTrue => cases h
    | iteFalse => cases h
  | iteTrue => cases h₂ with
    | ite h' => cases h'
    | iteTrue => rfl
  | iteFalse => cases h₂ with
    | ite h' => cases h'
    | iteFalse => rfl
  | addL h ih =>
    cases h₂ with
    | addL h' => rw [ih h']
    | addR hv _ => exact absurd h hv.no_step
    | addLit => cases h
  | addR hv h ih =>
    cases h₂ with
    | addL h' => exact absurd h' hv.no_step
    | addR _ h' => rw [ih h']
    | addLit => cases h
  | addLit =>
    cases h₂ with
    | addL h' => cases h'
    | addR _ h' => cases h'
    | addLit => rfl
  | isZero h ih =>
    cases h₂ with
    | isZero h' => rw [ih h']
    | isZeroZero => cases h
    | isZeroSucc => cases h
  | isZeroZero =>
    cases h₂ with
    | isZero h' => cases h'
    | isZeroZero => rfl
  | isZeroSucc =>
    cases h₂ with
    | isZero h' => cases h'
    | isZeroSucc => rfl
-- ANCHOR_END: deterministic

-- ANCHOR: value_unique
/-- A consequence of determinism: a term evaluates to at most one value. -/
theorem Steps.value_unique {t v₁ v₂ : Term} (h₁ : Steps t v₁) (h₂ : Steps t v₂)
    (hv₁ : Value v₁) (hv₂ : Value v₂) : v₁ = v₂ := by
  induction h₁ with
  | refl =>
    -- t = v₁ is a value, so the run to v₂ must be empty.
    cases h₂ with
    | refl => rfl
    | step h _ => exact absurd h hv₁.no_step
  | step h _ ih =>
    cases h₂ with
    | refl => exact absurd h hv₂.no_step
    | step h' rest =>
      -- Both runs take a first step; by determinism it is the same step.
      rw [Step.deterministic h h'] at *
      exact ih rest hv₁
-- ANCHOR_END: value_unique

/-! ## In Mathlib -/

-- ANCHOR: refl_trans_gen
/-- Mathlib's `Relation.ReflTransGen r` is the reflexive-transitive closure of
any relation `r`. Its constructors add steps at the end of a run rather than at
the front, but it is the same relation as our `Steps`. -/
theorem steps_iff_reflTransGen {t t' : Term} :
    Steps t t' ↔ Relation.ReflTransGen Step t t' := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step hstep _ ih => exact Relation.ReflTransGen.head hstep ih
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hstep _ ih => exact .step hstep ih
-- ANCHOR_END: refl_trans_gen

end Ch09
