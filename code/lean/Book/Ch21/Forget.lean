import Book.Ch06.Structural
import Book.Ch21.Linear

/-!
# Chapter 21 · Forgetting resources

Every linear derivation becomes an intuitionistic one when we forget the
difference between the two conjunctions (`⊗` and `&` both become `∧`), read
`⊸` as `→`, `⊕` as `∨`, `1` and `⊤` as `⊤`, and `0` as `⊥`. The translation
uses the admissible structural rules of Chapter 6 (imported here): linear
logic proves *fewer* sequents, never different ones. The converse fails:
`A ⊢ A ∧ A` is intuitionistically derivable, `A ⊢ A ⊗ A` is not.
-/

namespace Ch21

open Formula

-- ANCHOR: forget
/-- Forget resources: translate a linear formula into Chapter 6's formulas. -/
def Formula.forget : Formula → Ch06.Formula
  | atom a => .atom a
  | one => .top
  | top => .top
  | zero => .bot
  | A ⊗ B => .conj A.forget B.forget
  | .with A B => .conj A.forget B.forget
  | plus A B => .disj A.forget B.forget
  | A ⊸ B => .imp A.forget B.forget
-- ANCHOR_END: forget

section Lemmas

open Ch06 (Proves weakening)

variable {Γ : List Ch06.Formula} {A B C : Ch06.Formula}

-- ANCHOR: left_rules
/-- Using a conjunction on the left, the intuitionistic way: discharge both
components with `→I`, weaken, and apply to the two projections. -/
theorem conj_left (h : Proves (A :: B :: Γ) C) : Proves (.conj A B :: Γ) C :=
  .impE (.impE (weakening (.impI (.impI h))) (.conjE₂ (.hyp List.mem_cons_self)))
    (.conjE₁ (.hyp List.mem_cons_self))

/-- The same, keeping only the first component. -/
theorem conj_left₁ (h : Proves (A :: Γ) C) : Proves (.conj A B :: Γ) C :=
  .impE (weakening (.impI h)) (.conjE₁ (.hyp List.mem_cons_self))

/-- The same, keeping only the second component. -/
theorem conj_left₂ (h : Proves (B :: Γ) C) : Proves (.conj A B :: Γ) C :=
  .impE (weakening (.impI h)) (.conjE₂ (.hyp List.mem_cons_self))
-- ANCHOR_END: left_rules

end Lemmas

-- ANCHOR: forget_sound
/-- Every linear derivation, with resources forgotten, is an intuitionistic
derivation. -/
theorem LProves.forget {Γ : List Formula} {C : Formula} (h : Γ ⊢ C) :
    Ch06.Proves (Γ.map Formula.forget) C.forget := by
  induction h with
  | ax A => exact .hyp List.mem_cons_self
  | exch p _ ih =>
    -- Exchange: the translated contexts have the same elements.
    exact ih.mono (p.map _).subset
  | oneR => exact .topI
  | oneL _ ih => exact Ch06.weakening ih
  | topR => exact .topI
  | zeroL => exact .botE (.hyp List.mem_cons_self)
  | tensorR _ _ ih₁ ih₂ =>
    -- Splitting becomes sharing: each half is weakened to the whole context.
    rw [List.map_append]
    exact .conjI (ih₁.mono (List.subset_append_left _ _))
      (ih₂.mono (List.subset_append_right _ _))
  | tensorL _ ih => exact conj_left ih
  | withR _ _ ih₁ ih₂ => exact .conjI ih₁ ih₂
  | withL₁ _ ih => exact conj_left₁ ih
  | withL₂ _ ih => exact conj_left₂ ih
  | plusR₁ _ ih => exact .disjI₁ ih
  | plusR₂ _ ih => exact .disjI₂ ih
  | plusL _ _ ih₁ ih₂ =>
    exact .disjE (.hyp List.mem_cons_self)
      (ih₁.mono (List.cons_subset_cons _ (List.subset_cons_self _ _)))
      (ih₂.mono (List.cons_subset_cons _ (List.subset_cons_self _ _)))
  | lolliR _ ih => exact .impI ih
  | lolliL _ _ ih₁ ih₂ =>
    -- Apply the implication (first in the context) to a proof of its
    -- argument, then use the result as the hypothesis of the second premise.
    rw [List.map_cons, List.map_append]
    refine .impE (Ch06.weakening (.impI (ih₂.mono ?_)))
      (.impE (.hyp List.mem_cons_self) ?_)
    · exact List.cons_subset_cons _ (List.subset_append_right _ _)
    · exact ih₁.mono (List.subset_cons_of_subset _ (List.subset_append_left _ _))
-- ANCHOR_END: forget_sound

-- ANCHOR: converse_fails
/-- The converse fails: intuitionistic logic duplicates what linear logic
cannot. -/
example (a : String) :
    Ch06.Proves [(atom a).forget] ((atom a ⊗ atom a).forget) ∧
      ¬ ([atom a] ⊢ atom a ⊗ atom a) :=
  ⟨.conjI (.hyp List.mem_cons_self) (.hyp List.mem_cons_self), not_proves_dup a⟩
-- ANCHOR_END: converse_fails

end Ch21
