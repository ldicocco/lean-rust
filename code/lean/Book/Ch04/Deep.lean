/-!
# Chapter 4 · A deep embedding of natural deduction

Formulas as an inductive type, the hypothetical judgment `Γ ⊢ A` as an
inductive predicate `Proves`, derivations built by hand, truth tables, and the
soundness theorem: every derivable sequent is valid in every row of the truth
table. Consequences: consistency (no derivation of `⊥` from no assumptions)
and the underivability of some formulas.

Chapter 5 imports this file to prove soundness with respect to Kripke models.
-/

namespace Ch04

-- ANCHOR: formula
/-- Propositional formulas. Atoms are numbered: `var 0`, `var 1`, ... -/
inductive Formula where
  | var : Nat → Formula
  | top : Formula
  | bot : Formula
  | and : Formula → Formula → Formula
  | or  : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-- Negation is not a constructor: `¬A` abbreviates `A → ⊥`. -/
def Formula.neg (A : Formula) : Formula := .imp A .bot
-- ANCHOR_END: formula

-- ANCHOR: atoms
/-- Three atoms to write examples with. -/
def P : Formula := .var 0
def Q : Formula := .var 1
def R : Formula := .var 2
-- ANCHOR_END: atoms

-- ANCHOR: proves
/-- `Proves Γ A` is the hypothetical judgment `Γ ⊢ A` of intuitionistic natural
deduction, with one constructor per rule. The context is a list, and the newest
assumption is at its head: the `A :: Γ` of the code is the `Γ, A` of the text. -/
inductive Proves : List Formula → Formula → Prop where
  | hyp   {Γ A}     : A ∈ Γ → Proves Γ A
  | topI  {Γ}       : Proves Γ .top
  | botE  {Γ C}     : Proves Γ .bot → Proves Γ C
  | andI  {Γ A B}   : Proves Γ A → Proves Γ B → Proves Γ (.and A B)
  | andE1 {Γ A B}   : Proves Γ (.and A B) → Proves Γ A
  | andE2 {Γ A B}   : Proves Γ (.and A B) → Proves Γ B
  | orI1  {Γ A B}   : Proves Γ A → Proves Γ (.or A B)
  | orI2  {Γ A B}   : Proves Γ B → Proves Γ (.or A B)
  | orE   {Γ A B C} : Proves Γ (.or A B) → Proves (A :: Γ) C → Proves (B :: Γ) C →
                      Proves Γ C
  | impI  {Γ A B}   : Proves (A :: Γ) B → Proves Γ (.imp A B)
  | impE  {Γ A B}   : Proves Γ (.imp A B) → Proves Γ A → Proves Γ B
-- ANCHOR_END: proves

/-! ## Derivations as data -/

-- ANCHOR: and_comm_term
/-- The derivation of `P ∧ Q ⊢ Q ∧ P`, written as a term. Each `.hyp` needs a
proof that the formula is in the context; `List.Mem.head _` says "it is the
first element". -/
theorem and_comm_derivation : Proves [.and P Q] (.and Q P) :=
  .andI (.andE2 (.hyp (List.Mem.head _))) (.andE1 (.hyp (List.Mem.head _)))
-- ANCHOR_END: and_comm_term

-- ANCHOR: and_comm_tactic
/-- The same derivation under no assumptions, built bottom-up with `apply`.
Elimination rules have a formula in their premise that does not occur in their
conclusion (the `A` of ∧E₂ below), so we must supply it with `(A := P)`. -/
theorem and_comm_closed : Proves [] (.imp (.and P Q) (.and Q P)) := by
  apply Proves.impI           -- context is now [P ∧ Q]
  apply Proves.andI
  · apply Proves.andE2 (A := P)
    apply Proves.hyp
    simp                      -- P ∧ Q ∈ [P ∧ Q]
  · apply Proves.andE1 (B := Q)
    apply Proves.hyp
    simp
-- ANCHOR_END: and_comm_tactic

-- ANCHOR: or_map
/-- `⊢ (P → Q) → (P ∨ R) → (Q ∨ R)`: two →I, one ∨E, two ∨I, one →E. -/
theorem or_map_derivation : Proves [] (.imp (.imp P Q) (.imp (.or P R) (.or Q R))) := by
  apply Proves.impI                   -- assume P → Q
  apply Proves.impI                   -- assume P ∨ R
  apply Proves.orE (A := P) (B := R)  -- case analysis on P ∨ R
  · exact Proves.hyp (by simp)        -- the disjunction is an assumption
  · apply Proves.orI1                 -- case P: prove Q, then Q ∨ R
    apply Proves.impE (A := P)
    · exact Proves.hyp (by simp)      -- P → Q
    · exact Proves.hyp (by simp)      -- P
  · apply Proves.orI2                 -- case R: prove R, then Q ∨ R
    exact Proves.hyp (by simp)
-- ANCHOR_END: or_map

/-! ## Truth tables -/

-- ANCHOR: eval
/-- The truth-table value of a formula, given a value for every atom. -/
def eval (v : Nat → Bool) : Formula → Bool
  | .var n   => v n
  | .top     => true
  | .bot     => false
  | .and A B => eval v A && eval v B
  | .or A B  => eval v A || eval v B
  | .imp A B => !eval v A || eval v B
-- ANCHOR_END: eval

-- ANCHOR: valuations
/-- All valuations of the atoms `0, ..., n - 1` (the other atoms are `false`). -/
def valuations : Nat → List (Nat → Bool)
  | 0     => [fun _ => false]
  | n + 1 => (valuations n).flatMap fun v =>
      [v, fun k => if k = n then true else v k]

/-- A formula whose atoms are among `0, ..., n - 1` is a tautology when every
row of its truth table is `true`. -/
def isTautology (n : Nat) (A : Formula) : Bool :=
  (valuations n).all fun v => eval v A
-- ANCHOR_END: valuations

-- ANCHOR: taut_eval
/-- info: true -/
#guard_msgs in
#eval isTautology 2 (.imp (.imp P Q) (.imp (.or P R) (.or Q R)))

/-- info: false -/
#guard_msgs in
#eval isTautology 2 (.imp (.or P Q) P)

/-- info: true -/
#guard_msgs in
#eval isTautology 1 (.or P (.neg P))
-- ANCHOR_END: taut_eval

/-! ## Soundness -/

-- ANCHOR: soundness
/-- **Soundness.** If `Γ ⊢ A` is derivable, then every valuation that makes all
of `Γ` true makes `A` true. By induction on the derivation: one case per rule. -/
theorem soundness {Γ : List Formula} {A : Formula} (h : Proves Γ A) :
    ∀ v : Nat → Bool, (∀ B ∈ Γ, eval v B = true) → eval v A = true := by
  induction h with
  | hyp hmem =>
    -- The conclusion is one of the assumptions, which are all true.
    intro v hΓ
    exact hΓ _ hmem
  | topI =>
    intro v _
    rfl
  | botE _ ih =>
    -- The premise would make `false = true`: this case cannot happen.
    intro v hΓ
    have hbot := ih v hΓ
    simp [eval] at hbot
  | andI _ _ ih₁ ih₂ =>
    intro v hΓ
    simp [eval, ih₁ v hΓ, ih₂ v hΓ]
  | andE1 _ ih =>
    intro v hΓ
    have hand := ih v hΓ
    simp [eval] at hand
    exact hand.1
  | andE2 _ ih =>
    intro v hΓ
    have hand := ih v hΓ
    simp [eval] at hand
    exact hand.2
  | orI1 _ ih =>
    intro v hΓ
    simp [eval, ih v hΓ]
  | orI2 _ ih =>
    intro v hΓ
    simp [eval, ih v hΓ]
  | orE _ _ _ ih ihA ihB =>
    -- The disjunction is true, so one disjunct is; use the matching branch,
    -- whose context is Γ extended with that (true) disjunct.
    intro v hΓ
    have hor := ih v hΓ
    simp [eval] at hor
    rcases hor with hA | hB
    · apply ihA v
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hA
      · exact hΓ C hC
    · apply ihB v
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hB
      · exact hΓ C hC
  | @impI Γ A B _ ih =>
    -- If A is false the implication is true; if A is true, the premise
    -- (with A added to the context) gives B.
    intro v hΓ
    cases hA : eval v A with
    | false => simp [eval, hA]
    | true =>
      have hB : eval v B = true := by
        apply ih v
        intro C hC
        rcases List.mem_cons.mp hC with rfl | hC
        · exact hA
        · exact hΓ C hC
      simp [eval, hB]
  | impE _ _ ih₁ ih₂ =>
    intro v hΓ
    have himp := ih₁ v hΓ
    have hA := ih₂ v hΓ
    simp [eval, hA] at himp
    exact himp
-- ANCHOR_END: soundness

/-! ## Consequences -/

-- ANCHOR: consistency
/-- **Consistency.** `⊥` cannot be derived from no assumptions: under any
valuation, `eval v ⊥ = false`. -/
theorem consistency : ¬ Proves [] .bot := by
  intro h
  have := soundness h (fun _ => false) (by simp)
  simp [eval] at this
-- ANCHOR_END: consistency

-- ANCHOR: not_derivable
/-- An atom is not derivable: the valuation that makes every atom false is a
counterexample. -/
theorem atom_not_derivable : ¬ Proves [] P := by
  intro h
  have := soundness h (fun _ => false) (by simp)
  simp [eval, P] at this

/-- `(P ∨ Q) → P` is not derivable: take `P` false and `Q` true. -/
theorem or_imp_not_derivable : ¬ Proves [] (.imp (.or P Q) P) := by
  intro h
  have := soundness h (fun n => n = 1) (by simp)
  simp [eval, P, Q] at this
-- ANCHOR_END: not_derivable

-- ANCHOR: lem_tautology
/-- Excluded middle is a tautology: true in every row of its truth table. So
soundness alone cannot show that it is *not* derivable. (Chapter 5 shows it
with a Kripke model.) -/
theorem lem_tautology (v : Nat → Bool) : eval v (.or P (.neg P)) = true := by
  cases h : v 0 <;> simp [eval, Formula.neg, P, h]
-- ANCHOR_END: lem_tautology

end Ch04
