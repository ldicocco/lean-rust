import Book.Ch09.Typing

/-!
# Chapter 9 · Safety

Progress, preservation and their corollary, type safety: a closed well-typed
term never reaches a stuck state, however many steps it takes. Then a broken
typing rule, and a formal proof that it breaks safety.
-/

namespace Ch09

-- ANCHOR: progress
/-- Progress: a closed, well-typed term is a value or can take a step. -/
theorem progress {t : Term} {τ : Ty} (ht : HasType [] t τ) :
    Value t ∨ ∃ t', Step t t' := by
  -- Induction on the derivation. The context is `[]` in every case, so Lean
  -- needs to remember that: `generalize` names it `Γ` with `hΓ : [] = Γ`.
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var h =>
    -- A variable in the empty context. `h : lookup [] i = some τ` computes to
    -- `none = some τ`, which no constructor of `=` can prove.
    subst hΓ
    cases h
  | lam _ _ => left; exact .lam
  | @app _ σ τ t₁ t₂ ht₁ _ ih₁ ih₂ =>
    right
    rcases ih₁ hΓ with hv₁ | ⟨t₁', h₁⟩
    · rcases ih₂ hΓ with hv₂ | ⟨t₂', h₂⟩
      · -- Both are values: by canonical forms, t₁ is a λ, and β applies.
        subst hΓ
        obtain ⟨body, rfl⟩ := canonical_arrow hv₁ ht₁
        exact ⟨_, .beta hv₂⟩
      · exact ⟨_, .appR hv₁ h₂⟩     -- t₁ is a value, t₂ steps
    · exact ⟨_, .appL h₁⟩           -- t₁ steps
  | tt => left; exact .tt
  | ff => left; exact .ff
  | @ite _ τ c t e hc _ _ ihc _ _ =>
    right
    rcases ihc hΓ with hvc | ⟨c', hc'⟩
    · -- The condition is a value of type bool: `tt` or `ff`.
      subst hΓ
      rcases canonical_bool hvc hc with rfl | rfl
      · exact ⟨_, .iteTrue⟩
      · exact ⟨_, .iteFalse⟩
    · exact ⟨_, .ite hc'⟩
  | lit => left; exact .lit
  | @add _ t₁ t₂ ht₁ ht₂ ih₁ ih₂ =>
    right
    rcases ih₁ hΓ with hv₁ | ⟨t₁', h₁⟩
    · rcases ih₂ hΓ with hv₂ | ⟨t₂', h₂⟩
      · -- Two values of type nat: two literals, and `addLit` applies.
        subst hΓ
        obtain ⟨m, rfl⟩ := canonical_nat hv₁ ht₁
        obtain ⟨n, rfl⟩ := canonical_nat hv₂ ht₂
        exact ⟨_, .addLit⟩
      · exact ⟨_, .addR hv₁ h₂⟩
    · exact ⟨_, .addL h₁⟩
  | @isZero _ t ht' ih =>
    right
    rcases ih hΓ with hv | ⟨t', h⟩
    · subst hΓ
      obtain ⟨n, rfl⟩ := canonical_nat hv ht'
      cases n with
      | zero => exact ⟨_, .isZeroZero⟩
      | succ n => exact ⟨_, .isZeroSucc⟩
    · exact ⟨_, .isZero h⟩
-- ANCHOR_END: progress

-- ANCHOR: preservation
/-- Preservation: a step does not change the type of a term. -/
theorem preservation {Γ : Ctx} {t t' : Term} {τ : Ty}
    (ht : HasType Γ t τ) (hstep : Step t t') : HasType Γ t' τ := by
  -- Induction on the step; in each case, take the typing derivation apart.
  induction hstep generalizing τ with
  | appL _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app (ih ht₁) ht₂
  | appR _ _ ih =>
    cases ht with
    | app ht₁ ht₂ => exact .app ht₁ (ih ht₂)
  | beta _ =>
    -- ht : HasType Γ (app (lam σ body) v) τ. Take it apart twice:
    cases ht with
    | app hlam hv =>
      cases hlam with
      | lam hbody =>
        -- hbody : HasType (σ :: Γ) body τ,  hv : HasType Γ v σ
        exact instantiate_typing hbody hv
  | ite _ ih =>
    cases ht with
    | ite hc ht₁ ht₂ => exact .ite (ih hc) ht₁ ht₂
  | iteTrue =>
    cases ht with
    | ite _ ht₁ _ => exact ht₁
  | iteFalse =>
    cases ht with
    | ite _ _ ht₂ => exact ht₂
  | addL _ ih =>
    cases ht with
    | add ht₁ ht₂ => exact .add (ih ht₁) ht₂
  | addR _ _ ih =>
    cases ht with
    | add ht₁ ht₂ => exact .add ht₁ (ih ht₂)
  | addLit =>
    cases ht
    exact .lit
  | isZero _ ih =>
    cases ht with
    | isZero ht' => exact .isZero (ih ht')
  | isZeroZero =>
    cases ht
    exact .tt
  | isZeroSucc =>
    cases ht
    exact .ff
-- ANCHOR_END: preservation

-- ANCHOR: safety
/-- Preservation for runs of any length. -/
theorem preservation_steps {t t' : Term} {τ : Ty}
    (ht : HasType [] t τ) (hsteps : Steps t t') : HasType [] t' τ := by
  induction hsteps with
  | refl => exact ht
  | step hstep _ ih => exact ih (preservation ht hstep)

/-- Type safety: a closed well-typed term never reaches a stuck state. -/
theorem safety {t t' : Term} {τ : Ty}
    (ht : HasType [] t τ) (hsteps : Steps t t') : ¬ Stuck t' := by
  intro ⟨hnotval, hnostep⟩
  -- t' is still well typed, so progress applies to it.
  rcases progress (preservation_steps ht hsteps) with hv | ⟨t'', h⟩
  · exact hnotval hv
  · exact hnostep t'' h
-- ANCHOR_END: safety

-- ANCHOR: safety_corollary
/-- For example: the program `(λ:nat. #0 + 1) 41` never gets stuck, whatever
it reduces to. The typing derivation comes from the checker. -/
theorem incr41_safe {t' : Term} (h : Steps incr41 t') : ¬ Stuck t' :=
  safety incr41_typed h
-- ANCHOR_END: safety_corollary

/-! ## Putting it together -/

-- ANCHOR: program
/-- `λ (x : nat). x + 2` -/
def addTwo : Term := .lam .nat (.add (.var 0) (.lit 2))

/-- `twice (λ (x : nat). x + 2) 3` -/
def program : Term := .app (.app twice addTwo) (.lit 3)

/-- info: (λ:(nat → nat). λ:nat. #1 (#1 #0)) (λ:nat. #0 + 2) 3 -/
#guard_msgs in
#eval program

theorem program_typed : HasType [] program .nat := typeOf_sound rfl
-- ANCHOR_END: program

-- ANCHOR: program_runs
/-- The run of `program`, one rule instance per step. Lean computes each
intermediate term itself (by unfolding `instantiate`), and checks that the
rules apply. -/
theorem program_runs : Steps program (.lit 7) :=
  .step (.appL (.beta .lam)) <|   -- twice addTwo 3  ⟶  (λ:nat. addTwo (addTwo #0)) 3
  .step (.beta .lit) <|           --                 ⟶  addTwo (addTwo 3)
  .step (.appR .lam (.beta .lit)) <| --              ⟶  addTwo (3 + 2)
  .step (.appR .lam .addLit) <|   --                 ⟶  addTwo 5
  .step (.beta .lit) <|           --                 ⟶  5 + 2
  .step .addLit <|                --                 ⟶  7
  .refl

/-- Safety and determinism together: `program` never gets stuck, and `7` is the
only value it can produce. -/
theorem program_result {v : Term} (h : Steps program v) (hv : Value v) :
    v = .lit 7 :=
  Steps.value_unique h program_runs hv .lit
-- ANCHOR_END: program_runs

/-! ## What a proof needs: a broken rule -/

-- ANCHOR: bad_typing
/-- A *broken* type system: identical to `HasType`, except that the rule for
`if` only looks at the `then` branch. -/
inductive BadHasType : Ctx → Term → Ty → Prop
  | var {Γ : Ctx} {i : Nat} {τ : Ty} :
      lookup Γ i = some τ → BadHasType Γ (.var i) τ
  | lam {Γ : Ctx} {σ τ : Ty} {t : Term} :
      BadHasType (σ :: Γ) t τ → BadHasType Γ (.lam σ t) (.arrow σ τ)
  | app {Γ : Ctx} {σ τ : Ty} {t₁ t₂ : Term} :
      BadHasType Γ t₁ (.arrow σ τ) → BadHasType Γ t₂ σ →
      BadHasType Γ (.app t₁ t₂) τ
  | tt {Γ : Ctx} : BadHasType Γ .tt .bool
  | ff {Γ : Ctx} : BadHasType Γ .ff .bool
  | ite {Γ : Ctx} {τ τ' : Ty} {c t e : Term} :          -- τ' is ignored!
      BadHasType Γ c .bool → BadHasType Γ t τ → BadHasType Γ e τ' →
      BadHasType Γ (.ite c t e) τ
  | lit {Γ : Ctx} {n : Nat} : BadHasType Γ (.lit n) .nat
  | add {Γ : Ctx} {t₁ t₂ : Term} :
      BadHasType Γ t₁ .nat → BadHasType Γ t₂ .nat →
      BadHasType Γ (.add t₁ t₂) .nat
  | isZero {Γ : Ctx} {t : Term} :
      BadHasType Γ t .nat → BadHasType Γ (.isZero t) .bool
-- ANCHOR_END: bad_typing

-- ANCHOR: bad_unsafe
/-- The broken system is not safe: `(if false then 1 else true) + 2` is
"well typed" in it, and after one step it is stuck. -/
theorem bad_typing_unsafe :
    ∃ t t' τ, BadHasType [] t τ ∧ Steps t t' ∧ Stuck t' := by
  refine ⟨.add (.ite .ff (.lit 1) .tt) (.lit 2),   -- the program
          .add .tt (.lit 2),                         -- where it ends up
          .nat, ?_, ?_, ?_⟩
  · -- "Well typed": the `then` branch is a nat, the `else` branch is ignored.
    exact .add (.ite .ff .lit .tt) .lit
  · -- One step: the `if` reduces to its `else` branch.
    exact .step (.addL .iteFalse) .refl
  · -- `true + 2` is stuck, for the same reason as `true + 1`.
    constructor
    · intro h; cases h
    · intro t'' h
      cases h with
      | addL h₁ => cases h₁
      | addR _ h₂ => cases h₂
-- ANCHOR_END: bad_unsafe

-- ANCHOR: axioms
/-- info: 'Ch09.safety' does not depend on any axioms -/
#guard_msgs in
#print axioms safety
-- ANCHOR_END: axioms

end Ch09
