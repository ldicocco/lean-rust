import Book.Ch22.Syntax

/-!
# Chapter 22 · Typing with context splitting

Contexts with holes, the splitting relation `Split Γ Γ₁ Γ₂` (the text's
`Γ = Γ₁ ⊎ Γ₂`), the typing rules of `λ^aff` as an inductive relation, worked
derivations, a direct proof that `(z, z)` has no derivation, and weakening
proved admissible.
-/

namespace Ch22

-- ANCHOR: ctx
/-- A context: one entry per de Bruijn index. `some τ` is a variable of type
`τ` that the term may use; `none` is a hole, a variable that exists but is not
available to this part of the term (it was given to another part). -/
abbrev Ctx := List (Option Ty)
-- ANCHOR_END: ctx

-- ANCHOR: split
/-- `Split Γ Γ₁ Γ₂`: the context `Γ` is divided between `Γ₁` and `Γ₂`. Every
available variable of `Γ` goes to exactly one side and leaves a hole in the
other. Positions never move, so de Bruijn indices mean the same thing in all
three contexts. -/
inductive Split : Ctx → Ctx → Ctx → Prop where
  | nil : Split [] [] []
  | left {Γ Γ₁ Γ₂ : Ctx} {τ : Ty} :
      Split Γ Γ₁ Γ₂ → Split (some τ :: Γ) (some τ :: Γ₁) (none :: Γ₂)
  | right {Γ Γ₁ Γ₂ : Ctx} {τ : Ty} :
      Split Γ Γ₁ Γ₂ → Split (some τ :: Γ) (none :: Γ₁) (some τ :: Γ₂)
  | hole {Γ Γ₁ Γ₂ : Ctx} :
      Split Γ Γ₁ Γ₂ → Split (none :: Γ) (none :: Γ₁) (none :: Γ₂)
-- ANCHOR_END: split

-- ANCHOR: has_type
/-- The typing judgment `Γ ⊢ e : τ` of `λ^aff`. Every rule with two
subterms that both run splits the context; the additive rules (`wpair`, and the
two branches of `case`) share it. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {x : Nat} {τ : Ty} :
      Γ[x]? = some (some τ) →
      HasType Γ (.var x) τ
  | lam {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasType (some τ :: Γ) e σ →
      HasType Γ (.lam τ e) (τ ⊸ σ)
  | app {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      Split Γ Γ₁ Γ₂ →
      HasType Γ₁ e₁ (τ ⊸ σ) → HasType Γ₂ e₂ τ →
      HasType Γ (.app e₁ e₂) σ
  | unit {Γ : Ctx} :
      HasType Γ .unit .unit
  | pair {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      Split Γ Γ₁ Γ₂ →
      HasType Γ₁ e₁ τ → HasType Γ₂ e₂ σ →
      HasType Γ (.pair e₁ e₂) (τ ⊗ σ)
  | letPair {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ ρ : Ty} :
      Split Γ Γ₁ Γ₂ →
      HasType Γ₁ e₁ (τ ⊗ σ) → HasType (some σ :: some τ :: Γ₂) e₂ ρ →
      HasType Γ (.letPair e₁ e₂) ρ
  | wpair {Γ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      HasType Γ e₁ τ → HasType Γ e₂ σ →
      HasType Γ (.wpair e₁ e₂) (τ & σ)
  | fst {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasType Γ e (τ & σ) → HasType Γ (.fst e) τ
  | snd {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasType Γ e (τ & σ) → HasType Γ (.snd e) σ
  | inl {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasType Γ e τ → HasType Γ (.inl σ e) (τ ⊕ σ)
  | inr {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasType Γ e σ → HasType Γ (.inr τ e) (τ ⊕ σ)
  | case {Γ Γ₁ Γ₂ : Ctx} {e e₁ e₂ : Term} {τ σ ρ : Ty} :
      Split Γ Γ₁ Γ₂ →
      HasType Γ₁ e (τ ⊕ σ) →
      HasType (some τ :: Γ₂) e₁ ρ → HasType (some σ :: Γ₂) e₂ ρ →
      HasType Γ (.case e e₁ e₂) ρ
  | letIn {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      Split Γ Γ₁ Γ₂ →
      HasType Γ₁ e₁ τ → HasType (some τ :: Γ₂) e₂ σ →
      HasType Γ (.letIn e₁ e₂) σ
-- ANCHOR_END: has_type

-- ANCHOR: swap_typed
/-- Swap is typable: `⊢ λp. let (x, y) = p in (y, x) : (τ ⊗ σ) ⊸ (σ ⊗ τ)`. -/
theorem swap_typed (τ σ : Ty) : HasType [] (swap τ σ) ((τ ⊗ σ) ⊸ (σ ⊗ τ)) :=
  .lam                                  -- context: p
    (.letPair (.left .nil)              -- p goes to the `let`, nothing else
      (.var rfl)                        -- p : τ ⊗ σ
      (.pair (.left (.right (.hole .nil)))  -- y left, x right, p is a hole
        (.var rfl)                      -- y : σ
        (.var rfl)))                    -- x : τ
-- ANCHOR_END: swap_typed

-- ANCHOR: discard_typed
/-- Discarding is typable: `⊢ λx. λy. x : τ ⊸ σ ⊸ τ`. Rule `var` accepts the
unused `y` in the context: that is weakening. -/
theorem discard_typed (τ σ : Ty) : HasType [] (discard τ σ) (τ ⊸ σ ⊸ τ) :=
  .lam (.lam (.var rfl))
-- ANCHOR_END: discard_typed

-- ANCHOR: no_dup
/-- `(z, z)` has no type in a context where `z` is the variable 0, whatever the
rest of the context and whatever the type: rule `pair` must split the context,
and only one side receives `z`. -/
theorem no_pair_twice (Γ : Ctx) (τ ρ : Ty) :
    ¬ HasType (some τ :: Γ) (.pair (.var 0) (.var 0)) ρ := by
  intro h
  -- The only rule that concludes a pair is `pair`: it gives a split and two
  -- derivations, one for each component.
  cases h with
  | pair hs h₁ h₂ =>
    -- The only rule that concludes a variable is `var`: each side must have
    -- `some _` at position 0.
    cases h₁ with
    | var g₁ =>
      cases h₂ with
      | var g₂ =>
        -- The split puts position 0 on one side only; the other side has a
        -- hole there, which contradicts `g₁` or `g₂`.
        cases hs <;> simp at g₁ g₂
-- ANCHOR_END: no_dup

/-! ## Weakening is admissible -/

-- ANCHOR: wk
/-- `Wk Γ Γ'`: the context `Γ'` is `Γ` with some holes filled in by
variables. -/
inductive Wk : Ctx → Ctx → Prop where
  | nil : Wk [] []
  | keep {Γ Γ' : Ctx} {o : Option Ty} : Wk Γ Γ' → Wk (o :: Γ) (o :: Γ')
  | fill {Γ Γ' : Ctx} {τ : Ty} : Wk Γ Γ' → Wk (none :: Γ) (some τ :: Γ')
-- ANCHOR_END: wk

theorem Wk.refl : (Γ : Ctx) → Wk Γ Γ
  | [] => .nil
  | _ :: Γ => .keep (Wk.refl Γ)

theorem Wk.trans {Γ₁ Γ₂ Γ₃ : Ctx} (h₁ : Wk Γ₁ Γ₂) (h₂ : Wk Γ₂ Γ₃) : Wk Γ₁ Γ₃ := by
  induction h₁ generalizing Γ₃ with
  | nil => exact h₂
  | keep _ ih =>
    cases h₂ with
    | keep h₂ => exact .keep (ih h₂)
    | fill h₂ => exact .fill (ih h₂)
  | fill _ ih =>
    cases h₂ with
    | keep h₂ => exact .fill (ih h₂)

/-- A variable that is available in `Γ` is still available after weakening. -/
theorem Wk.get {Γ Γ' : Ctx} (hw : Wk Γ Γ') {x : Nat} {τ : Ty}
    (h : Γ[x]? = some (some τ)) : Γ'[x]? = some (some τ) := by
  induction hw generalizing x with
  | nil => simp at h
  | keep _ ih =>
    cases x with
    | zero => simpa using h
    | succ x => simpa using ih (by simpa using h)
  | fill _ ih =>
    cases x with
    | zero => simp at h
    | succ x => simpa using ih (by simpa using h)

-- ANCHOR: split_wk
/-- If `Γ` splits into `Γ₁` and `Γ₂`, and `Γ'` has more variables than `Γ`, then
`Γ'` splits into `Γ₂` and a weakening of `Γ₁`: the new variables go left. -/
theorem Split.wk {Γ Γ₁ Γ₂ Γ' : Ctx} (hs : Split Γ Γ₁ Γ₂) (hw : Wk Γ Γ') :
    ∃ Γ₁', Split Γ' Γ₁' Γ₂ ∧ Wk Γ₁ Γ₁' := by
  induction hs generalizing Γ' with
  | nil => cases hw; exact ⟨[], .nil, .nil⟩
  | left _ ih =>
    cases hw with
    | keep hw =>
      obtain ⟨Γ₁', hs', hw'⟩ := ih hw
      exact ⟨_, .left hs', .keep hw'⟩
  | right _ ih =>
    cases hw with
    | keep hw =>
      obtain ⟨Γ₁', hs', hw'⟩ := ih hw
      exact ⟨_, .right hs', .keep hw'⟩
  | hole _ ih =>
    cases hw with
    | keep hw =>
      obtain ⟨Γ₁', hs', hw'⟩ := ih hw
      exact ⟨_, .hole hs', .keep hw'⟩
    | fill hw =>
      obtain ⟨Γ₁', hs', hw'⟩ := ih hw
      exact ⟨_, .left hs', .fill hw'⟩
-- ANCHOR_END: split_wk

-- ANCHOR: weaken
/-- **Weakening is admissible**: a term that is well typed in `Γ` is well
typed in any context with more variables. -/
theorem weaken {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) :
    ∀ {Γ'}, Wk Γ Γ' → HasType Γ' e τ := by
  induction h with
  | var hx => intro _ hw; exact .var (hw.get hx)
  | lam _ ih => intro _ hw; exact .lam (ih (.keep hw))
  | unit => intro _ _; exact .unit
  | app hs _ h₂ ih₁ _ =>
    -- Split the bigger context so that the new variables go to e₁.
    intro _ hw
    obtain ⟨_, hs', hw'⟩ := hs.wk hw
    exact .app hs' (ih₁ hw') h₂
  | pair hs _ h₂ ih₁ _ =>
    intro _ hw
    obtain ⟨_, hs', hw'⟩ := hs.wk hw
    exact .pair hs' (ih₁ hw') h₂
  | letPair hs _ h₂ ih₁ _ =>
    intro _ hw
    obtain ⟨_, hs', hw'⟩ := hs.wk hw
    exact .letPair hs' (ih₁ hw') h₂
  | case hs _ h₁ h₂ ih _ _ =>
    intro _ hw
    obtain ⟨_, hs', hw'⟩ := hs.wk hw
    exact .case hs' (ih hw') h₁ h₂
  | letIn hs _ h₂ ih₁ _ =>
    intro _ hw
    obtain ⟨_, hs', hw'⟩ := hs.wk hw
    exact .letIn hs' (ih₁ hw') h₂
  | wpair _ _ ih₁ ih₂ => intro _ hw; exact .wpair (ih₁ hw) (ih₂ hw)
  | fst _ ih => intro _ hw; exact .fst (ih hw)
  | snd _ ih => intro _ hw; exact .snd (ih hw)
  | inl _ ih => intro _ hw; exact .inl (ih hw)
  | inr _ ih => intro _ hw; exact .inr (ih hw)
-- ANCHOR_END: weaken

end Ch22
