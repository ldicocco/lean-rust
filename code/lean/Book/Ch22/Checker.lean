import Book.Ch22.Usage

/-!
# Chapter 22 · An algorithmic checker with leftovers

The declarative rules guess how to split a context. The checker does not: it
threads the context through the term, from left to right. `infer Γ e` returns
the type of `e` and the **leftover** context, `Γ` with a hole in place of every
variable that `e` consumed. Soundness: whatever the checker accepts has a
derivation, and the consumed part of the context is exactly what the derivation
uses.
-/

namespace Ch22

-- ANCHOR: take
/-- Consume the variable `x`: return its type and the context with a hole at
`x`. Fails if `x` is a hole (already consumed) or does not exist. -/
def take : Ctx → Nat → Option (Ty × Ctx)
  | some τ :: Γ, 0 => some (τ, none :: Γ)
  | none :: _, 0 => none
  | o :: Γ, x + 1 =>
    match take Γ x with
    | some (τ, Δ) => some (τ, o :: Δ)
    | none => none
  | [], _ => none
-- ANCHOR_END: take

-- ANCHOR: meet
/-- What is left after two alternatives: a variable survives only if neither
alternative consumed it. -/
def meet : Ctx → Ctx → Ctx
  | some τ :: Γ, some _ :: Δ => some τ :: meet Γ Δ
  | _ :: Γ, _ :: Δ => none :: meet Γ Δ
  | _, _ => []
-- ANCHOR_END: meet

-- ANCHOR: infer
/-- The checker. `infer Γ e = some (τ, Δ)` means: `e` has type `τ`, and `Δ` is
what remains of `Γ` after `e` has consumed the variables it uses. -/
def infer : Ctx → Term → Option (Ty × Ctx)
  | Γ, .var x => take Γ x
  | Γ, .unit => some (.unit, Γ)
  | Γ, .lam τ e =>
    match infer (some τ :: Γ) e with
    | some (σ, _ :: Δ) => some (τ ⊸ σ, Δ)        -- the parameter leaves scope
    | _ => none
  | Γ, .app e₁ e₂ =>
    match infer Γ e₁ with
    | some (.lolli τ σ, Δ₁) =>
      match infer Δ₁ e₂ with                    -- e₂ gets the leftovers of e₁
      | some (τ', Δ₂) => if τ = τ' then some (σ, Δ₂) else none
      | none => none
    | _ => none
  | Γ, .pair e₁ e₂ =>
    match infer Γ e₁ with
    | some (τ, Δ₁) =>
      match infer Δ₁ e₂ with
      | some (σ, Δ₂) => some (τ ⊗ σ, Δ₂)
      | none => none
    | none => none
  | Γ, .letPair e₁ e₂ =>
    match infer Γ e₁ with
    | some (.tensor τ σ, Δ₁) =>
      match infer (some σ :: some τ :: Δ₁) e₂ with
      | some (ρ, _ :: _ :: Δ₂) => some (ρ, Δ₂)
      | _ => none
    | _ => none
  | Γ, .wpair e₁ e₂ =>
    match infer Γ e₁, infer Γ e₂ with           -- both start from Γ
    | some (τ, Δ₁), some (σ, Δ₂) => some (τ & σ, meet Δ₁ Δ₂)
    | _, _ => none
  | Γ, .fst e =>
    match infer Γ e with
    | some (.amp τ _, Δ) => some (τ, Δ)
    | _ => none
  | Γ, .snd e =>
    match infer Γ e with
    | some (.amp _ σ, Δ) => some (σ, Δ)
    | _ => none
  | Γ, .inl σ e =>
    match infer Γ e with
    | some (τ, Δ) => some (τ ⊕ σ, Δ)
    | none => none
  | Γ, .inr τ e =>
    match infer Γ e with
    | some (σ, Δ) => some (τ ⊕ σ, Δ)
    | none => none
  | Γ, .case e e₁ e₂ =>
    match infer Γ e with
    | some (.plus τ σ, Δ) =>
      match infer (some τ :: Δ) e₁, infer (some σ :: Δ) e₂ with
      | some (ρ₁, _ :: Δ₁), some (ρ₂, _ :: Δ₂) =>
        if ρ₁ = ρ₂ then some (ρ₁, meet Δ₁ Δ₂) else none
      | _, _ => none
    | _ => none
  | Γ, .letIn e₁ e₂ =>
    match infer Γ e₁ with
    | some (τ, Δ₁) =>
      match infer (some τ :: Δ₁) e₂ with
      | some (σ, _ :: Δ₂) => some (σ, Δ₂)
      | _ => none
    | none => none
-- ANCHOR_END: infer

-- ANCHOR: infer_eval
-- swap is accepted, in the empty context:
/-- info: some ((String ⊗ File) ⊸ (File ⊗ String), []) -/
#guard_msgs in
#eval infer [] (swap Str File)

-- dup is rejected:
/-- info: none -/
#guard_msgs in
#eval infer [] (dup Str)

-- Leftovers: with s : String (variable 1) and f : File (variable 0), the term
-- `s` consumes s and leaves f.
/-- info: some (String, [some File, none]) -/
#guard_msgs in
#eval infer [some File, some Str] (.var 1)

-- An additive pair whose components use different variables consumes both.
/-- info: some (File & String, [none, none]) -/
#guard_msgs in
#eval infer [some File, some Str] (.wpair (.var 0) (.var 1))
-- ANCHOR_END: infer_eval

/-! ## Lemmas about splitting -/

/-- Nothing can go to the right. -/
theorem Split.all_right : (Γ : Ctx) → Split Γ Γ.holes Γ
  | [] => .nil
  | none :: Γ => .hole (Split.all_right Γ)
  | some _ :: Γ => .right (Split.all_right Γ)

/-- The left part of a split is a part of the whole: filling its holes gives
back the whole. -/
theorem Split.wk_left {Γ Γ₁ Γ₂ : Ctx} (hs : Split Γ Γ₁ Γ₂) : Wk Γ₁ Γ := by
  induction hs with
  | nil => exact .nil
  | left _ ih => exact .keep ih
  | right _ ih => exact .fill ih
  | hole _ ih => exact .keep ih

-- ANCHOR: split_assoc
/-- Two successive splits are one split: if `Γ` gives `U₁` to `e₁` and keeps
`Δ₁`, and `Δ₁` gives `U₂` to `e₂` and keeps `Δ₂`, then `Γ` gives `U = U₁ ⊎ U₂`
to the pair and keeps `Δ₂`. -/
theorem Split.assoc {Γ U₁ Δ₁ U₂ Δ₂ : Ctx} (h₁ : Split Γ U₁ Δ₁) (h₂ : Split Δ₁ U₂ Δ₂) :
    ∃ U, Split Γ U Δ₂ ∧ Split U U₁ U₂ := by
  induction h₁ generalizing U₂ Δ₂ with
  | nil => cases h₂; exact ⟨[], .nil, .nil⟩
  | left _ ih =>
    cases h₂ with
    | hole h₂ =>
      obtain ⟨U, hU, hU'⟩ := ih h₂
      exact ⟨_, .left hU, .left hU'⟩
  | right _ ih =>
    cases h₂ with
    | left h₂ =>
      obtain ⟨U, hU, hU'⟩ := ih h₂
      exact ⟨_, .left hU, .right hU'⟩
    | right h₂ =>
      obtain ⟨U, hU, hU'⟩ := ih h₂
      exact ⟨_, .right hU, .hole hU'⟩
  | hole _ ih =>
    cases h₂ with
    | hole h₂ =>
      obtain ⟨U, hU, hU'⟩ := ih h₂
      exact ⟨_, .hole hU, .hole hU'⟩
-- ANCHOR_END: split_assoc

-- ANCHOR: split_meet
/-- Two alternatives that both start from `Γ`: the union of what they consume
is split off from `Γ`, leaving the meet of their leftovers. -/
theorem Split.meet {Γ U₁ Δ₁ U₂ Δ₂ : Ctx} (h₁ : Split Γ U₁ Δ₁) (h₂ : Split Γ U₂ Δ₂) :
    ∃ U, Split Γ U (meet Δ₁ Δ₂) ∧ Wk U₁ U ∧ Wk U₂ U := by
  induction h₁ generalizing U₂ Δ₂ with
  | nil => cases h₂; exact ⟨[], .nil, .nil, .nil⟩
  | left _ ih =>
    cases h₂ with
    | left h₂ =>
      obtain ⟨U, hU, w₁, w₂⟩ := ih h₂
      exact ⟨_, .left hU, .keep w₁, .keep w₂⟩
    | right h₂ =>
      obtain ⟨U, hU, w₁, w₂⟩ := ih h₂
      exact ⟨_, .left hU, .keep w₁, .fill w₂⟩
  | right _ ih =>
    cases h₂ with
    | left h₂ =>
      obtain ⟨U, hU, w₁, w₂⟩ := ih h₂
      exact ⟨_, .left hU, .fill w₁, .keep w₂⟩
    | right h₂ =>
      obtain ⟨U, hU, w₁, w₂⟩ := ih h₂
      exact ⟨_, .right hU, .keep w₁, .keep w₂⟩
  | hole _ ih =>
    cases h₂ with
    | hole h₂ =>
      obtain ⟨U, hU, w₁, w₂⟩ := ih h₂
      exact ⟨_, .hole hU, .keep w₁, .keep w₂⟩
-- ANCHOR_END: split_meet

/-- Peeling off a bound variable: if the extended context splits, the context
without the binder splits too, and the used part can be weakened so that the
binder is available. -/
theorem Split.uncons {Γ V Δ : Ctx} {τ : Ty} {o : Option Ty}
    (h : Split (some τ :: Γ) V (o :: Δ)) :
    ∃ V', Split Γ V' Δ ∧ Wk V (some τ :: V') := by
  cases h with
  | left h => exact ⟨_, h, .keep (Wk.refl _)⟩
  | right h => exact ⟨_, h, .fill (Wk.refl _)⟩

/-- What `take` consumes is a single variable. -/
theorem take_sound {Γ Δ : Ctx} {x : Nat} {τ : Ty} (h : take Γ x = some (τ, Δ)) :
    ∃ U, Split Γ U Δ ∧ U[x]? = some (some τ) := by
  induction Γ generalizing x Δ with
  | nil => simp [take] at h
  | cons o Γ ih =>
    cases x with
    | zero =>
      cases o with
      | none => simp [take] at h
      | some σ =>
        simp only [take, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨some σ :: Ctx.holes Γ, .left (Split.all_right Γ), rfl⟩
    | succ x =>
      simp only [take] at h
      split at h
      · rename_i σ Δ' hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨U, hU, hUx⟩ := ih hx
        cases o with
        | none => exact ⟨none :: U, .hole hU, by simpa using hUx⟩
        | some ρ => exact ⟨none :: U, .right hU, by simpa using hUx⟩
      · simp at h

-- ANCHOR: infer_sound
/-- **Soundness of the checker.** If `infer Γ e = some (τ, Δ)`, then `Γ` splits
into a used part `U` and the leftovers `Δ`, and `U ⊢ e : τ`. -/
theorem infer_sound (e : Term) :
    ∀ {Γ Δ : Ctx} {τ : Ty}, infer Γ e = some (τ, Δ) →
      ∃ U, Split Γ U Δ ∧ HasType U e τ := by
  induction e with
  | var x =>
    intro Γ Δ τ h
    obtain ⟨U, hs, hx⟩ := take_sound h
    exact ⟨U, hs, .var hx⟩
  | unit =>
    intro Γ Δ τ h
    simp only [infer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Γ.holes, Split.all_right Γ, .unit⟩
  | lam τ e ih =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i σ o Δ' he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The body was checked with the parameter in front of Γ.
      obtain ⟨V, hs, hv⟩ := ih he
      obtain ⟨V', hs', hw⟩ := hs.uncons
      exact ⟨V', hs', .lam (weaken hv hw)⟩
    · simp at h
  | app e₁ e₂ ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ σ Δ₁ h₁
      split at h
      · rename_i τ' Δ₂ h₂
        split at h
        · rename_i hτ
          subst hτ
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨U₁, hs₁, d₁⟩ := ih₁ h₁
          obtain ⟨U₂, hs₂, d₂⟩ := ih₂ h₂
          obtain ⟨U, hs, hU⟩ := hs₁.assoc hs₂
          exact ⟨U, hs, .app hU d₁ d₂⟩
        · simp at h
      · simp at h
    · simp at h
  | pair e₁ e₂ ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ Δ₁ h₁
      split at h
      · rename_i σ Δ₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨U₁, hs₁, d₁⟩ := ih₁ h₁
        obtain ⟨U₂, hs₂, d₂⟩ := ih₂ h₂
        obtain ⟨U, hs, hU⟩ := hs₁.assoc hs₂
        exact ⟨U, hs, .pair hU d₁ d₂⟩
      · simp at h
    · simp at h
  | letPair e₁ e₂ ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ σ Δ₁ h₁
      split at h
      · rename_i ρ' o o' Δ₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨U₁, hs₁, d₁⟩ := ih₁ h₁
        obtain ⟨V, hs₂, d₂⟩ := ih₂ h₂
        obtain ⟨V₁, hs₂', hw₁⟩ := hs₂.uncons
        obtain ⟨V₂, hs₂'', hw₂⟩ := hs₂'.uncons
        obtain ⟨U, hs, hU⟩ := hs₁.assoc hs₂''
        exact ⟨U, hs, .letPair hU d₁ (weaken d₂ (hw₁.trans (.keep hw₂)))⟩
      · simp at h
    · simp at h
  | wpair e₁ e₂ ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ Δ₁ σ Δ₂ h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨U₁, hs₁, d₁⟩ := ih₁ h₁
      obtain ⟨U₂, hs₂, d₂⟩ := ih₂ h₂
      obtain ⟨U, hs, w₁, w₂⟩ := hs₁.meet hs₂
      exact ⟨U, hs, .wpair (weaken d₁ w₁) (weaken d₂ w₂)⟩
    · simp at h
  | fst e ih =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ σ Δ' he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨U, hs, d⟩ := ih he
      exact ⟨U, hs, .fst d⟩
    · simp at h
  | snd e ih =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ σ Δ' he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨U, hs, d⟩ := ih he
      exact ⟨U, hs, .snd d⟩
    · simp at h
  | inl σ e ih =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ Δ' he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨U, hs, d⟩ := ih he
      exact ⟨U, hs, .inl d⟩
    · simp at h
  | inr τ e ih =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i σ Δ' he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨U, hs, d⟩ := ih he
      exact ⟨U, hs, .inr d⟩
    · simp at h
  | case e e₁ e₂ ih ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ σ Δ₀ he
      split at h
      · rename_i ρ₁ o₁ Δ₁ ρ₂ o₂ Δ₂ h₁ h₂
        split at h
        · rename_i hρ
          subst hρ
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨U, hs, d⟩ := ih he
          obtain ⟨V₁, hs₁, d₁⟩ := ih₁ h₁
          obtain ⟨V₂, hs₂, d₂⟩ := ih₂ h₂
          obtain ⟨V₁', hs₁', hw₁⟩ := hs₁.uncons
          obtain ⟨V₂', hs₂', hw₂⟩ := hs₂.uncons
          obtain ⟨W, hW, w₁, w₂⟩ := hs₁'.meet hs₂'
          obtain ⟨X, hX, hX'⟩ := hs.assoc hW
          exact ⟨X, hX, .case hX' d
            (weaken d₁ (hw₁.trans (.keep w₁)))
            (weaken d₂ (hw₂.trans (.keep w₂)))⟩
        · simp at h
      · simp at h
    · simp at h
  | letIn e₁ e₂ ih₁ ih₂ =>
    intro Γ Δ ρ h
    simp only [infer] at h
    split at h
    · rename_i τ Δ₁ h₁
      split at h
      · rename_i σ o Δ₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨U₁, hs₁, d₁⟩ := ih₁ h₁
        obtain ⟨V, hs₂, d₂⟩ := ih₂ h₂
        obtain ⟨V', hs₂', hw⟩ := hs₂.uncons
        obtain ⟨U, hs, hU⟩ := hs₁.assoc hs₂'
        exact ⟨U, hs, .letIn hU d₁ (weaken d₂ hw)⟩
      · simp at h
    · simp at h
-- ANCHOR_END: infer_sound

-- ANCHOR: infer_sound_cor
/-- In particular, whatever the checker accepts is well typed in the whole
context (the leftovers are discarded by weakening). -/
theorem infer_typed {Γ Δ : Ctx} {e : Term} {τ : Ty} (h : infer Γ e = some (τ, Δ)) :
    HasType Γ e τ := by
  obtain ⟨U, hs, d⟩ := infer_sound e h
  exact weaken d hs.wk_left

/-- And so the usage theorem applies to every term the checker accepts. -/
theorem infer_at_most_once {Γ Δ : Ctx} {e : Term} {τ : Ty}
    (h : infer Γ e = some (τ, Δ)) (i : Nat) : uses i e ≤ 1 :=
  at_most_once (infer_typed h) i
-- ANCHOR_END: infer_sound_cor

/-! ## Completeness -/

-- ANCHOR: consumed
/-- `consumed Γ f`: the context `Γ` with a hole at every position `i` such that
`f i > 0`. With `f i = uses i e` it is what remains of `Γ` after `e`. -/
def consumed : Ctx → (Nat → Nat) → Ctx
  | [], _ => []
  | o :: Γ, f => (if f 0 = 0 then o else none) :: consumed Γ (fun i => f (i + 1))
-- ANCHOR_END: consumed

theorem consumed_zero : (Γ : Ctx) → consumed Γ (fun _ => 0) = Γ
  | [] => rfl
  | o :: Γ => by simp [consumed, consumed_zero Γ]

theorem consumed_consumed :
    (Γ : Ctx) → (f g : Nat → Nat) →
      consumed (consumed Γ f) g = consumed Γ (fun i => f i + g i)
  | [], _, _ => rfl
  | o :: Γ, f, g => by
    simp only [consumed, consumed_consumed Γ]
    congr 1
    by_cases hf : f 0 = 0 <;> by_cases hg : g 0 = 0 <;> simp [hf, hg]

theorem meet_consumed :
    (Γ : Ctx) → (f g : Nat → Nat) →
      meet (consumed Γ f) (consumed Γ g) = consumed Γ (fun i => max (f i) (g i))
  | [], _, _ => rfl
  | o :: Γ, f, g => by
    simp only [consumed]
    rw [← meet_consumed Γ]
    cases o with
    | none => by_cases hf : f 0 = 0 <;> by_cases hg : g 0 = 0 <;> simp [meet, hf, hg]
    | some τ => by_cases hf : f 0 = 0 <;> by_cases hg : g 0 = 0 <;> simp [meet, hf, hg]

/-- Taking an available variable leaves a hole exactly there. -/
theorem take_of_get :
    (Γ : Ctx) → (x : Nat) → {τ : Ty} → Γ[x]? = some (some τ) →
      take Γ x = some (τ, consumed Γ (fun i => if i = x then 1 else 0))
  | [], _, _, h => by simp at h
  | some σ :: Γ, 0, τ, h => by
    simp at h
    subst h
    simp [take, consumed, consumed_zero]
  | none :: _, 0, _, h => by simp at h
  | o :: Γ, x + 1, τ, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [take, take_of_get Γ x h, consumed]
    simp

-- ANCHOR: wk_consumed
/-- If `U` splits into `U₁` and `U₂` and `Γ` has at least the variables of
`U`, then removing from `Γ` only variables of `U₁` leaves every variable of
`U₂` in place. -/
theorem Split.wk_consumed {U U₁ U₂ : Ctx} (hs : Split U U₁ U₂) :
    ∀ {Γ : Ctx} {f : Nat → Nat}, Wk U Γ → (∀ i, f i ≤ avail U₁ i) →
      Wk U₂ (consumed Γ f) := by
  induction hs with
  | nil => intro Γ f hw _; cases hw; exact .nil
  | left _ ih =>
    intro Γ f hw hf
    cases hw with
    | keep hw =>
      have := ih (f := fun i => f (i + 1)) hw (fun i => by simpa using hf (i + 1))
      simp only [consumed]
      split
      · exact .fill this
      · exact .keep this
  | right _ ih =>
    intro Γ f hw hf
    cases hw with
    | keep hw =>
      have h0 : f 0 = 0 := by simpa [avail] using hf 0
      have := ih (f := fun i => f (i + 1)) hw (fun i => by simpa using hf (i + 1))
      simp only [consumed, h0, ↓reduceIte]
      exact .keep this
  | hole _ ih =>
    intro Γ f hw hf
    cases hw with
    | keep hw =>
      have := ih (f := fun i => f (i + 1)) hw (fun i => by simpa using hf (i + 1))
      simp only [consumed]
      split <;> exact .keep this
    | fill hw =>
      have := ih (f := fun i => f (i + 1)) hw (fun i => by simpa using hf (i + 1))
      simp only [consumed]
      split
      · exact .fill this
      · exact .keep this
-- ANCHOR_END: wk_consumed

-- ANCHOR: infer_complete
/-- **Completeness of the checker.** If `U ⊢ e : τ` and the checker's context
`Γ` has at least the variables of `U`, the checker succeeds with the type `τ`,
and its leftovers are `Γ` minus exactly the variables that `e` uses. -/
theorem infer_complete {U : Ctx} {e : Term} {τ : Ty} (h : HasType U e τ) :
    ∀ {Γ : Ctx}, Wk U Γ → infer Γ e = some (τ, consumed Γ (fun i => uses i e)) := by
  induction h with
  | @var U x τ hx =>
    intro Γ hw
    simp only [infer, uses]
    exact take_of_get Γ x (hw.get hx)
  | unit =>
    intro Γ _
    simp [infer, uses, consumed_zero]
  | lam _ ih =>
    intro Γ hw
    have := ih (Wk.keep (o := some _) hw)
    simp only [infer, this, consumed]
    rfl
  | app hs d₁ _ ih₁ ih₂ =>
    intro Γ hw
    have h₁ := ih₁ (hs.wk_left.trans hw)
    have h₂ := ih₂ (hs.wk_consumed hw (usage d₁))
    simp only [infer, h₁, h₂, consumed_consumed, ↓reduceIte]
    rfl
  | pair hs d₁ _ ih₁ ih₂ =>
    intro Γ hw
    have h₁ := ih₁ (hs.wk_left.trans hw)
    have h₂ := ih₂ (hs.wk_consumed hw (usage d₁))
    simp only [infer, h₁, h₂, consumed_consumed]
    rfl
  | letPair hs d₁ _ ih₁ ih₂ =>
    intro Γ hw
    have h₁ := ih₁ (hs.wk_left.trans hw)
    have h₂ := ih₂ (Wk.keep (Wk.keep (hs.wk_consumed hw (usage d₁))))
    simp only [infer, h₁, h₂, consumed, consumed_consumed]
    rfl
  | letIn hs d₁ _ ih₁ ih₂ =>
    intro Γ hw
    have h₁ := ih₁ (hs.wk_left.trans hw)
    have h₂ := ih₂ (Wk.keep (hs.wk_consumed hw (usage d₁)))
    simp only [infer, h₁, h₂, consumed, consumed_consumed]
    rfl
  | wpair _ _ ih₁ ih₂ =>
    intro Γ hw
    simp only [infer, ih₁ hw, ih₂ hw, meet_consumed]
    rfl
  | fst _ ih =>
    intro Γ hw
    simp only [infer, ih hw]
    rfl
  | snd _ ih =>
    intro Γ hw
    simp only [infer, ih hw]
    rfl
  | inl _ ih =>
    intro Γ hw
    simp only [infer, ih hw]
    rfl
  | inr _ ih =>
    intro Γ hw
    simp only [infer, ih hw]
    rfl
  | case hs d _ _ ih ih₁ ih₂ =>
    intro Γ hw
    have h := ih (hs.wk_left.trans hw)
    have hw₂ := hs.wk_consumed hw (usage d)
    have h₁ := ih₁ (Wk.keep hw₂)
    have h₂ := ih₂ (Wk.keep hw₂)
    simp only [infer, h, h₁, h₂, consumed, ↓reduceIte, meet_consumed, consumed_consumed]
    -- Left: max (u + v₁) (u + v₂); right: u + max v₁ v₂. Equal, by arithmetic.
    congr 2
    apply congrArg
    funext i
    simp only [uses]
    omega
-- ANCHOR_END: infer_complete

-- ANCHOR: decides
/-- Together: the checker decides typability in a context. -/
theorem infer_iff {Γ : Ctx} {e : Term} {τ : Ty} :
    HasType Γ e τ ↔ ∃ Δ, infer Γ e = some (τ, Δ) := by
  constructor
  · intro h
    exact ⟨_, infer_complete h (Wk.refl Γ)⟩
  · intro ⟨Δ, h⟩
    exact infer_typed h
-- ANCHOR_END: decides

/-! ## Putting it together: the upload -/

-- ANCHOR: upload
def Conn : Ty := .base "Conn"

/-- The context of the upload: the two resources and the three functions of the
environment. Index 0 is the innermost entry. -/
def uploadCtx : Ctx :=
  [ some File                       -- 0  file
  , some Conn                       -- 1  conn
  , some (File ⊸ .unit)             -- 2  close_file
  , some (Conn ⊸ Str ⊸ Conn)        -- 3  send (curried)
  , some (File ⊸ Str ⊗ File) ]      -- 4  read_all

/-- `let (data, opened) = read_all file in let sent = send conn data in`
`let _ = close_file opened in sent`. Under the `letPair`, `opened` is 0 and
`data` is 1; under the first `letIn`, `sent` is 0; under the second, `sent` is 1. -/
def upload : Term :=
  .letPair (.app (.var 4) (.var 0))
    (.letIn (.app (.app (.var 5) (.var 3)) (.var 1))
      (.letIn (.app (.var 5) (.var 1))
        (.var 1)))

/-- The same without `close_file opened`. -/
def uploadLeaky : Term :=
  .letPair (.app (.var 4) (.var 0))
    (.app (.app (.var 5) (.var 3)) (.var 1))
-- ANCHOR_END: upload

-- ANCHOR: upload_eval
-- Everything is consumed:
/-- info: some (Conn, [none, none, none, none, none]) -/
#guard_msgs in
#eval infer uploadCtx upload

-- The leaky version is accepted too; `close_file` is left over, unused.
/-- info: some (Conn, [none, none, some (File ⊸ 𝟏), none, none]) -/
#guard_msgs in
#eval infer uploadCtx uploadLeaky

/-- The checker's answer is a proof: `upload` is well typed. -/
theorem upload_typed : HasType uploadCtx upload Conn :=
  infer_iff.mpr ⟨_, rfl⟩
-- ANCHOR_END: upload_eval

end Ch22
