import Book.Ch09.Semantics

/-!
# Chapter 9 · Typing

The typing judgment `HasType Γ t τ` as an inductive predicate, a type checker
proved sound, the canonical forms lemmas, and the two structural lemmas of the
metatheory: renaming (which contains weakening) and substitution.
-/

namespace Ch09

-- ANCHOR: ctx
/-- A context lists the types of the free variables: entry `i` is the type of
`var i`. The most recently bound variable comes first. -/
abbrev Ctx := List Ty

/-- The type of variable `i` in `Γ`, if `Γ` has an entry `i`. -/
def lookup : Ctx → Nat → Option Ty
  | [], _ => none
  | σ :: _, 0 => some σ
  | _ :: Γ, i + 1 => lookup Γ i
-- ANCHOR_END: ctx

-- ANCHOR: has_type
/-- `HasType Γ t τ`: in context `Γ`, the term `t` has type `τ`. -/
inductive HasType : Ctx → Term → Ty → Prop
  | var {Γ : Ctx} {i : Nat} {τ : Ty} :
      lookup Γ i = some τ → HasType Γ (.var i) τ
  | lam {Γ : Ctx} {σ τ : Ty} {t : Term} :
      HasType (σ :: Γ) t τ → HasType Γ (.lam σ t) (.arrow σ τ)
  | app {Γ : Ctx} {σ τ : Ty} {t₁ t₂ : Term} :
      HasType Γ t₁ (.arrow σ τ) → HasType Γ t₂ σ → HasType Γ (.app t₁ t₂) τ
  | tt {Γ : Ctx} : HasType Γ .tt .bool
  | ff {Γ : Ctx} : HasType Γ .ff .bool
  | ite {Γ : Ctx} {τ : Ty} {c t e : Term} :
      HasType Γ c .bool → HasType Γ t τ → HasType Γ e τ →
      HasType Γ (.ite c t e) τ
  | lit {Γ : Ctx} {n : Nat} : HasType Γ (.lit n) .nat
  | add {Γ : Ctx} {t₁ t₂ : Term} :
      HasType Γ t₁ .nat → HasType Γ t₂ .nat → HasType Γ (.add t₁ t₂) .nat
  | isZero {Γ : Ctx} {t : Term} :
      HasType Γ t .nat → HasType Γ (.isZero t) .bool
-- ANCHOR_END: has_type

-- ANCHOR: twice_typed
/-- A derivation, built by hand: `twice` has type `(nat → nat) → nat → nat`.
Read the proof term from the outside in: two `lam` rules, then the outer
application, whose function is `#1` and whose argument is another application. -/
example : HasType [] twice (.arrow (.arrow .nat .nat) (.arrow .nat .nat)) :=
  .lam (.lam
    (.app (.var rfl)                          -- #1 : nat → nat
      (.app (.var rfl) (.var rfl))))          -- #1 #0 : nat
-- ANCHOR_END: twice_typed

/-! ## A type checker -/

-- ANCHOR: type_of
/-- The type checker: `some τ` if the term has type `τ`, `none` if it has no
type. -/
def typeOf (Γ : Ctx) : Term → Option Ty
  | .var i => lookup Γ i
  | .lam σ t =>
    match typeOf (σ :: Γ) t with
    | some τ => some (.arrow σ τ)
    | none => none
  | .app t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | some (.arrow σ τ), some σ' => if σ = σ' then some τ else none
    | _, _ => none
  | .tt => some .bool
  | .ff => some .bool
  | .ite c t e =>
    match typeOf Γ c, typeOf Γ t, typeOf Γ e with
    | some .bool, some τ, some τ' => if τ = τ' then some τ else none
    | _, _, _ => none
  | .lit _ => some .nat
  | .add t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | some .nat, some .nat => some .nat
    | _, _ => none
  | .isZero t =>
    match typeOf Γ t with
    | some .nat => some .bool
    | _ => none
-- ANCHOR_END: type_of

-- ANCHOR: type_of_eval
/-- info: some ((nat → nat) → nat → nat) -/
#guard_msgs in
#eval typeOf [] twice

/-- info: none -/
#guard_msgs in
#eval typeOf [] (.add .tt (.lit 1))
-- ANCHOR_END: type_of_eval

-- ANCHOR: type_of_sound
-- ANCHOR: type_of_sound_head
/-- The checker is sound: when it answers `some τ`, a derivation exists. -/
theorem typeOf_sound {Γ : Ctx} {t : Term} {τ : Ty} :
    typeOf Γ t = some τ → HasType Γ t τ := by
  induction t generalizing Γ τ with
  | var i => intro h; exact .var h
  | lam σ t ih =>
    intro h
    simp only [typeOf] at h
    split at h
    · next τ' h' => cases h; exact .lam (ih h')
    · cases h
  | app t₁ t₂ ih₁ ih₂ =>
    intro h
    simp only [typeOf] at h
    split at h
    · next σ τ' σ' h₁ h₂ =>
      split at h
      · next hσ => cases h; subst hσ; exact .app (ih₁ h₁) (ih₂ h₂)
      · cases h
    · cases h
  -- ANCHOR_END: type_of_sound_head
  | tt => intro h; cases h; exact .tt
  | ff => intro h; cases h; exact .ff
  | ite c t e ihc iht ihe =>
    intro h
    simp only [typeOf] at h
    split at h
    · next τ₁ τ₂ hc ht he =>
      split at h
      · next heq => cases h; subst heq; exact .ite (ihc hc) (iht ht) (ihe he)
      · cases h
    · cases h
  | lit n => intro h; cases h; exact .lit
  | add t₁ t₂ ih₁ ih₂ =>
    intro h
    simp only [typeOf] at h
    split at h
    · next h₁ h₂ => cases h; exact .add (ih₁ h₁) (ih₂ h₂)
    · cases h
  | isZero t ih =>
    intro h
    simp only [typeOf] at h
    split at h
    · next h₁ => cases h; exact .isZero (ih h₁)
    · cases h
-- ANCHOR_END: type_of_sound

-- ANCHOR: incr41_typed
/-- With a sound checker, a derivation for a concrete program is a computation:
`rfl` checks that the checker says `some nat`. -/
theorem incr41_typed : HasType [] incr41 .nat := typeOf_sound rfl
-- ANCHOR_END: incr41_typed

/-! ## Canonical forms -/

-- ANCHOR: canonical
/-- A value of type `bool` is `tt` or `ff`. -/
theorem canonical_bool {v : Term} (hv : Value v) (ht : HasType [] v .bool) :
    v = .tt ∨ v = .ff := by
  cases hv with
  | lam => cases ht        -- a λ has an arrow type, not bool
  | tt => left; rfl
  | ff => right; rfl
  | lit => cases ht        -- a literal has type nat, not bool

/-- A value of type `nat` is a literal. -/
theorem canonical_nat {v : Term} (hv : Value v) (ht : HasType [] v .nat) :
    ∃ n, v = .lit n := by
  cases hv with
  | lit => exact ⟨_, rfl⟩
  | _ => cases ht          -- every other value has a different type

/-- A value of type `σ → τ` is a λ whose parameter has type `σ`. -/
theorem canonical_arrow {v : Term} {σ τ : Ty} (hv : Value v)
    (ht : HasType [] v (.arrow σ τ)) : ∃ body, v = .lam σ body := by
  cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | _ => cases ht
-- ANCHOR_END: canonical

/-! ## Renaming and weakening -/

-- ANCHOR: rename_typing
/-- Renaming preserves types, provided the renaming respects the contexts:
whenever `Γ` gives variable `i` type `τ`, `Δ` gives `ρ i` the same type. -/
theorem rename_typing {Γ Δ : Ctx} {ρ : Nat → Nat} {t : Term} {τ : Ty}
    (hρ : ∀ i τ, lookup Γ i = some τ → lookup Δ (ρ i) = some τ)
    (ht : HasType Γ t τ) : HasType Δ (rename ρ t) τ := by
  induction ht generalizing Δ ρ with
  | var h => exact .var (hρ _ _ h)
  | lam _ ih =>
    -- Under the binder, the lifted renaming respects the extended contexts.
    apply HasType.lam
    apply ih
    intro i τ' h
    cases i with
    | zero => exact h                   -- the bound variable: 0 ↦ 0
    | succ i => exact hρ i τ' h         -- an outer variable: i + 1 ↦ ρ i + 1
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hρ) (ih₂ hρ)
  | tt => exact .tt
  | ff => exact .ff
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hρ) (iht hρ) (ihe hρ)
  | lit => exact .lit
  | add _ _ ih₁ ih₂ => exact .add (ih₁ hρ) (ih₂ hρ)
  | isZero _ ih => exact .isZero (ih hρ)
-- ANCHOR_END: rename_typing

-- ANCHOR: weakening
/-- Weakening: a term typed in `Γ` is still typed, after shifting, in a
context with one more variable in front. -/
theorem weakening {Γ : Ctx} {t : Term} {τ : Ty} (σ : Ty) (ht : HasType Γ t τ) :
    HasType (σ :: Γ) (shift t) τ :=
  rename_typing (fun _ _ h => h) ht
-- ANCHOR_END: weakening

/-! ## Substitution -/

-- ANCHOR: subst_typing
/-- Substitution preserves types, provided every variable is replaced by a term
of its own type: whenever `Γ` gives `i` type `τ`, the term `σ i` has type `τ`
in `Δ`. -/
theorem subst_typing {Γ Δ : Ctx} {σ : Nat → Term} {t : Term} {τ : Ty}
    (hσ : ∀ i τ, lookup Γ i = some τ → HasType Δ (σ i) τ)
    (ht : HasType Γ t τ) : HasType Δ (subst σ t) τ := by
  induction ht generalizing Δ σ with
  | var h => exact hσ _ _ h
  | @lam Γ α β t _ ih =>
    apply HasType.lam
    apply ih
    intro i τ' h
    cases i with
    | zero =>
      -- The bound variable is replaced by itself.
      exact .var h
    | succ i =>
      -- An outer variable is replaced by `shift (σ i)`, typed by weakening.
      exact weakening α (hσ i τ' h)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hσ) (ih₂ hσ)
  | tt => exact .tt
  | ff => exact .ff
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hσ) (iht hσ) (ihe hσ)
  | lit => exact .lit
  | add _ _ ih₁ ih₂ => exact .add (ih₁ hσ) (ih₂ hσ)
  | isZero _ ih => exact .isZero (ih hσ)
-- ANCHOR_END: subst_typing

-- ANCHOR: instantiate_typing
/-- The substitution lemma in the form β-reduction needs: if the body of a λ
has type `τ` when its parameter has type `σ`, and `s` has type `σ`, then the
instantiated body has type `τ`. -/
theorem instantiate_typing {Γ : Ctx} {σ τ : Ty} {body s : Term}
    (hbody : HasType (σ :: Γ) body τ) (hs : HasType Γ s σ) :
    HasType Γ (instantiate body s) τ := by
  apply subst_typing _ hbody
  intro i τ' h
  cases i with
  | zero =>
    -- Variable 0 has type σ in σ :: Γ: `h` computes to `some σ = some τ'`,
    -- and `cases` concludes that τ' is σ. Variable 0 is replaced by s : σ.
    cases h
    exact hs
  | succ i =>
    -- Variable i + 1 becomes var i, with the same type in Γ.
    exact .var h
-- ANCHOR_END: instantiate_typing

end Ch09
