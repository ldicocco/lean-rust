import Book.Ch22.Typing

/-!
# Chapter 22 · The usage theorem

In a well-typed term of `λ^aff`, every variable of the context is used at most
once, and a hole is not used at all. The proof is an induction on the typing
derivation; the key lemma is that splitting a context divides its resources
without creating any. Corollaries: `dup` has no type in any context, contraction
is not admissible, and projections on `⊗` can be defined but not both used.
-/

namespace Ch22

-- ANCHOR: avail
/-- How many times the term may use the variable `i` of `Γ`: once if it is
available, never if it is a hole or does not exist. -/
def avail (Γ : Ctx) (i : Nat) : Nat :=
  match Γ[i]? with
  | some (some _) => 1
  | _ => 0
-- ANCHOR_END: avail

@[simp] theorem avail_cons_succ (o : Option Ty) (Γ : Ctx) (i : Nat) :
    avail (o :: Γ) (i + 1) = avail Γ i := by
  simp [avail]

theorem avail_le_one (Γ : Ctx) (i : Nat) : avail Γ i ≤ 1 := by
  unfold avail
  split <;> omega

-- ANCHOR: split_avail
/-- Splitting divides resources and creates none: what `Γ` offers for the
variable `i` is the sum of what the two parts offer. -/
theorem Split.avail_add {Γ Γ₁ Γ₂ : Ctx} (hs : Split Γ Γ₁ Γ₂) (i : Nat) :
    avail Γ i = avail Γ₁ i + avail Γ₂ i := by
  induction hs generalizing i with
  | nil => simp [avail]
  | left _ ih | right _ ih | hole _ ih =>
    cases i with
    | zero => simp [avail]            -- position 0: 1 = 1 + 0, 1 = 0 + 1, 0 = 0 + 0
    | succ i => simpa using ih i      -- other positions: the induction hypothesis
-- ANCHOR_END: split_avail

-- ANCHOR: usage
/-- **The usage theorem.** In a term typed in `Γ`, each variable is used at
most as often as `Γ` makes it available. -/
theorem usage {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) :
    ∀ i, uses i e ≤ avail Γ i := by
  induction h with
  | @var Γ x τ hx =>
    intro i
    by_cases hi : i = x
    · subst hi; simp [uses, avail, hx]   -- the variable itself: 1 ≤ 1
    · simp [uses, hi]                    -- any other variable: 0 ≤ ...
  | unit => intro i; simp [uses]
  | lam _ ih =>
    -- Under the binder, our variable has index i + 1.
    intro i; simpa [uses] using ih (i + 1)
  | app hs _ _ ih₁ ih₂ | pair hs _ _ ih₁ ih₂ =>
    -- The two subterms are typed in the two parts of a split.
    intro i
    have h₁ := ih₁ i
    have h₂ := ih₂ i
    have hs' := hs.avail_add i
    simp only [uses]; omega
  | letPair hs _ _ ih₁ ih₂ =>
    intro i
    have h₁ := ih₁ i
    have h₂ := ih₂ (i + 2)
    have hs' := hs.avail_add i
    simp only [uses]; simp at h₂; omega
  | letIn hs _ _ ih₁ ih₂ =>
    intro i
    have h₁ := ih₁ i
    have h₂ := ih₂ (i + 1)
    have hs' := hs.avail_add i
    simp only [uses]; simp at h₂; omega
  | case hs _ _ _ ih ih₁ ih₂ =>
    -- The scrutinee and the branches split; the two branches share.
    intro i
    have h := ih i
    have h₁ := ih₁ (i + 1)
    have h₂ := ih₂ (i + 1)
    have hs' := hs.avail_add i
    simp only [uses]; simp at h₁ h₂; omega
  | wpair _ _ ih₁ ih₂ =>
    -- The two components share the context: count the larger of the two.
    intro i
    have h₁ := ih₁ i
    have h₂ := ih₂ i
    simp only [uses]; omega
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih =>
    intro i; simpa [uses] using ih i
-- ANCHOR_END: usage

-- ANCHOR: at_most_once
/-- Every variable is used at most once. -/
theorem at_most_once {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) (i : Nat) :
    uses i e ≤ 1 :=
  Nat.le_trans (usage h i) (avail_le_one Γ i)

/-- A hole is never used. -/
theorem hole_unused {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) {i : Nat}
    (hi : Γ[i]? = some none) : uses i e = 0 := by
  have := usage h i
  simp [avail, hi] at this
  exact this
-- ANCHOR_END: at_most_once

-- ANCHOR: dup_untypable
/-- `λx. (x, x)` has no type, in any context. -/
theorem dup_untypable (Γ : Ctx) (τ ρ : Ty) : ¬ HasType Γ (dup τ) ρ := by
  intro h
  cases h with
  | lam h =>
    -- The body uses variable 0 twice, but the context offers it once.
    have := usage h 0
    simp [uses, avail] at this
-- ANCHOR_END: dup_untypable

-- ANCHOR: contraction_fails
/-- Contraction is not admissible: `x : String, y : String ⊢ (x, y)` is
derivable, but identifying `x` and `y` gives `z : String ⊢ (z, z)`, which is not.
(In the de Bruijn notation, `y` is variable 0 and `x` is variable 1.) -/
theorem contraction_fails :
    HasType [some Str, some Str] (.pair (.var 1) (.var 0)) (Str ⊗ Str) ∧
    ¬ HasType [some Str] (.pair (.var 0) (.var 0)) (Str ⊗ Str) := by
  constructor
  · exact .pair (.right (.left .nil)) (.var rfl) (.var rfl)
  · intro h
    have := usage h 0
    simp [uses, avail] at this
-- ANCHOR_END: contraction_fails

/-! ## Projections on `⊗` -/

/-- The context with the same positions as `Γ`, all holes. -/
def Ctx.holes (Γ : Ctx) : Ctx := Γ.map fun _ => none

/-- Everything can go to the left. -/
theorem Split.all_left : (Γ : Ctx) → Split Γ Γ Γ.holes
  | [] => .nil
  | none :: Γ => .hole (Split.all_left Γ)
  | some _ :: Γ => .left (Split.all_left Γ)

-- ANCHOR: tensor_fst
/-- A first projection for `⊗`, defined with the `let`: `let (x, y) = e in x`.
The second component `y` is discarded. -/
def tfst (e : Term) : Term := .letPair e (.var 1)

/-- The second projection, `let (x, y) = e in y`. -/
def tsnd (e : Term) : Term := .letPair e (.var 0)

theorem tfst_typed {Γ : Ctx} {e : Term} {τ σ : Ty} (h : HasType Γ e (τ ⊗ σ)) :
    HasType Γ (tfst e) τ :=
  .letPair (Split.all_left Γ) h (.var rfl)

/-- But the two projections cannot both be applied to the same pair. -/
theorem no_both_projections (Γ : Ctx) (τ σ ρ : Ty) :
    ¬ HasType (some (τ ⊗ σ) :: Γ) (.pair (tfst (.var 0)) (tsnd (.var 0))) ρ := by
  intro h
  have := usage h 0
  simp [tfst, tsnd, uses, avail] at this
-- ANCHOR_END: tensor_fst

end Ch22
