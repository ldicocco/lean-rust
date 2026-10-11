import Book.Ch03.Arith

/-!
# Chapter 3 · The Arith checker is correct

Soundness (every type the checker reports is backed by a derivation),
completeness (every derivable judgment is found by the checker), uniqueness of
types (proved twice: by induction on derivations, and as a corollary of the
other two theorems), deciding the typing judgment, and proofs that no
derivation exists.
-/

namespace Ch03

-- ANCHOR: check_sound
/-- **Soundness.** If the checker says `τ`, there is a derivation of
`Γ ⊢ e : τ`. -/
theorem check_sound {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : check Γ e = some τ) : HasType Γ e τ := by
  induction e generalizing Γ τ with
  | num n =>
    -- h : check Γ (Expr.num n) = some τ, which computes to some Ty.nat = some τ
    simp only [check, Option.some.injEq] at h
    -- h : Ty.nat = τ
    subst h
    exact HasType.num
  | bool b =>
    simp only [check, Option.some.injEq] at h
    subst h
    exact HasType.bool
  | var x =>
    -- h : Γ.lookup x = some τ, exactly the premise of rule T-Var
    exact HasType.var h
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [check] at h
    split at h
    · -- The checker found Nat for both operands.
      rename_i h₁ h₂
      -- h₁ : check Γ e₁ = some Ty.nat, h₂ : check Γ e₂ = some Ty.nat
      -- h  : some Ty.nat = some τ
      cases h
      exact HasType.add (ih₁ h₁) (ih₂ h₂)
    · -- The checker returned none, but h says it returned some τ.
      contradiction
  | eq e₁ e₂ ih₁ ih₂ =>
    simp only [check] at h
    split at h
    · rename_i τ₁ τ₂ h₁ h₂
      split at h
      · -- The two operands have the same type: τ₁ = τ₂.
        rename_i same
        cases h
        subst same
        exact HasType.eq (ih₁ h₁) (ih₂ h₂)
      · contradiction
    · contradiction
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    simp only [check] at h
    split at h
    · rename_i τ₁ τ₂ hc h₁ h₂
      split at h
      · rename_i same
        cases h
        subst same
        exact HasType.ite (ihc hc) (ih₁ h₁) (ih₂ h₂)
      · contradiction
    · contradiction
  | letE x e₁ e₂ ih₁ ih₂ =>
    simp only [check] at h
    split at h
    · -- The checker found τ₁ for e₁ and then checked e₂ in the extended context.
      rename_i τ₁ h₁
      exact HasType.letE (ih₁ h₁) (ih₂ h)
    · contradiction
-- ANCHOR_END: check_sound

-- ANCHOR: check_complete
/-- **Completeness.** If there is a derivation, the checker finds its type. -/
theorem check_complete {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : HasType Γ e τ) : check Γ e = some τ := by
  induction h with
  | num => rfl
  | bool => rfl
  | var hx => exact hx
  | add _ _ ih₁ ih₂ => simp [check, ih₁, ih₂]
  | eq _ _ ih₁ ih₂ => simp [check, ih₁, ih₂]
  | ite _ _ _ ihc ih₁ ih₂ => simp [check, ihc, ih₁, ih₂]
  | letE _ _ ih₁ ih₂ => simp [check, ih₁, ih₂]
-- ANCHOR_END: check_complete

-- ANCHOR: check_iff
/-- The checker is a decision procedure for the typing judgment. -/
theorem check_iff {Γ : Ctx} {e : Expr} {τ : Ty} :
    check Γ e = some τ ↔ HasType Γ e τ :=
  ⟨check_sound, check_complete⟩

instance (Γ : Ctx) (e : Expr) (τ : Ty) : Decidable (HasType Γ e τ) :=
  decidable_of_iff (check Γ e = some τ) check_iff

example : HasType [] sample .nat := by decide

example : ¬ HasType [] (.add (.num 1) (.bool true)) .nat := by decide
-- ANCHOR_END: check_iff

-- ANCHOR: type_unique
/-- **Uniqueness of types.** An expression has at most one type in a given
context. Proved by induction on the first derivation and inversion of the
second. -/
theorem type_unique {Γ : Ctx} {e : Expr} {σ τ : Ty}
    (h₁ : HasType Γ e σ) (h₂ : HasType Γ e τ) : σ = τ := by
  induction h₁ generalizing τ with
  | num =>
    -- h₂ : HasType Γ (Expr.num n) τ. Only T-Num concludes that, and it forces
    -- τ = Ty.nat.
    cases h₂
    rfl
  | bool =>
    cases h₂
    rfl
  | var hσ =>
    -- hσ : Γ.lookup x = some σ; inverting h₂ gives hτ : Γ.lookup x = some τ.
    cases h₂ with
    | var hτ =>
      rw [hσ] at hτ
      -- hτ : some σ = some τ
      exact Option.some.inj hτ
  | add _ _ _ _ =>
    cases h₂
    rfl
  | eq _ _ _ _ =>
    cases h₂
    rfl
  | ite _ _ _ _ ih₁ _ =>
    -- The type of an `if` is the type of its first branch.
    cases h₂ with
    | ite _ h₂₁ _ => exact ih₁ h₂₁
  | letE _ _ ih₁ ih₂ =>
    cases h₂ with
    | letE h₂₁ h₂₂ =>
      -- Both derivations type e₁ first; by induction they agree on its type,
      have same := ih₁ h₂₁
      -- so they type e₂ in the same extended context, and agree again.
      subst same
      exact ih₂ h₂₂
-- ANCHOR_END: type_unique

-- ANCHOR: type_unique_corollary
/-- Uniqueness again, as a corollary: the checker is a function, and it
finds every type that can be derived. -/
theorem type_unique' {Γ : Ctx} {e : Expr} {σ τ : Ty}
    (h₁ : HasType Γ e σ) (h₂ : HasType Γ e τ) : σ = τ := by
  have hσ := check_complete h₁   -- check Γ e = some σ
  have hτ := check_complete h₂   -- check Γ e = some τ
  rw [hσ] at hτ                  -- some σ = some τ
  exact Option.some.inj hτ
-- ANCHOR_END: type_unique_corollary

-- ANCHOR: no_derivation
/-- No derivation of `⊢ 1 + true : τ` exists, whatever `τ` is. Proved by
inversion: the only rule that could conclude it is T-Add, whose second premise
would be a derivation of `⊢ true : Nat`, and no rule concludes that. -/
theorem add_bool_untypable (τ : Ty) :
    ¬ HasType [] (.add (.num 1) (.bool true)) τ := by
  intro h
  cases h with
  | add _ h₂ =>
    -- h₂ : HasType [] (Expr.bool true) Ty.nat
    cases h₂
-- ANCHOR_END: no_derivation

end Ch03
