import Book.Ch28.Syntax

/-!
# Chapter 28 · Typing rules of the borrow calculus

Contexts, context splitting with `Copy`, the typing judgment `Δ; Γ ⊢ e : τ` as
an inductive relation (one constructor per rule of the text), and the chapter's
metatheorem: in a well-typed term, a variable whose type is not `Copy` (an
owner, or a mutable reference) occurs at most once.
-/

namespace Ch28

-- ANCHOR: ctx
/-- A typing context: a list of variables with their types, most recent
first. -/
abbrev Ctx := List (Var × Ty)

/-- The type of `x` in `Γ`, if `x` is in `Γ`. -/
def lookup : Ctx → Var → Option Ty
  | [], _ => none
  | (y, τ) :: Γ, x => if x = y then some τ else lookup Γ x

/-- The variables of a context. -/
def dom (Γ : Ctx) : List Var := Γ.map Prod.fst
-- ANCHOR_END: ctx

-- ANCHOR: split
/-- `Split Γ Γ₁ Γ₂` is the text's `Γ = Γ₁ ⊎ Γ₂`: every entry of `Γ` goes to
the left part, to the right part, or, if its type is `Copy`, to both. -/
inductive Split : Ctx → Ctx → Ctx → Prop where
  | nil : Split [] [] []
  | left {b Γ Γ₁ Γ₂} : Split Γ Γ₁ Γ₂ → Split (b :: Γ) (b :: Γ₁) Γ₂
  | right {b Γ Γ₁ Γ₂} : Split Γ Γ₁ Γ₂ → Split (b :: Γ) Γ₁ (b :: Γ₂)
  | both {b Γ Γ₁ Γ₂} : Copy b.2 → Split Γ Γ₁ Γ₂ → Split (b :: Γ) (b :: Γ₁) (b :: Γ₂)
-- ANCHOR_END: split

-- ANCHOR: has_type
/-- The typing judgment `Δ; Γ ⊢ e : τ`: `Δ` lists the lifetimes in scope,
`Γ` the variables. The premises `x ∉ dom Γ₂` spell out the text's convention
that a context is only extended with a variable it does not already contain. -/
inductive HasType : List Lft → Ctx → Term → Ty → Prop where
  | var {Δ Γ x τ} :
      lookup Γ x = some τ →
      HasType Δ Γ (.var x) τ
  | lit {Δ Γ n} : HasType Δ Γ (.lit n) .int
  | unit {Δ Γ} : HasType Δ Γ .unit .unit
  | pair {Δ Γ Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ τ₁ →
      HasType Δ Γ₂ e₂ τ₂ →
      HasType Δ Γ (.pair e₁ e₂) (.pair τ₁ τ₂)
  | letIn {Δ Γ Γ₁ Γ₂ x e₁ e₂ τ₁ σ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ τ₁ →
      x ∉ dom Γ₂ →
      HasType Δ ((x, τ₁) :: Γ₂) e₂ σ →
      HasType Δ Γ (.letIn x e₁ e₂) σ
  | letPair {Δ Γ Γ₁ Γ₂ x y e₁ e₂ τ₁ τ₂ σ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ (.pair τ₁ τ₂) →
      x ∉ dom Γ₂ → y ∉ dom Γ₂ → x ≠ y →
      HasType Δ ((x, τ₁) :: (y, τ₂) :: Γ₂) e₂ σ →
      HasType Δ Γ (.letPair x y e₁ e₂) σ
  | new {Δ Γ e τ} :
      HasType Δ Γ e τ →
      HasType Δ Γ (.new e) (.box τ)
  | drop {Δ Γ e τ} :
      HasType Δ Γ e τ →
      HasType Δ Γ (.drop e) .unit
  | deref {Δ Γ e κ τ} :
      HasType Δ Γ e (.ref κ τ) →
      Copy τ →
      HasType Δ Γ (.deref e) τ
  | assign {Δ Γ Γ₁ Γ₂ e₁ e₂ κ τ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ (.refMut κ τ) →
      HasType Δ Γ₂ e₂ τ →
      HasType Δ Γ (.assign e₁ e₂) .unit
  | borrow {Δ Γ Γ₁ Γ₂ α y e₁ e₂ τ σ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ (.box τ) →
      y ∉ dom Γ₂ →
      HasType (α :: Δ) ((y, .ref α τ) :: Γ₂) e₂ σ →
      α ∉ Δ →
      α ∉ σ.lfts →
      HasType Δ Γ (.borrow α y e₁ e₂) (.pair (.box τ) σ)
  | borrowMut {Δ Γ Γ₁ Γ₂ α y e₁ e₂ τ σ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ (.box τ) →
      y ∉ dom Γ₂ →
      HasType (α :: Δ) ((y, .refMut α τ) :: Γ₂) e₂ σ →
      α ∉ Δ →
      α ∉ σ.lfts →
      HasType Δ Γ (.borrowMut α y e₁ e₂) (.pair (.box τ) σ)
  | reborrow {Δ Γ Γ₁ Γ₂ α y e₁ e₂ κ τ σ} :
      Split Γ Γ₁ Γ₂ →
      HasType Δ Γ₁ e₁ (.refMut κ τ) →
      y ∉ dom Γ₂ →
      HasType (α :: Δ) ((y, .refMut α τ) :: Γ₂) e₂ σ →
      α ∉ Δ →
      α ∉ σ.lfts →
      HasType Δ Γ (.reborrow α y e₁ e₂) (.pair (.refMut κ τ) σ)
-- ANCHOR_END: has_type

/-! ## Facts about contexts -/

-- ANCHOR: split_sublist
/-- Each part of a split is a sublist of the whole context. -/
theorem Split.sublist {Γ Γ₁ Γ₂ : Ctx} (h : Split Γ Γ₁ Γ₂) :
    Γ₁.Sublist Γ ∧ Γ₂.Sublist Γ := by
  induction h with
  | nil => exact ⟨.slnil, .slnil⟩
  | left _ ih => exact ⟨ih.1.cons_cons _, ih.2.cons _⟩
  | right _ ih => exact ⟨ih.1.cons _, ih.2.cons_cons _⟩
  | both _ _ ih => exact ⟨ih.1.cons_cons _, ih.2.cons_cons _⟩
-- ANCHOR_END: split_sublist

/-- A sublist has fewer variables. -/
theorem dom_subset {Γ' Γ : Ctx} (h : Γ'.Sublist Γ) {x : Var} (hx : x ∈ dom Γ') :
    x ∈ dom Γ :=
  (h.map Prod.fst).subset hx

/-- A sublist of a context without repeated variables has none either. -/
theorem nodup_of_sublist {Γ' Γ : Ctx} (h : Γ'.Sublist Γ) (hnd : (dom Γ).Nodup) :
    (dom Γ').Nodup :=
  hnd.sublist (h.map Prod.fst)

/-- The variables of an extended context. -/
@[simp] theorem dom_cons {Γ : Ctx} {y : Var} {τ : Ty} :
    dom ((y, τ) :: Γ) = y :: dom Γ := rfl

/-- A variable that has a type is in the context. -/
theorem mem_dom_of_lookup {Γ : Ctx} {x : Var} {τ : Ty} (h : lookup Γ x = some τ) :
    x ∈ dom Γ := by
  induction Γ with
  | nil => simp [lookup] at h
  | cons b Γ ih =>
    obtain ⟨y, σ⟩ := b
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [lookup, hxy] at h
      simp [ih h]

/-- A variable in the context differs from one that is not. -/
theorem ne_of_mem_dom {Γ : Ctx} {x y : Var} (hx : x ∈ dom Γ) (hy : y ∉ dom Γ) :
    x ≠ y :=
  fun h => hy (h ▸ hx)

/-- Looking past a different variable. -/
theorem lookup_cons_ne {Γ : Ctx} {x y : Var} {τ : Ty} (h : x ≠ y) :
    lookup ((y, τ) :: Γ) x = lookup Γ x := by
  simp [lookup, h]

-- ANCHOR: split_non_copy
/-- The heart of the matter. When `Γ` splits into `Γ₁` and `Γ₂`, a variable
whose type is not `Copy` ends up in exactly one of the two parts. -/
theorem Split.non_copy {Γ Γ₁ Γ₂ : Ctx} (hs : Split Γ Γ₁ Γ₂) (hnd : (dom Γ).Nodup)
    {x : Var} {σ : Ty} (hx : lookup Γ x = some σ) (hσ : ¬ Copy σ) :
    (lookup Γ₁ x = some σ ∧ x ∉ dom Γ₂) ∨ (lookup Γ₂ x = some σ ∧ x ∉ dom Γ₁) := by
  induction hs with
  | nil => simp [lookup] at hx
  | @left b Γ Γ₁ Γ₂ hs ih =>
    obtain ⟨y, τ⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hxy : x = y
    · -- `x` is the entry that went left; it is not repeated further down.
      subst hxy
      simp [lookup] at hx
      subst hx
      exact Or.inl ⟨by simp [lookup], fun hm => hnd.1 (dom_subset hs.sublist.2 hm)⟩
    · rw [lookup_cons_ne hxy] at hx
      rcases ih hnd.2 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨by rw [lookup_cons_ne hxy]; exact h₁, h₂⟩
      · exact Or.inr ⟨h₁, by simp [hxy, h₂]⟩
  | @right b Γ Γ₁ Γ₂ hs ih =>
    obtain ⟨y, τ⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hxy : x = y
    · subst hxy
      simp [lookup] at hx
      subst hx
      exact Or.inr ⟨by simp [lookup], fun hm => hnd.1 (dom_subset hs.sublist.1 hm)⟩
    · rw [lookup_cons_ne hxy] at hx
      rcases ih hnd.2 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, by simp [hxy, h₂]⟩
      · exact Or.inr ⟨by rw [lookup_cons_ne hxy]; exact h₁, h₂⟩
  | @both b Γ Γ₁ Γ₂ hc hs ih =>
    obtain ⟨y, τ⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hxy : x = y
    · -- The entry shared by both parts is `Copy`, but `x` is not.
      subst hxy
      simp [lookup] at hx
      subst hx
      exact absurd hc hσ
    · rw [lookup_cons_ne hxy] at hx
      rcases ih hnd.2 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨by rw [lookup_cons_ne hxy]; exact h₁, by simp [hxy, h₂]⟩
      · exact Or.inr ⟨by rw [lookup_cons_ne hxy]; exact h₁, by simp [hxy, h₂]⟩
-- ANCHOR_END: split_non_copy

-- ANCHOR: occ_zero
/-- A variable that is not in the context does not occur free in a well-typed
term. -/
theorem HasType.occ_eq_zero {Δ : List Lft} {Γ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Δ Γ e τ) {x : Var} (hx : x ∉ dom Γ) : e.occ x = 0 := by
  induction h generalizing x with
  | var hl =>
    have := mem_dom_of_lookup hl
    simp only [Term.occ]
    split
    · subst_vars; exact absurd this hx
    · rfl
  | lit | unit => rfl
  | pair hs _ _ ih₁ ih₂ | assign hs _ _ ih₁ ih₂ =>
    simp only [Term.occ,
      ih₁ (fun hm => hx (dom_subset hs.sublist.1 hm)),
      ih₂ (fun hm => hx (dom_subset hs.sublist.2 hm))]
  | new _ ih | drop _ ih | deref _ _ ih => exact ih hx
  | letIn hs _ _ _ ih₁ ih₂ | borrow hs _ _ _ _ _ ih₁ ih₂
  | borrowMut hs _ _ _ _ _ ih₁ ih₂ | reborrow hs _ _ _ _ _ ih₁ ih₂ =>
    have hx₂ : x ∉ dom _ := fun hm => hx (dom_subset hs.sublist.2 hm)
    simp only [Term.occ, ih₁ (fun hm => hx (dom_subset hs.sublist.1 hm)), Nat.zero_add]
    split
    · rfl
    · rename_i hne
      exact ih₂ (x := x) (by simp [hne, hx₂])
  | letPair hs _ _ _ _ _ ih₁ ih₂ =>
    have hx₂ : x ∉ dom _ := fun hm => hx (dom_subset hs.sublist.2 hm)
    simp only [Term.occ, ih₁ (fun hm => hx (dom_subset hs.sublist.1 hm)), Nat.zero_add]
    split
    · rfl
    · rename_i hne
      rw [not_or] at hne
      exact ih₂ (x := x) (by simp [hne.1, hne.2, hx₂])
-- ANCHOR_END: occ_zero

-- ANCHOR: var_mem
/-- A variable that has a type is in the context (inversion of rule T-Var). -/
theorem HasType.var_mem {Δ : List Lft} {Γ : Ctx} {x : Var} {τ : Ty}
    (h : HasType Δ Γ (.var x) τ) : x ∈ dom Γ := by
  cases h with
  | var hl => exact mem_dom_of_lookup hl
-- ANCHOR_END: var_mem

/-! ## The metatheorem -/

-- ANCHOR: used_at_most_once
-- ANCHOR: usage_simple
/-- **Usage theorem.** In a well-typed term, a variable whose type is not `Copy`
occurs free at most once. (The context must not repeat a variable; contexts
built by the rules never do.) -/
theorem HasType.used_at_most_once {Δ : List Lft} {Γ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Δ Γ e τ) (hnd : (dom Γ).Nodup)
    {x : Var} {σ : Ty} (hx : lookup Γ x = some σ) (hσ : ¬ Copy σ) :
    e.occ x ≤ 1 := by
  induction h generalizing x with
  | var _ =>
    -- A variable occurs once in itself and zero times in any other variable.
    simp only [Term.occ]
    split <;> omega
  | lit | unit => simp [Term.occ]
  | new _ ih | drop _ ih | deref _ _ ih =>
    -- One premise, same context: the induction hypothesis is the answer.
    exact ih hnd hx
-- ANCHOR_END: usage_simple
-- ANCHOR: usage_pair
  | pair hs h₁ h₂ ih₁ ih₂ | assign hs h₁ h₂ ih₁ ih₂ =>
    simp only [Term.occ]
    -- `x` went to exactly one side of the split.
    rcases hs.non_copy hnd hx hσ with ⟨hin, hout⟩ | ⟨hin, hout⟩
    · have := ih₁ (nodup_of_sublist hs.sublist.1 hnd) hin
      have := h₂.occ_eq_zero hout
      omega
    · have := h₁.occ_eq_zero hout
      have := ih₂ (nodup_of_sublist hs.sublist.2 hnd) hin
      omega
-- ANCHOR_END: usage_pair
-- ANCHOR: usage_binder
  | letIn hs h₁ hy h₂ ih₁ ih₂ | borrow hs h₁ hy h₂ _ _ ih₁ ih₂
  | borrowMut hs h₁ hy h₂ _ _ ih₁ ih₂ | reborrow hs h₁ hy h₂ _ _ ih₁ ih₂ =>
    simp only [Term.occ]
    rcases hs.non_copy hnd hx hσ with ⟨hin, hout⟩ | ⟨hin, hout⟩
    · -- `x` went to the first premise; the body cannot mention it.
      have := ih₁ (nodup_of_sublist hs.sublist.1 hnd) hin
      split
      · omega
      · rename_i hne
        have := h₂.occ_eq_zero (x := x) (by simp [hne, hout])
        omega
    · -- `x` went to the body, so it differs from the variable bound there.
      have := h₁.occ_eq_zero hout
      have hne := ne_of_mem_dom (mem_dom_of_lookup hin) hy
      have hnd₂ := nodup_of_sublist hs.sublist.2 hnd
      have := ih₂ (by rw [dom_cons, List.nodup_cons]; exact ⟨hy, hnd₂⟩)
        (by rw [lookup_cons_ne hne]; exact hin)
      simp only [hne, ite_false]
      omega
-- ANCHOR_END: usage_binder
  | letPair hs h₁ hx₁ hy₁ hxy h₂ ih₁ ih₂ =>
    simp only [Term.occ]
    rcases hs.non_copy hnd hx hσ with ⟨hin, hout⟩ | ⟨hin, hout⟩
    · have := ih₁ (nodup_of_sublist hs.sublist.1 hnd) hin
      split
      · omega
      · rename_i hne
        rw [not_or] at hne
        have := h₂.occ_eq_zero (x := x) (by simp [hne.1, hne.2, hout])
        omega
    · have := h₁.occ_eq_zero hout
      have hne₁ := ne_of_mem_dom (mem_dom_of_lookup hin) hx₁
      have hne₂ := ne_of_mem_dom (mem_dom_of_lookup hin) hy₁
      have hnd₂ := nodup_of_sublist hs.sublist.2 hnd
      have := ih₂
        (by simp only [dom_cons, List.nodup_cons, List.mem_cons]
            exact ⟨fun h => h.elim hxy hx₁, hy₁, hnd₂⟩)
        (by rw [lookup_cons_ne hne₁, lookup_cons_ne hne₂]; exact hin)
      simp only [hne₁, hne₂, or_self, ite_false]
      omega
-- ANCHOR_END: used_at_most_once

-- ANCHOR: ref_mut_once
/-- The case the chapter cares about: a mutable reference is used at most
once. -/
theorem HasType.ref_mut_used_at_most_once {Δ : List Lft} {Γ : Ctx} {e : Term}
    {τ : Ty} (h : HasType Δ Γ e τ) (hnd : (dom Γ).Nodup)
    {r : Var} {κ : Lft} {σ : Ty} (hr : lookup Γ r = some (.refMut κ σ)) :
    e.occ r ≤ 1 :=
  h.used_at_most_once hnd hr (not_copy_refMut κ σ)
-- ANCHOR_END: ref_mut_once

end Ch28
