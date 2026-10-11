import Mathlib.Data.Int.Notation
import Mathlib.Tactic.Linarith

/-!
# Chapter 27 · A tiny language with subtyping

Types with a subtyping relation: three base types `pos <: nat <: int` (all
represented at run time by integers) and function types. Types denote
*refinements*: a type says which run-time values belong to it. We prove

* soundness: if `σ <: τ`, every value of type `σ` is a value of type `τ`;
  the proof for function types is where contravariance is needed;
* that a covariant rule for arguments would be unsound (a counterexample);
* that an algorithmic subtyping check, without a transitivity rule, decides
  the relation;
* that a subtyping proof gives a coercion between Lean subtypes that does
  nothing to the value.
-/

namespace Ch27

-- ANCHOR: shape
/-- The shape of a type: what its values look like at run time. -/
inductive Shape where
  | base
  | arrow (s t : Shape)

/-- The run-time values of each shape: integers, and functions. -/
@[reducible] def Shape.Val : Shape → Type
  | .base => ℤ
  | .arrow s t => s.Val → t.Val
-- ANCHOR_END: shape

-- ANCHOR: ty
/-- Types, indexed by their shape. -/
inductive Ty : Shape → Type where
  | pos : Ty .base
  | nat : Ty .base
  | int : Ty .base
  | arrow {s t : Shape} (σ : Ty s) (τ : Ty t) : Ty (.arrow s t)

/-- Which values belong to a type. A function belongs to `σ ⇒ τ` when it maps
every value of `σ` to a value of `τ`. -/
def Ty.Holds : {s : Shape} → Ty s → s.Val → Prop
  | _, .pos, z => 0 < z
  | _, .nat, z => 0 ≤ z
  | _, .int, _ => True
  | _, .arrow σ τ, f => ∀ x, σ.Holds x → τ.Holds (f x)

/-- `σ ⇒ τ` is the type of functions from `σ` to `τ`. -/
scoped infixr:30 " ⇒ " => Ty.arrow
-- ANCHOR_END: ty

-- ANCHOR: sub
/-- The subtyping relation. -/
inductive Sub : {s : Shape} → Ty s → Ty s → Prop where
  | refl {s : Shape} (τ : Ty s) : Sub τ τ
  | trans {s : Shape} {σ τ υ : Ty s} : Sub σ τ → Sub τ υ → Sub σ υ
  | pos_nat : Sub .pos .nat
  | nat_int : Sub .nat .int
  | arrow {s t : Shape} {σ σ' : Ty s} {τ τ' : Ty t} :
      Sub σ' σ → Sub τ τ' → Sub (σ ⇒ τ) (σ' ⇒ τ')

/-- `σ <: τ`: `σ` is a subtype of `τ`. -/
scoped infix:50 " <: " => Sub
-- ANCHOR_END: sub

-- ANCHOR: sound
/-- **Subsumption is sound.** A value of a subtype is a value of the
supertype. -/
theorem Sub.sound {s : Shape} {σ τ : Ty s} (h : σ <: τ) :
    ∀ v, σ.Holds v → τ.Holds v := by
  induction h with
  | refl τ => exact fun v hv => hv
  | trans _ _ ih₁ ih₂ => exact fun v hv => ih₂ v (ih₁ v hv)
  | pos_nat =>
    -- 0 < v implies 0 ≤ v.
    intro v hv
    exact le_of_lt hv
  | nat_int => exact fun _ _ => trivial
  | arrow _ _ ihσ ihτ =>
    -- `f` maps σ to τ; we must show it maps σ' to τ'.
    intro f hf x hx
    -- `x` is a σ'. Since σ' <: σ (contravariance!), `x` is also a σ...
    have hxσ := ihσ x hx
    -- ...so `f x` is a τ, and since τ <: τ', it is a τ'.
    exact ihτ (f x) (hf x hxσ)
-- ANCHOR_END: sound

-- ANCHOR: bad
/-- The same relation with a *covariant* rule for function arguments. -/
inductive BadSub : {s : Shape} → Ty s → Ty s → Prop where
  | refl {s : Shape} (τ : Ty s) : BadSub τ τ
  | trans {s : Shape} {σ τ υ : Ty s} : BadSub σ τ → BadSub τ υ → BadSub σ υ
  | pos_nat : BadSub .pos .nat
  | nat_int : BadSub .nat .int
  | arrow {s t : Shape} {σ σ' : Ty s} {τ τ' : Ty t} :
      BadSub σ σ' → BadSub τ τ' → BadSub (σ ⇒ τ) (σ' ⇒ τ')

/-- With the covariant rule, subsumption is unsound. -/
theorem badSub_unsound :
    ¬ ∀ {s : Shape} (σ τ : Ty s), BadSub σ τ → ∀ v, σ.Holds v → τ.Holds v := by
  intro h
  -- The bad rule derives `nat ⇒ nat <: int ⇒ nat`.
  have hsub : BadSub (Ty.nat ⇒ .nat) (Ty.int ⇒ .nat) :=
    BadSub.arrow BadSub.nat_int (BadSub.refl _)
  -- The identity function maps naturals to naturals...
  have hid : (Ty.nat ⇒ .nat).Holds (fun z : ℤ => z) := fun _ hz => hz
  -- ...so it would also map every integer to a natural, -1 included.
  have hneg : (0 : ℤ) ≤ -1 := h _ _ hsub (fun z : ℤ => z) hid (-1) trivial
  linarith
-- ANCHOR_END: bad

/-! ## Algorithmic subtyping -/

-- ANCHOR: algorithmic
/-- The base types are a chain: `pos` below `nat` below `int`. -/
def Ty.rank : Ty .base → ℕ
  | .pos => 0
  | .nat => 1
  | .int => 2

/-- Subtyping as a function, with no transitivity rule: compare the ranks of
base types, and treat function types by their variance. -/
def subtype : {s : Shape} → Ty s → Ty s → Bool
  | .base, σ, τ => σ.rank ≤ τ.rank
  | .arrow _ _, .arrow σ τ, .arrow σ' τ' => subtype σ' σ && subtype τ τ'
-- ANCHOR_END: algorithmic

/-- On base types, the relation is the order of the ranks. -/
theorem sub_base {σ τ : Ty .base} (h : σ.rank ≤ τ.rank) : σ <: τ := by
  cases σ <;> cases τ <;> simp [Ty.rank] at h
  all_goals first
    | exact Sub.refl _
    | exact Sub.pos_nat
    | exact Sub.nat_int
    | exact Sub.trans Sub.pos_nat Sub.nat_int

theorem subtype_sound : {s : Shape} → {σ τ : Ty s} → subtype σ τ = true → σ <: τ
  | .base, _, _, h => sub_base (by simpa [subtype] using h)
  | .arrow _ _, .arrow _ _, .arrow _ _, h => by
    simp only [subtype, Bool.and_eq_true] at h
    exact Sub.arrow (subtype_sound h.1) (subtype_sound h.2)

theorem subtype_refl : {s : Shape} → (τ : Ty s) → subtype τ τ = true
  | .base, _ => by simp [subtype]
  | .arrow _ _, .arrow σ τ => by simp [subtype, subtype_refl σ, subtype_refl τ]

-- ANCHOR: subtype_trans
/-- Transitivity is *admissible*: the algorithm does not need a rule for it. -/
theorem subtype_trans : {s : Shape} → {σ τ υ : Ty s} →
    subtype σ τ = true → subtype τ υ = true → subtype σ υ = true
  | .base, _, _, _, h₁, h₂ => by
    simp only [subtype, decide_eq_true_eq] at h₁ h₂ ⊢
    omega
  | .arrow _ _, .arrow _ _, .arrow _ _, .arrow _ _, h₁, h₂ => by
    simp only [subtype, Bool.and_eq_true] at h₁ h₂ ⊢
    -- Arguments: υ's argument <: τ's <: σ's, the order flips.
    exact ⟨subtype_trans h₂.1 h₁.1, subtype_trans h₁.2 h₂.2⟩
-- ANCHOR_END: subtype_trans

theorem subtype_complete {s : Shape} {σ τ : Ty s} (h : σ <: τ) :
    subtype σ τ = true := by
  induction h with
  | refl τ => exact subtype_refl τ
  | trans _ _ ih₁ ih₂ => exact subtype_trans ih₁ ih₂
  | pos_nat => rfl
  | nat_int => rfl
  | arrow _ _ ihσ ihτ => simp [subtype, ihσ, ihτ]

-- ANCHOR: decide
/-- The algorithm decides subtyping, so `decide` can prove (and refute)
subtyping judgments. -/
instance {s : Shape} (σ τ : Ty s) : Decidable (σ <: τ) :=
  decidable_of_iff (subtype σ τ = true) ⟨subtype_sound, subtype_complete⟩

example : (Ty.int ⇒ .pos) <: (Ty.pos ⇒ .int) := by decide

example : ¬ (Ty.nat ⇒ .nat) <: (Ty.int ⇒ .nat) := by decide

example : ((Ty.pos ⇒ .int) ⇒ .pos) <: ((Ty.nat ⇒ .int) ⇒ .nat) := by decide
-- ANCHOR_END: decide

/-! ## Subtyping as a coercion that does nothing -/

-- ANCHOR: coe
/-- The values of a type, as a Lean subtype of the run-time values. -/
abbrev Ty.Sem {s : Shape} (τ : Ty s) : Type := {v : s.Val // τ.Holds v}

/-- A subtyping proof turns a value of `σ` into a value of `τ`... -/
def Sub.coe {s : Shape} {σ τ : Ty s} (h : σ <: τ) : σ.Sem → τ.Sem :=
  fun v => ⟨v.val, h.sound v.val v.property⟩

/-- ...without changing it: the underlying run-time value is the same. -/
theorem Sub.coe_val {s : Shape} {σ τ : Ty s} (h : σ <: τ) (v : σ.Sem) :
    (h.coe v).val = v.val := rfl
-- ANCHOR_END: coe

end Ch27
