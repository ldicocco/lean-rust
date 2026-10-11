import Book.Ch22.Checker
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Chapter 23 · `λ^aff` with `Copy` types

The affine λ-calculus of Chapter 22 (whose types, terms and `uses` function we
import) extended with a `Copy` predicate on types and a splitting rule that may
give a `Copy` variable to *both* sides. The typing rules are otherwise unchanged.
The usage theorem generalizes: every variable is used at most as often as its
multiplicity allows, where the multiplicity is `1` for an ordinary variable and
`⊤` (unbounded) for a `Copy` one. Non-`Copy` variables are still used at most
once.
-/

namespace Ch23

open Ch22

-- ANCHOR: is_copy
/-- The base types that are `Copy`: a few of Rust's scalar types. -/
def copyBase (name : String) : Bool :=
  name == "i32" || name == "u64" || name == "bool" || name == "char"

/-- The `Copy` predicate, decided by the structure of the type, the way rustc
decides it. A pair or a sum is `Copy` when its components are (this is the rule
of *promotion*). Functions and additive pairs are never `Copy`: their values
may hold resources that their types do not mention. -/
def isCopy : Ty → Bool
  | .base n => copyBase n
  | .unit => true
  | .tensor a b => isCopy a && isCopy b
  | .plus a b => isCopy a && isCopy b
  | .lolli _ _ => false
  | .amp _ _ => false
-- ANCHOR_END: is_copy

-- ANCHOR: copy_examples
def I32 : Ty := .base "i32"

example : isCopy I32 = true := rfl
example : isCopy (I32 ⊗ (I32 ⊕ .unit)) = true := rfl
example : isCopy Str = false := rfl
example : isCopy (I32 ⊗ Str) = false := rfl
example : isCopy (I32 ⊸ I32) = false := rfl

/-- Promotion: a pair is `Copy` exactly when both components are. -/
theorem isCopy_tensor (τ σ : Ty) :
    isCopy (τ ⊗ σ) = true ↔ isCopy τ = true ∧ isCopy σ = true := by
  simp [isCopy]
-- ANCHOR_END: copy_examples

-- ANCHOR: split_c
/-- Splitting with duplication: the four rules of Chapter 22, plus `both`,
which gives a variable to both sides when its type satisfies the predicate
`cp`. Rule `both` is contraction, restricted to the types that `cp` accepts.
The predicate is a parameter so that we can compare choices; the book's is
`isCopy`. -/
inductive SplitC (cp : Ty → Bool) : Ctx → Ctx → Ctx → Prop where
  | nil : SplitC cp [] [] []
  | left {Γ Γ₁ Γ₂ : Ctx} {τ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → SplitC cp (some τ :: Γ) (some τ :: Γ₁) (none :: Γ₂)
  | right {Γ Γ₁ Γ₂ : Ctx} {τ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → SplitC cp (some τ :: Γ) (none :: Γ₁) (some τ :: Γ₂)
  | hole {Γ Γ₁ Γ₂ : Ctx} :
      SplitC cp Γ Γ₁ Γ₂ → SplitC cp (none :: Γ) (none :: Γ₁) (none :: Γ₂)
  | both {Γ Γ₁ Γ₂ : Ctx} {τ : Ty} :
      cp τ = true →
      SplitC cp Γ Γ₁ Γ₂ → SplitC cp (some τ :: Γ) (some τ :: Γ₁) (some τ :: Γ₂)
-- ANCHOR_END: split_c

-- ANCHOR: has_type_c
/-- The typing rules of `λ^aff` with duplicable types: the rules of Chapter 22,
word for word, with `SplitC cp` in place of `Split`. -/
inductive HasTypeC (cp : Ty → Bool) : Ctx → Term → Ty → Prop where
  | var {Γ : Ctx} {x : Nat} {τ : Ty} :
      Γ[x]? = some (some τ) → HasTypeC cp Γ (.var x) τ
  | lam {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasTypeC cp (some τ :: Γ) e σ → HasTypeC cp Γ (.lam τ e) (τ ⊸ σ)
  | app {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → HasTypeC cp Γ₁ e₁ (τ ⊸ σ) → HasTypeC cp Γ₂ e₂ τ →
      HasTypeC cp Γ (.app e₁ e₂) σ
  | unit {Γ : Ctx} : HasTypeC cp Γ .unit .unit
  | pair {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → HasTypeC cp Γ₁ e₁ τ → HasTypeC cp Γ₂ e₂ σ →
      HasTypeC cp Γ (.pair e₁ e₂) (τ ⊗ σ)
  | letPair {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ ρ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → HasTypeC cp Γ₁ e₁ (τ ⊗ σ) →
      HasTypeC cp (some σ :: some τ :: Γ₂) e₂ ρ → HasTypeC cp Γ (.letPair e₁ e₂) ρ
  | wpair {Γ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      HasTypeC cp Γ e₁ τ → HasTypeC cp Γ e₂ σ → HasTypeC cp Γ (.wpair e₁ e₂) (τ & σ)
  | fst {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasTypeC cp Γ e (τ & σ) → HasTypeC cp Γ (.fst e) τ
  | snd {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasTypeC cp Γ e (τ & σ) → HasTypeC cp Γ (.snd e) σ
  | inl {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasTypeC cp Γ e τ → HasTypeC cp Γ (.inl σ e) (τ ⊕ σ)
  | inr {Γ : Ctx} {e : Term} {τ σ : Ty} :
      HasTypeC cp Γ e σ → HasTypeC cp Γ (.inr τ e) (τ ⊕ σ)
  | case {Γ Γ₁ Γ₂ : Ctx} {e e₁ e₂ : Term} {τ σ ρ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → HasTypeC cp Γ₁ e (τ ⊕ σ) →
      HasTypeC cp (some τ :: Γ₂) e₁ ρ → HasTypeC cp (some σ :: Γ₂) e₂ ρ →
      HasTypeC cp Γ (.case e e₁ e₂) ρ
  | letIn {Γ Γ₁ Γ₂ : Ctx} {e₁ e₂ : Term} {τ σ : Ty} :
      SplitC cp Γ Γ₁ Γ₂ → HasTypeC cp Γ₁ e₁ τ → HasTypeC cp (some τ :: Γ₂) e₂ σ →
      HasTypeC cp Γ (.letIn e₁ e₂) σ
-- ANCHOR_END: has_type_c

/-! ## The affine calculus is a fragment -/

theorem Split.toC {cp : Ty → Bool} {Γ Γ₁ Γ₂ : Ctx} (h : Split Γ Γ₁ Γ₂) :
    SplitC cp Γ Γ₁ Γ₂ := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | hole _ ih => exact .hole ih

-- ANCHOR: embed
/-- Every derivation of Chapter 22 is a derivation here, whatever the
predicate: adding duplication only adds programs. -/
theorem HasType.toC {cp : Ty → Bool} {Γ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Γ e τ) : HasTypeC cp Γ e τ := by
  induction h with
  | var hx => exact .var hx
  | lam _ ih => exact .lam ih
  | app hs _ _ ih₁ ih₂ => exact .app (Split.toC hs) ih₁ ih₂
  | unit => exact .unit
  | pair hs _ _ ih₁ ih₂ => exact .pair (Split.toC hs) ih₁ ih₂
  | letPair hs _ _ ih₁ ih₂ => exact .letPair (Split.toC hs) ih₁ ih₂
  | wpair _ _ ih₁ ih₂ => exact .wpair ih₁ ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case hs _ _ _ ih ih₁ ih₂ => exact .case (Split.toC hs) ih ih₁ ih₂
  | letIn hs _ _ ih₁ ih₂ => exact .letIn (Split.toC hs) ih₁ ih₂
-- ANCHOR_END: embed

/-! ## Examples -/

-- ANCHOR: copy_dup
/-- For a `Copy` type, `λx. (x, x)` is well typed: rule `both` gives `x` to the
two components. So every `Copy` type has a `clone`. -/
theorem copy_dup {τ : Ty} (hc : isCopy τ = true) :
    HasTypeC isCopy [] (dup τ) (τ ⊸ τ ⊗ τ) :=
  .lam (.pair (.both hc .nil) (.var rfl) (.var rfl))

/-- `n : i32 ⊢ (n, (n, n)) : i32 ⊗ (i32 ⊗ i32)`: a `Copy` variable can be used
any number of times. -/
example : HasTypeC isCopy [some I32] (.pair (.var 0) (.pair (.var 0) (.var 0)))
    (I32 ⊗ (I32 ⊗ I32)) :=
  .pair (.both rfl .nil) (.var rfl) (.pair (.both rfl .nil) (.var rfl) (.var rfl))
-- ANCHOR_END: copy_dup

/-! ## The generalized usage theorem -/

-- ANCHOR: avail_c
/-- The multiplicity of variable `i` in `Γ`, in `ℕ∞ = ℕ ∪ {⊤}`: unbounded for
a duplicable variable, one for any other variable, zero for a hole. -/
def availC (cp : Ty → Bool) (Γ : Ctx) (i : Nat) : ℕ∞ :=
  match Γ[i]? with
  | some (some τ) => if cp τ then ⊤ else 1
  | _ => 0
-- ANCHOR_END: avail_c

@[simp] theorem availC_cons_succ (cp : Ty → Bool) (o : Option Ty) (Γ : Ctx) (i : Nat) :
    availC cp (o :: Γ) (i + 1) = availC cp Γ i := by
  simp [availC]

-- ANCHOR: split_c_avail
/-- Splitting never creates resources. It may duplicate them, but only those
whose multiplicity is already `⊤`, and `⊤ + ⊤ = ⊤`. -/
theorem SplitC.avail_le {cp : Ty → Bool} {Γ Γ₁ Γ₂ : Ctx} (hs : SplitC cp Γ Γ₁ Γ₂)
    (i : Nat) : availC cp Γ₁ i + availC cp Γ₂ i ≤ availC cp Γ i := by
  induction hs generalizing i with
  | nil => simp [availC]
  | left _ ih | right _ ih | hole _ ih =>
    cases i with
    | zero => simp [availC]
    | succ i => simpa using ih i
  | both hc _ ih =>
    cases i with
    | zero => simp [availC, hc]          -- ⊤ + ⊤ ≤ ⊤
    | succ i => simpa using ih i
-- ANCHOR_END: split_c_avail

/-- The cast of a maximum is below `c` when both arguments are. -/
theorem cast_max_le {a b : ℕ} {c : ℕ∞} (ha : (a : ℕ∞) ≤ c) (hb : (b : ℕ∞) ≤ c) :
    ((max a b : ℕ) : ℕ∞) ≤ c := by
  rw [Nat.mono_cast.map_max]
  exact max_le ha hb

-- ANCHOR: usage_c
/-- **The generalized usage theorem.** Every variable is used at most as often as
its multiplicity allows, for every choice of the duplicable types. -/
theorem usageC {cp : Ty → Bool} {Γ : Ctx} {e : Term} {τ : Ty} (h : HasTypeC cp Γ e τ) :
    ∀ i, (uses i e : ℕ∞) ≤ availC cp Γ i := by
  induction h with
  | @var Γ x τ hx =>
    intro i
    by_cases hi : i = x
    · -- The variable itself: used once, and its multiplicity is 1 or ⊤.
      subst hi
      simp only [uses, ↓reduceIte, Nat.cast_one, availC, hx]
      split <;> simp
    · simp [uses, hi]
  | unit => intro i; simp [uses]
  | lam _ ih => intro i; simpa [uses] using ih (i + 1)
  | app hs _ _ ih₁ ih₂ | pair hs _ _ ih₁ ih₂ =>
    intro i
    simp only [uses, Nat.cast_add]
    exact (add_le_add (ih₁ i) (ih₂ i)).trans (hs.avail_le i)
  | letPair hs _ _ ih₁ ih₂ =>
    intro i
    have h₂ := ih₂ (i + 2)
    simp only [availC_cons_succ] at h₂
    simp only [uses, Nat.cast_add]
    exact (add_le_add (ih₁ i) h₂).trans (hs.avail_le i)
  | letIn hs _ _ ih₁ ih₂ =>
    intro i
    have h₂ := ih₂ (i + 1)
    simp only [availC_cons_succ] at h₂
    simp only [uses, Nat.cast_add]
    exact (add_le_add (ih₁ i) h₂).trans (hs.avail_le i)
  | case hs _ _ _ ih ih₁ ih₂ =>
    intro i
    have h₁ := ih₁ (i + 1)
    have h₂ := ih₂ (i + 1)
    simp only [availC_cons_succ] at h₁ h₂
    simp only [uses, Nat.cast_add]
    exact (add_le_add (ih i) (cast_max_le h₁ h₂)).trans (hs.avail_le i)
  | wpair _ _ ih₁ ih₂ =>
    intro i
    simp only [uses]
    exact cast_max_le (ih₁ i) (ih₂ i)
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih =>
    intro i; simpa [uses] using ih i
-- ANCHOR_END: usage_c

-- ANCHOR: non_copy_once
/-- **Non-duplicable variables are used at most once.** -/
theorem non_copy_at_most_once {cp : Ty → Bool} {Γ : Ctx} {e : Term} {τ σ : Ty}
    (h : HasTypeC cp Γ e τ) {i : Nat} (hi : Γ[i]? = some (some σ)) (hσ : cp σ = false) :
    uses i e ≤ 1 := by
  have := usageC h i
  simp [availC, hi, hσ] at this
  exact_mod_cast this

/-- So `λx. (x, x)` is still untypable at every non-`Copy` type. -/
theorem dup_untypable_c {τ ρ : Ty} (hσ : isCopy τ = false) (Γ : Ctx) :
    ¬ HasTypeC isCopy Γ (dup τ) ρ := by
  intro h
  cases h with
  | lam h =>
    have := non_copy_at_most_once h (i := 0) rfl hσ
    simp [uses] at this
-- ANCHOR_END: non_copy_once

/-! ## Why functions are not `Copy` -/

-- ANCHOR: promotion
/-- A bad choice: every function type is duplicable, whatever it captures. -/
def fnCopy : Ty → Bool
  | .lolli _ _ => true
  | t => isCopy t

/-- With `s : String` (variable 0): `let f = λu:𝟏. s in (f (), f ())`. The
closure captures `s`; the body calls the closure twice. -/
def callTwice : Term :=
  .letIn (.lam .unit (.var 1))
    (.pair (.app (.var 0) .unit) (.app (.var 0) .unit))

/-- What `callTwice` becomes after one step, `let f = v in e ⟶ e[v/f]`: the
closure, and with it `s`, now appears twice. -/
def callTwice' : Term :=
  .pair (.app (.lam .unit (.var 1)) .unit) (.app (.lam .unit (.var 1)) .unit)

/-- If closures were `Copy` whatever they capture, preservation would fail:
`callTwice` is typable, but the term it steps to is not. -/
theorem promotion_matters :
    HasTypeC fnCopy [some Str] callTwice (Str ⊗ Str) ∧
    ¬ HasTypeC fnCopy [some Str] callTwice' (Str ⊗ Str) := by
  constructor
  · -- `s` goes to the closure; the closure is shared by the two calls.
    exact .letIn (.left .nil) (.lam (.var rfl))
      (.pair (.both rfl (.hole .nil))
        (.app (.left (.hole .nil)) (.var rfl) .unit)
        (.app (.left (.hole .nil)) (.var rfl) .unit))
  · -- After the step, `s` occurs twice, and it is not duplicable.
    intro h
    have := non_copy_at_most_once h (i := 0) rfl rfl
    simp [callTwice', uses] at this

/-- With the real `isCopy`, `callTwice` is rejected in the first place: the
closure `f` is used twice, and a function type is never `Copy`. -/
theorem callTwice_rejected : ¬ HasTypeC isCopy [some Str] callTwice (Str ⊗ Str) := by
  intro h
  cases h with
  | letIn _ hf hbody =>
    -- The let-bound value is a λ, so `f` has a function type.
    cases hf with
    | lam _ =>
      have := non_copy_at_most_once hbody (i := 0) rfl rfl
      simp [uses] at this
-- ANCHOR_END: promotion

end Ch23
