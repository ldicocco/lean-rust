import Mathlib.Data.Nat.Notation

/-!
# Chapter 12 · A type checker for System F

System F with one base type (`Bool`), type variables as de Bruijn indices, a
type checker written as a function, the typing rules written as an inductive
relation, and two theorems: the checker is sound (every type it reports can be
derived) and complete (every derivable type is the one it reports).
-/

namespace Ch12.SystemF

-- ANCHOR: ty
/-- Types: `Bool`, type variables, functions and `∀`. A type variable is a
number: `var 0` refers to the nearest enclosing `∀`, `var 1` to the one
outside it, and so on (de Bruijn indices, as in Chapter 7). -/
inductive Ty where
  | bool : Ty
  | var : ℕ → Ty
  | arr : Ty → Ty → Ty
  | all : Ty → Ty
deriving DecidableEq, Repr
-- ANCHOR_END: ty

namespace Ty

-- ANCHOR: lift_subst
/-- `τ.lift c` adds one to every type variable of `τ` that points outside the
innermost `c` binders. Needed when a type is moved under one more `∀`. -/
def lift : Ty → ℕ → Ty
  | bool, _ => bool
  | var k, c => if k < c then var k else var (k + 1)
  | arr a b, c => arr (a.lift c) (b.lift c)
  | all t, c => all (t.lift (c + 1))

/-- `τ.subst k σ` replaces variable `k` of `τ` by `σ`; the variables above `k`
move down by one, because the `∀` that bound `k` is gone. -/
def subst : Ty → ℕ → Ty → Ty
  | bool, _, _ => bool
  | var n, k, σ => if n < k then var n else if n = k then σ else var (n - 1)
  | arr a b, k, σ => arr (a.subst k σ) (b.subst k σ)
  | all t, k, σ => all (t.subst (k + 1) (σ.lift 0))
-- ANCHOR_END: lift_subst

-- ANCHOR: show
/-- A name for the type variable bound at depth `d`. -/
def name (d : ℕ) : String :=
  (["α", "β", "γ", "δ"][d]?).getD s!"α{d}"

/-- Print a type under `d` binders, with names instead of numbers. -/
def toStr (d : ℕ) : Ty → String
  | bool => "Bool"
  | var k => if k < d then name (d - 1 - k) else s!"#{k}"
  | arr a b =>
    let left := match a with
      | arr .. | all .. => s!"({a.toStr d})"
      | _ => a.toStr d
    s!"{left} → {b.toStr d}"
  | all t => s!"∀{name d}. {t.toStr (d + 1)}"
-- ANCHOR_END: show

end Ty

-- ANCHOR: term
/-- Terms. Term variables are de Bruijn indices into the context too. -/
inductive Term where
  | var : ℕ → Term              -- x
  | tt : Term                   -- true
  | ff : Term                   -- false
  | lam : Ty → Term → Term      -- λ (x : τ). e
  | app : Term → Term → Term    -- e₁ e₂
  | tlam : Term → Term          -- Λα. e
  | tapp : Term → Ty → Term     -- e [τ]
deriving Repr
-- ANCHOR_END: term

open Ty Term

-- ANCHOR: has_type
/-- The typing rules of System F. The context lists the types of the term
variables in scope, nearest first. Going under a `Λ` adds a type variable, so
every type already in the context is lifted past it. -/
inductive HasType : List Ty → Term → Ty → Prop
  | var {Γ i τ} : Γ[i]? = some τ → HasType Γ (.var i) τ
  | tt {Γ} : HasType Γ .tt .bool
  | ff {Γ} : HasType Γ .ff .bool
  | lam {Γ σ e τ} : HasType (σ :: Γ) e τ → HasType Γ (.lam σ e) (.arr σ τ)
  | app {Γ f a σ τ} :
      HasType Γ f (.arr σ τ) → HasType Γ a σ → HasType Γ (.app f a) τ
  | tlam {Γ e τ} : HasType (Γ.map (·.lift 0)) e τ → HasType Γ (.tlam e) (.all τ)
  | tapp {Γ e τ σ} : HasType Γ e (.all τ) → HasType Γ (.tapp e σ) (τ.subst 0 σ)
-- ANCHOR_END: has_type

-- ANCHOR: type_of
/-- The type checker: the rules read from the conclusion upwards. -/
def typeOf : List Ty → Term → Option Ty
  | Γ, .var i => Γ[i]?
  | _, .tt => some .bool
  | _, .ff => some .bool
  | Γ, .lam σ e => (typeOf (σ :: Γ) e).map (.arr σ)
  | Γ, .app f a =>
    match typeOf Γ f, typeOf Γ a with
    | some (.arr σ τ), some σ' => if σ = σ' then some τ else none
    | _, _ => none
  | Γ, .tlam e => (typeOf (Γ.map (·.lift 0)) e).map .all
  | Γ, .tapp e σ =>
    match typeOf Γ e with
    | some (.all τ) => some (τ.subst 0 σ)
    | _ => none

/-- Check a closed term and print its type. -/
def check (e : Term) : String :=
  match typeOf [] e with
  | some τ => τ.toStr 0
  | none => "type error"
-- ANCHOR_END: type_of

/-! ## Examples -/

-- ANCHOR: examples
/-- `Λα. λ (x : α). x` -/
def polyId : Term := .tlam (.lam (.var 0) (.var 0))

/-- The type of Church numerals, `∀α. (α → α) → α → α`. -/
def CNat : Ty := .all (.arr (.arr (.var 0) (.var 0)) (.arr (.var 0) (.var 0)))

/-- `Λα. λ (f : α → α). λ (x : α). f (f x)` -/
def two : Term :=
  .tlam (.lam (.arr (.var 0) (.var 0))
    (.lam (.var 0) (.app (.var 1) (.app (.var 1) (.var 0)))))

/-- `λ (n : CNat). Λα. λ (f : α → α). λ (x : α). f (n [α] f x)` -/
def succ : Term :=
  .lam CNat (.tlam (.lam (.arr (.var 0) (.var 0)) (.lam (.var 0)
    (.app (.var 1) (.app (.app (.tapp (.var 2) (.var 0)) (.var 1)) (.var 0))))))

/-- Self-application, typable thanks to impredicativity:
`λ (x : ∀α. α → α). x [∀α. α → α] x` -/
def selfApp : Term :=
  .lam (.all (.arr (.var 0) (.var 0)))
    (.app (.tapp (.var 0) (.all (.arr (.var 0) (.var 0)))) (.var 0))

/-- A rank-2 function: `λ (f : ∀α. α → α). f [Bool] true` -/
def useTwice : Term :=
  .lam (.all (.arr (.var 0) (.var 0))) (.app (.tapp (.var 0) .bool) .tt)
-- ANCHOR_END: examples

-- ANCHOR: examples_eval
/-- info: "∀α. α → α" -/
#guard_msgs in
#eval check polyId

/-- info: "Bool" -/
#guard_msgs in
#eval check (.app (.tapp polyId .bool) .tt)

/-- info: "∀α. (α → α) → α → α" -/
#guard_msgs in
#eval check two

/-- info: "(∀α. (α → α) → α → α) → ∀α. (α → α) → α → α" -/
#guard_msgs in
#eval check succ

/-- info: "∀α. (α → α) → α → α" -/
#guard_msgs in
#eval check (.app succ two)

/-- info: "(∀α. α → α) → ∀α. α → α" -/
#guard_msgs in
#eval check selfApp

/-- info: "(∀α. α → α) → Bool" -/
#guard_msgs in
#eval check useTwice

/-- info: "type error" -/
#guard_msgs in
#eval check (.lam .bool (.app (.var 0) (.var 0)))  -- λ (x : Bool). x x
-- ANCHOR_END: examples_eval

/-! ## The checker is sound and complete -/

-- ANCHOR: sound
/-- Soundness: if the checker returns a type, there is a derivation of it. -/
theorem typeOf_sound {Γ : List Ty} {e : Term} {τ : Ty} (h : typeOf Γ e = some τ) :
    HasType Γ e τ := by
  induction e generalizing Γ τ with
  | var i => exact .var h
  | tt =>
    -- h : some bool = some τ
    cases h
    exact .tt
  | ff =>
    cases h
    exact .ff
  | lam σ e ih =>
    -- h : (typeOf (σ :: Γ) e).map (arr σ) = some τ
    simp only [typeOf, Option.map_eq_some_iff] at h
    obtain ⟨τ', h', rfl⟩ := h
    exact .lam (ih h')
  | app f a ihf iha =>
    simp only [typeOf] at h
    -- Look at what the checker found for `f` and `a`.
    split at h
    · rename_i σ τ' σ' hf ha
      -- h : (if σ = σ' then some τ' else none) = some τ
      split at h
      · rename_i hσ
        cases h
        subst hσ
        exact .app (ihf hf) (iha ha)
      · cases h
    · cases h
  | tlam e ih =>
    simp only [typeOf, Option.map_eq_some_iff] at h
    obtain ⟨τ', h', rfl⟩ := h
    exact .tlam (ih h')
  | tapp e σ ih =>
    simp only [typeOf] at h
    split at h
    · rename_i τ' he
      cases h
      exact .tapp (ih he)
    · cases h
-- ANCHOR_END: sound

-- ANCHOR: complete
/-- Completeness: every derivable type is the one the checker reports. -/
theorem typeOf_complete {Γ : List Ty} {e : Term} {τ : Ty} (h : HasType Γ e τ) :
    typeOf Γ e = some τ := by
  induction h with
  | var hi => exact hi
  | tt => rfl
  | ff => rfl
  | lam _ ih => simp [typeOf, ih]
  | app _ _ ihf iha => simp [typeOf, ihf, iha]
  | tlam _ ih => simp [typeOf, ih]
  | tapp _ ih => simp [typeOf, ih]

/-- A consequence: a term has at most one type. -/
theorem type_unique {Γ : List Ty} {e : Term} {τ₁ τ₂ : Ty}
    (h₁ : HasType Γ e τ₁) (h₂ : HasType Γ e τ₂) : τ₁ = τ₂ := by
  have := (typeOf_complete h₁).symm.trans (typeOf_complete h₂)
  exact Option.some.inj this
-- ANCHOR_END: complete

end Ch12.SystemF
