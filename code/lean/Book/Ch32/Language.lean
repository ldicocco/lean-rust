import Mathlib.Data.Nat.Notation

/-!
# Chapter 32 · A small language with an unchecked primitive

Natural numbers, booleans, `if`, functions and one primitive that the type
system has no rule for: unchecked subtraction `subRaw`, which gets stuck when
the result would be negative. Stuck is this language's version of undefined
behavior. The file defines the syntax, a big-step semantics with closures, the
syntactic typing rules and a fuel-based interpreter proved sound with respect
to the semantics. `Book.Ch32.LogicalRelation` builds the semantic types on top.
-/

namespace Ch32

-- ANCHOR: syntax
/-- Types: natural numbers, booleans and functions. -/
inductive Ty where
  | nat
  | bool
  | arr (dom cod : Ty)
  deriving DecidableEq, Repr

/-- Terms. Variables are de Bruijn indices: `var 0` is the nearest enclosing
`lam`, `var 1` the one around it, and so on. -/
inductive Expr where
  | var (i : ℕ)
  | nat (n : ℕ)
  | bool (b : Bool)
  | add (e₁ e₂ : Expr)
  | le (e₁ e₂ : Expr)       -- `e₁ ≤ e₂`, a boolean
  | ite (c t f : Expr)      -- `if c then t else f`
  | lam (body : Expr)       -- a function whose parameter is `var 0` in `body`
  | app (f a : Expr)
  | subRaw (e₁ e₂ : Expr)   -- unchecked `e₁ - e₂`: stuck when `e₁ < e₂`
  deriving Repr
-- ANCHOR_END: syntax

-- ANCHOR: values
/-- Values: numbers, booleans and closures. A closure is a function body
together with the environment it was created in. -/
inductive Val where
  | nat (n : ℕ)
  | bool (b : Bool)
  | clo (env : List Val) (body : Expr)
  deriving Repr
-- ANCHOR_END: values

-- ANCHOR: eval
/-- Big-step semantics. `Eval ρ e v` says: in the environment `ρ` (the values
of the variables, nearest first), the term `e` evaluates to the value `v`. -/
inductive Eval : List Val → Expr → Val → Prop where
  | var {ρ i v} : ρ[i]? = some v → Eval ρ (.var i) v
  | nat {ρ n} : Eval ρ (.nat n) (.nat n)
  | bool {ρ b} : Eval ρ (.bool b) (.bool b)
  | add {ρ e₁ e₂ n₁ n₂} :
      Eval ρ e₁ (.nat n₁) → Eval ρ e₂ (.nat n₂) →
      Eval ρ (.add e₁ e₂) (.nat (n₁ + n₂))
  | le {ρ e₁ e₂ n₁ n₂} :
      Eval ρ e₁ (.nat n₁) → Eval ρ e₂ (.nat n₂) →
      Eval ρ (.le e₁ e₂) (.bool (decide (n₁ ≤ n₂)))
  | iteTrue {ρ c t f v} :
      Eval ρ c (.bool true) → Eval ρ t v → Eval ρ (.ite c t f) v
  | iteFalse {ρ c t f v} :
      Eval ρ c (.bool false) → Eval ρ f v → Eval ρ (.ite c t f) v
  | lam {ρ body} : Eval ρ (.lam body) (.clo ρ body)
  | app {ρ f a ρ' body w v} :
      Eval ρ f (.clo ρ' body) → Eval ρ a w → Eval (w :: ρ') body v →
      Eval ρ (.app f a) v
  | subRaw {ρ e₁ e₂ n₁ n₂} :
      Eval ρ e₁ (.nat n₁) → Eval ρ e₂ (.nat n₂) → n₂ ≤ n₁ →
      Eval ρ (.subRaw e₁ e₂) (.nat (n₁ - n₂))
-- ANCHOR_END: eval

-- ANCHOR: has_type
/-- The syntactic typing rules. There is deliberately no rule for `subRaw`:
the type system cannot check its precondition `e₂ ≤ e₁`. -/
inductive HasType : List Ty → Expr → Ty → Prop where
  | var {Γ i τ} : Γ[i]? = some τ → HasType Γ (.var i) τ
  | nat {Γ n} : HasType Γ (.nat n) .nat
  | bool {Γ b} : HasType Γ (.bool b) .bool
  | add {Γ e₁ e₂} :
      HasType Γ e₁ .nat → HasType Γ e₂ .nat → HasType Γ (.add e₁ e₂) .nat
  | le {Γ e₁ e₂} :
      HasType Γ e₁ .nat → HasType Γ e₂ .nat → HasType Γ (.le e₁ e₂) .bool
  | ite {Γ c t f τ} :
      HasType Γ c .bool → HasType Γ t τ → HasType Γ f τ →
      HasType Γ (.ite c t f) τ
  | lam {Γ body σ τ} :
      HasType (σ :: Γ) body τ → HasType Γ (.lam body) (.arr σ τ)
  | app {Γ f a σ τ} :
      HasType Γ f (.arr σ τ) → HasType Γ a σ → HasType Γ (.app f a) τ
-- ANCHOR_END: has_type

/-! ## Two library functions, one careful and one careless -/

-- ANCHOR: libraries
/-- Saturating subtraction, `fun x y => if y ≤ x then x - y else 0`, written
with the unchecked primitive. Inside the body, `var 1` is `x` and `var 0`
is `y`. The `if` establishes the precondition of `subRaw` before calling it. -/
def satSub : Expr :=
  .lam (.lam (.ite (.le (.var 0) (.var 1)) (.subRaw (.var 1) (.var 0)) (.nat 0)))

/-- The careless version: it calls the primitive without checking. -/
def badSub : Expr :=
  .lam (.lam (.subRaw (.var 1) (.var 0)))

/-- Apply a two-argument function to two numbers. -/
def call₂ (f : Expr) (x y : ℕ) : Expr := .app (.app f (.nat x)) (.nat y)
-- ANCHOR_END: libraries

/-! ## A fuel-based interpreter -/

-- ANCHOR: outcome
/-- The three ways a run can end. -/
inductive Outcome where
  | value (v : Val)
  | stuck        -- no rule applies: the run went wrong
  | outOfFuel    -- we gave up before the run finished
  deriving Repr

/-- Continue with `k` if the run produced a value. -/
def Outcome.bind : Outcome → (Val → Outcome) → Outcome
  | .value v, k => k v
  | .stuck, _ => .stuck
  | .outOfFuel, _ => .outOfFuel
-- ANCHOR_END: outcome

-- ANCHOR: run
/-- Run `e` in the environment `ρ` for at most `fuel` nested steps. -/
def run : ℕ → List Val → Expr → Outcome
  | 0, _, _ => .outOfFuel
  | _ + 1, ρ, .var i =>
    match ρ[i]? with
    | some v => .value v
    | none => .stuck
  | _ + 1, _, .nat n => .value (.nat n)
  | _ + 1, _, .bool b => .value (.bool b)
  | k + 1, ρ, .add e₁ e₂ =>
    (run k ρ e₁).bind fun
      | .nat n₁ => (run k ρ e₂).bind fun
        | .nat n₂ => .value (.nat (n₁ + n₂))
        | _ => .stuck
      | _ => .stuck
  | k + 1, ρ, .le e₁ e₂ =>
    (run k ρ e₁).bind fun
      | .nat n₁ => (run k ρ e₂).bind fun
        | .nat n₂ => .value (.bool (decide (n₁ ≤ n₂)))
        | _ => .stuck
      | _ => .stuck
  | k + 1, ρ, .ite c t f =>
    (run k ρ c).bind fun
      | .bool true => run k ρ t
      | .bool false => run k ρ f
      | _ => .stuck
  | _ + 1, ρ, .lam body => .value (.clo ρ body)
  | k + 1, ρ, .app f a =>
    (run k ρ f).bind fun
      | .clo ρ' body => (run k ρ a).bind fun w => run k (w :: ρ') body
      | _ => .stuck
  | k + 1, ρ, .subRaw e₁ e₂ =>
    (run k ρ e₁).bind fun
      | .nat n₁ => (run k ρ e₂).bind fun
        | .nat n₂ => if n₂ ≤ n₁ then .value (.nat (n₁ - n₂)) else .stuck
        | _ => .stuck
      | _ => .stuck
-- ANCHOR_END: run

-- ANCHOR: run_examples
/-- info: Ch32.Outcome.value (Ch32.Val.nat 2) -/
#guard_msgs in
#eval run 10 [] (call₂ satSub 5 3)

/-- info: Ch32.Outcome.value (Ch32.Val.nat 0) -/
#guard_msgs in
#eval run 10 [] (call₂ satSub 3 5)

/-- info: Ch32.Outcome.value (Ch32.Val.nat 2) -/
#guard_msgs in
#eval run 10 [] (call₂ badSub 5 3)

/-- info: Ch32.Outcome.stuck -/
#guard_msgs in
#eval run 10 [] (call₂ badSub 3 5)
-- ANCHOR_END: run_examples

/-! ## The interpreter is sound -/

theorem Outcome.bind_eq_value {o : Outcome} {k : Val → Outcome} {v : Val} :
    o.bind k = .value v ↔ ∃ w, o = .value w ∧ k w = .value v := by
  cases o <;> simp [Outcome.bind]

-- ANCHOR: run_sound
/-- Whenever the interpreter returns a value, the big-step semantics agrees. -/
theorem run_sound : ∀ (fuel : ℕ) (ρ : List Val) (e : Expr) (v : Val),
    run fuel ρ e = .value v → Eval ρ e v := by
  intro fuel
  induction fuel with
  | zero => intro ρ e v h; simp [run] at h
  | succ k ih =>
    intro ρ e v h
    cases e with
    | var i =>
      simp only [run] at h
      split at h <;> simp_all [Eval.var]
    | nat n => simp only [run, Outcome.value.injEq] at h; subst h; exact .nat
    | bool b => simp only [run, Outcome.value.injEq] at h; subst h; exact .bool
    | add e₁ e₂ =>
      simp only [run, Outcome.bind_eq_value] at h
      obtain ⟨w₁, h₁, h⟩ := h
      split at h <;> simp only [Outcome.bind_eq_value, reduceCtorEq] at h
      obtain ⟨w₂, h₂, h⟩ := h
      split at h <;> simp only [Outcome.value.injEq, reduceCtorEq] at h
      subst h
      exact .add (ih _ _ _ h₁) (ih _ _ _ h₂)
    | le e₁ e₂ =>
      simp only [run, Outcome.bind_eq_value] at h
      obtain ⟨w₁, h₁, h⟩ := h
      split at h <;> simp only [Outcome.bind_eq_value, reduceCtorEq] at h
      obtain ⟨w₂, h₂, h⟩ := h
      split at h <;> simp only [Outcome.value.injEq, reduceCtorEq] at h
      subst h
      exact .le (ih _ _ _ h₁) (ih _ _ _ h₂)
    | ite c t f =>
      simp only [run, Outcome.bind_eq_value] at h
      obtain ⟨w, hc, h⟩ := h
      split at h
      · exact .iteTrue (ih _ _ _ hc) (ih _ _ _ h)
      · exact .iteFalse (ih _ _ _ hc) (ih _ _ _ h)
      · simp at h
    | lam body => simp only [run, Outcome.value.injEq] at h; subst h; exact .lam
    | app f a =>
      simp only [run, Outcome.bind_eq_value] at h
      obtain ⟨w₁, hf, h⟩ := h
      split at h <;> simp only [Outcome.bind_eq_value, reduceCtorEq] at h
      obtain ⟨w₂, ha, h⟩ := h
      exact .app (ih _ _ _ hf) (ih _ _ _ ha) (ih _ _ _ h)
    | subRaw e₁ e₂ =>
      simp only [run, Outcome.bind_eq_value] at h
      obtain ⟨w₁, h₁, h⟩ := h
      split at h <;> simp only [Outcome.bind_eq_value, reduceCtorEq] at h
      obtain ⟨w₂, h₂, h⟩ := h
      split at h
      · -- `w₂` is a number `n₂`: the run checks the precondition `n₂ ≤ n₁`
        split at h
        · simp only [Outcome.value.injEq] at h
          subst h
          exact .subRaw (ih _ _ _ h₁) (ih _ _ _ h₂) (by assumption)
        · simp at h
      · simp at h
-- ANCHOR_END: run_sound

end Ch32
