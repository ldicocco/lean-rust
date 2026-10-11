import Book.Ch13.Unify

/-!
# Chapter 13 · Let-polymorphism, declaratively

The Hindley–Milner typing rules as an inductive relation, over the types and
substitutions of `Unify.lean`. Two programs that compute the same thing: the
`let` version has a typing derivation, and the `fun` version has none at all.
-/

namespace Ch13.HM

-- ANCHOR: syntax
/-- A fragment of mini-ML: enough for the chapter's example. -/
inductive Expr where
  | var : String → Expr
  | lit : Nat → Expr
  | tt : Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | let_ : String → Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr

/-- A type scheme `∀ vars. ty`. -/
structure Scheme where
  vars : List Nat
  ty : Ty

/-- A context binds names to schemes; the most recent binding comes first. -/
abbrev Ctx := List (String × Scheme)

def Ctx.lookup : Ctx → String → Option Scheme
  | [], _ => none
  | (y, σ) :: Γ, x => if x = y then some σ else Ctx.lookup Γ x

/-- The type variable `v` is free in the context: some scheme mentions it
without binding it. -/
def Ctx.Free (Γ : Ctx) (v : Nat) : Prop :=
  ∃ x σ, (x, σ) ∈ Γ ∧ σ.ty.occurs v = true ∧ v ∉ σ.vars

/-- `τ` is an instance of `∀ vars. ty`: substitute for the bound variables
(and only for them). -/
def Scheme.Inst (σ : Scheme) (τ : Ty) : Prop :=
  ∃ s : Subst, (∀ n, n ∉ σ.vars → s n = .var n) ∧ τ = σ.ty.subst s
-- ANCHOR_END: syntax

-- ANCHOR: rules
/-- The Hindley–Milner typing rules. -/
inductive HasType : Ctx → Expr → Ty → Prop
  /-- Var: instantiate the scheme of `x`. -/
  | var {Γ x σ τ} :
      Γ.lookup x = some σ → σ.Inst τ → HasType Γ (.var x) τ
  | lit {Γ n} : HasType Γ (.lit n) .int
  | tt {Γ} : HasType Γ .tt .bool
  /-- Abs: the parameter gets a monotype (a scheme with no bound variables). -/
  | lam {Γ x e τ₁ τ₂} :
      HasType ((x, ⟨[], τ₁⟩) :: Γ) e τ₂ → HasType Γ (.lam x e) (τ₁ ⇒ τ₂)
  | app {Γ f a τ₁ τ₂} :
      HasType Γ f (τ₁ ⇒ τ₂) → HasType Γ a τ₁ → HasType Γ (.app f a) τ₂
  /-- Let: generalize over variables that are not free in the context. -/
  | let_ {Γ x e₁ e₂ vs τ₁ τ₂} :
      HasType Γ e₁ τ₁ → (∀ v ∈ vs, ¬ Γ.Free v) →
      HasType ((x, ⟨vs, τ₁⟩) :: Γ) e₂ τ₂ → HasType Γ (.let_ x e₁ e₂) τ₂
  | ite {Γ c a b τ} :
      HasType Γ c .bool → HasType Γ a τ → HasType Γ b τ →
      HasType Γ (.ite c a b) τ
-- ANCHOR_END: rules

-- ANCHOR: programs
/-- `let id = fun x -> x in if id true then id 1 else 2` -/
def withLet : Expr :=
  .let_ "id" (.lam "x" (.var "x"))
    (.ite (.app (.var "id") .tt) (.app (.var "id") (.lit 1)) (.lit 2))

/-- `(fun id -> if id true then id 1 else 2)`, the same body under `fun`. -/
def withFun : Expr :=
  .lam "id" (.ite (.app (.var "id") .tt) (.app (.var "id") (.lit 1)) (.lit 2))
-- ANCHOR_END: programs

-- ANCHOR: with_let
/-- The scheme `∀ ?0. ?0 → ?0` has `τ → τ` as an instance, for every `τ`. -/
theorem id_inst (τ : Ty) : (Scheme.mk [0] (.var 0 ⇒ .var 0)).Inst (τ ⇒ τ) := by
  refine ⟨Subst.single 0 τ, ?_, rfl⟩
  -- Every variable other than `?0` is left alone by `[?0 := τ]`.
  intro n hn
  simp only [List.mem_singleton] at hn
  simp [Subst.single, hn]

/-- With `let`, the program has type `Int`: `id` is used at `Bool → Bool`
and at `Int → Int`. -/
theorem withLet_typed : HasType [] withLet .int := by
  apply HasType.let_ (vs := [0]) (τ₁ := .var 0 ⇒ .var 0)
  · -- `fun x -> x : ?0 → ?0`
    apply HasType.lam
    apply HasType.var rfl
    exact ⟨Subst.id, fun _ _ => rfl, (subst_id _).symm⟩
  · -- The empty context has no free variables, so `?0` may be generalized.
    intro v _ ⟨x, σ, hmem, _⟩
    cases hmem
  · -- The body, with `id : ∀ ?0. ?0 → ?0`.
    apply HasType.ite
    · exact HasType.app (HasType.var rfl (id_inst .bool)) HasType.tt
    · exact HasType.app (HasType.var rfl (id_inst .int)) HasType.lit
    · exact HasType.lit
-- ANCHOR_END: with_let

-- ANCHOR: with_fun
/-- A scheme with no bound variables has exactly one instance: itself. -/
theorem mono_inst {τ₁ τ : Ty} (h : (Scheme.mk [] τ₁).Inst τ) : τ = τ₁ := by
  obtain ⟨s, hs, rfl⟩ := h
  -- `s` changes no variable, so it is the identity substitution.
  have : s = Subst.id := funext fun n => hs n (List.not_mem_nil)
  rw [this, subst_id]

/-- With `fun`, the program has no type at all. -/
theorem withFun_untypable (τ : Ty) : ¬ HasType [] withFun τ := by
  intro h
  -- Invert the derivation, rule by rule, from the bottom up.
  cases h with
  | lam hbody =>
    -- `id : τ₁`, a monotype, and the body is an `if`.
    cases hbody with
    | ite hcond hthen _ =>
      -- `id true : Bool` forces `id : Bool → Bool`...
      cases hcond with
      | app hid htrue =>
        cases htrue
        cases hid with
        | var hlook hinst =>
          simp [Ctx.lookup] at hlook
          subst hlook
          have h1 := mono_inst hinst
          -- ...and `id 1` forces `id : Int → τ`.
          cases hthen with
          | app hid' hone =>
            cases hone
            cases hid' with
            | var hlook' hinst' =>
              simp [Ctx.lookup] at hlook'
              subst hlook'
              have h2 := mono_inst hinst'
              -- `Bool → Bool = Int → τ` is impossible: `Bool ≠ Int`.
              rw [← h1] at h2
              cases h2
-- ANCHOR_END: with_fun

end Ch13.HM
