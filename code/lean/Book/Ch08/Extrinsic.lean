import Book.Ch08.Intrinsic

/-!
# Chapter 8 · The extrinsic view, for contrast

Raw terms without types and a separate typing relation `HasType` (the style of
Chapters 3 and 9). Two theorems: self-application `λx. x x` has no simple
type, and erasing the types from an intrinsically typed term gives a raw term
that `HasType` accepts.
-/

namespace Ch08

open Ty

-- ANCHOR: raw
/-- Raw terms: de Bruijn indices, no type annotations, no guarantees. -/
inductive Raw where
  | var : Nat → Raw
  | lam : Raw → Raw
  | app : Raw → Raw → Raw
  | unit | tt | ff
  | ite : Raw → Raw → Raw → Raw
  | zero
  | succ : Raw → Raw
  | iter : Raw → Raw → Raw → Raw
  | pair : Raw → Raw → Raw
  | fst : Raw → Raw
  | snd : Raw → Raw
  | inl : Raw → Raw
  | inr : Raw → Raw
  | case : Raw → Raw → Raw → Raw
  deriving DecidableEq, Repr
-- ANCHOR_END: raw

-- ANCHOR: has_type
/-- The typing judgment `Γ ⊢ t : τ` as an inductive relation: one constructor
per typing rule. The λ rule does not say where `σ` comes from: any `σ` will
do, if the body can be typed with it (Curry style). -/
inductive HasType : List Ty → Raw → Ty → Prop where
  | var {Γ : List Ty} {k : Nat} {τ : Ty} :
      Γ[k]? = some τ → HasType Γ (.var k) τ
  | lam {Γ : List Ty} {t : Raw} {σ τ : Ty} :
      HasType (σ :: Γ) t τ → HasType Γ (.lam t) (σ ⇒ τ)
  | app {Γ : List Ty} {f a : Raw} {σ τ : Ty} :
      HasType Γ f (σ ⇒ τ) → HasType Γ a σ → HasType Γ (.app f a) τ
  | unit {Γ : List Ty} : HasType Γ .unit .unit
  | tt {Γ : List Ty} : HasType Γ .tt .bool
  | ff {Γ : List Ty} : HasType Γ .ff .bool
  | ite {Γ : List Ty} {c a b : Raw} {τ : Ty} :
      HasType Γ c .bool → HasType Γ a τ → HasType Γ b τ → HasType Γ (.ite c a b) τ
  | zero {Γ : List Ty} : HasType Γ .zero .nat
  | succ {Γ : List Ty} {n : Raw} : HasType Γ n .nat → HasType Γ (.succ n) .nat
  | iter {Γ : List Ty} {n z s : Raw} {τ : Ty} :
      HasType Γ n .nat → HasType Γ z τ → HasType Γ s (τ ⇒ τ) →
        HasType Γ (.iter n z s) τ
  | pair {Γ : List Ty} {a b : Raw} {σ τ : Ty} :
      HasType Γ a σ → HasType Γ b τ → HasType Γ (.pair a b) (.prod σ τ)
  | fst {Γ : List Ty} {p : Raw} {σ τ : Ty} :
      HasType Γ p (.prod σ τ) → HasType Γ (.fst p) σ
  | snd {Γ : List Ty} {p : Raw} {σ τ : Ty} :
      HasType Γ p (.prod σ τ) → HasType Γ (.snd p) τ
  | inl {Γ : List Ty} {a : Raw} {σ τ : Ty} :
      HasType Γ a σ → HasType Γ (.inl a) (.sum σ τ)
  | inr {Γ : List Ty} {b : Raw} {σ τ : Ty} :
      HasType Γ b τ → HasType Γ (.inr b) (.sum σ τ)
  | case {Γ : List Ty} {e l r : Raw} {σ τ ρ : Ty} :
      HasType Γ e (.sum σ τ) → HasType (σ :: Γ) l ρ → HasType (τ :: Γ) r ρ →
        HasType Γ (.case e l r) ρ
-- ANCHOR_END: has_type

-- ANCHOR: arrow_ne
/-- No type is a function type whose domain is the type itself: `σ ⇒ τ` is
always strictly bigger than `σ`. -/
theorem arrow_ne_self (σ τ : Ty) : (σ ⇒ τ) ≠ σ := by
  intro h
  -- Compare sizes: `sizeOf (σ ⇒ τ) = 1 + sizeOf σ + sizeOf τ`.
  have := congrArg sizeOf h
  simp at this
  omega
-- ANCHOR_END: arrow_ne

-- ANCHOR: no_self_app
/-- `λx. x x` has no type, in any context. -/
theorem self_application_untypable (Γ : List Ty) (τ : Ty) :
    ¬ HasType Γ (.lam (.app (.var 0) (.var 0))) τ := by
  intro h
  -- Only rule `lam` concludes a judgment about a `λ`: τ = σ ⇒ ρ for some σ, ρ,
  -- and the body `x x` has type ρ when `x : σ`.
  cases h with
  | lam hbody =>
    -- Only rule `app` concludes a judgment about an application: the first
    -- `x` has some type σ' ⇒ ρ and the second has type σ'.
    cases hbody with
    | app hf ha =>
      -- Both are the variable 0, whose type is σ: so σ = σ' ⇒ ρ and σ = σ'.
      cases hf with
      | var e₁ =>
        cases ha with
        | var e₂ =>
          simp at e₁ e₂
          -- e₁ : σ = σ' ⇒ ρ and e₂ : σ = σ', hence σ' ⇒ ρ = σ'.
          subst e₂
          exact arrow_ne_self _ _ e₁.symm
-- ANCHOR_END: no_self_app

-- ANCHOR: erase
/-- The position of a typed variable, as a de Bruijn index. -/
def Var.index {Γ : List Ty} {τ : Ty} : Var Γ τ → Nat
  | .here => 0
  | .there x => x.index + 1

/-- Forget the types: an intrinsically typed term becomes a raw term. -/
def Term.erase {Γ : List Ty} {τ : Ty} : Term Γ τ → Raw
  | .var x => .var x.index
  | .lam b => .lam b.erase
  | .app f a => .app f.erase a.erase
  | .unit => .unit
  | .tt => .tt
  | .ff => .ff
  | .ite c a b => .ite c.erase a.erase b.erase
  | .zero => .zero
  | .succ n => .succ n.erase
  | .iter n z s => .iter n.erase z.erase s.erase
  | .pair a b => .pair a.erase b.erase
  | .fst p => .fst p.erase
  | .snd p => .snd p.erase
  | .inl a => .inl a.erase
  | .inr b => .inr b.erase
  | .case e l r => .case e.erase l.erase r.erase
-- ANCHOR_END: erase

-- ANCHOR: erase_typed
/-- A typed variable's index points at its type in the context. -/
theorem Var.index_lookup {Γ : List Ty} {τ : Ty} (x : Var Γ τ) : Γ[x.index]? = some τ := by
  induction x with
  | here => rfl
  | there x ih => simpa [Var.index] using ih

/-- Every intrinsically typed term, once its types are erased, is accepted by
the extrinsic typing relation, at the same type: the constructors of `Term`
*are* the typing rules. -/
theorem Term.erase_typed {Γ : List Ty} {τ : Ty} (t : Term Γ τ) :
    HasType Γ t.erase τ := by
  induction t with
  | var x => exact .var x.index_lookup
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | unit => exact .unit
  | tt => exact .tt
  | ff => exact .ff
  | ite _ _ _ ihc iha ihb => exact .ite ihc iha ihb
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | iter _ _ _ ihn ihz ihs => exact .iter ihn ihz ihs
  | pair _ _ iha ihb => exact .pair iha ihb
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
-- ANCHOR_END: erase_typed

-- ANCHOR: erase_example
/-- Erasing `twice` gives back the untyped `λ. λ. 1 (1 0)` of Chapter 7. -/
example : twice.erase = .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0)))) := rfl

/-- So `HasType` accepts it, with the type that `twice` carries. -/
example : HasType [] twice.erase ((nat ⇒ nat) ⇒ nat ⇒ nat) := twice.erase_typed
-- ANCHOR_END: erase_example

end Ch08
