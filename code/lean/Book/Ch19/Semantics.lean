import Book.Ch19.CCC

/-!
# Chapter 19 · The simply typed λ-calculus in any cartesian closed category

Intrinsically typed STLC terms (Chapter 8's representation, redefined here
with unit, products and functions over numbered base types), their
interpretation in an arbitrary cartesian closed category, and Lambek's
soundness theorem: β and η hold in every CCC. In `Type` the interpretation is
an evaluator and the β-law holds by `rfl`; in a Heyting algebra it turns a
term into a proof.
-/

namespace Ch19.STLC

open Ch16 Ch19 Ch19.HasTerminal Ch19.HasProducts Ch19.CartesianClosed

universe u

-- ANCHOR: syntax
inductive Ty where
  | base : ℕ → Ty           -- base types `o₀, o₁, ...`
  | unit : Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty

abbrev Ctx := List Ty

/-- A variable is a typed position in the context (a de Bruijn index). -/
inductive Var : Ctx → Ty → Type where
  | here {Γ : Ctx} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : Ctx} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

/-- Terms in context: `Term Γ τ` is the type of derivations of `Γ ⊢ t : τ`. -/
inductive Term : Ctx → Ty → Type where
  | var {Γ τ} : Var Γ τ → Term Γ τ
  | lam {Γ σ τ} : Term (σ :: Γ) τ → Term Γ (.arr σ τ)
  | app {Γ σ τ} : Term Γ (.arr σ τ) → Term Γ σ → Term Γ τ
  | unit {Γ} : Term Γ .unit
  | pair {Γ σ τ} : Term Γ σ → Term Γ τ → Term Γ (.prod σ τ)
  | fst {Γ σ τ} : Term Γ (.prod σ τ) → Term Γ σ
  | snd {Γ σ τ} : Term Γ (.prod σ τ) → Term Γ τ
-- ANCHOR_END: syntax

-- ANCHOR: substitution
/-- Renamings and substitutions: what to put in place of each variable. -/
abbrev Ren (Γ Δ : Ctx) := ∀ {τ}, Var Γ τ → Var Δ τ
abbrev Sub (Γ Δ : Ctx) := ∀ {τ}, Var Γ τ → Term Δ τ

/-- Push a renaming under a binder. -/
def Ren.lift {Γ Δ σ} (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def Term.rename {Γ Δ} (r : Ren Γ Δ) : {τ : Ty} → Term Γ τ → Term Δ τ
  | _, .var v => .var (r v)
  | _, .lam t => .lam (t.rename r.lift)
  | _, .app f a => .app (f.rename r) (a.rename r)
  | _, .unit => .unit
  | _, .pair a b => .pair (a.rename r) (b.rename r)
  | _, .fst p => .fst (p.rename r)
  | _, .snd p => .snd (p.rename r)

/-- Push a substitution under a binder (the bound variable stays itself; the
other terms are weakened by one). -/
def Sub.lift {Γ Δ σ} (s : Sub Γ Δ) : Sub (σ :: Γ) (σ :: Δ)
  | _, .here => .var .here
  | _, .there v => (s v).rename .there

def Term.subst {Γ Δ} (s : Sub Γ Δ) : {τ : Ty} → Term Γ τ → Term Δ τ
  | _, .var v => s v
  | _, .lam t => .lam (t.subst s.lift)
  | _, .app f a => .app (f.subst s) (a.subst s)
  | _, .unit => .unit
  | _, .pair a b => .pair (a.subst s) (b.subst s)
  | _, .fst p => .fst (p.subst s)
  | _, .snd p => .snd (p.subst s)

/-- The substitution `[a/x]` for the innermost variable `x`. -/
def Sub.single {Γ σ} (a : Term Γ σ) : Sub (σ :: Γ) Γ
  | _, .here => a
  | _, .there v => .var v
-- ANCHOR_END: substitution

section Interpretation

variable {Obj : Type u} [Category Obj] [HasTerminal Obj] [HasProducts Obj]
  [CartesianClosed Obj] (B : ℕ → Obj)

-- ANCHOR: interp
/-- Types are objects. -/
@[reducible] def Ty.interp : Ty → Obj
  | .base i => B i
  | .unit => one
  | .prod σ τ => σ.interp ⨯ τ.interp
  | .arr σ τ => σ.interp ⟹ τ.interp

/-- Contexts are products of objects, the newest variable on the right. -/
@[reducible] def Ctx.interp : Ctx → Obj
  | [] => one
  | τ :: Γ => Ctx.interp Γ ⨯ τ.interp B

/-- A variable is a projection out of the context. -/
def Var.interp : {Γ : Ctx} → {τ : Ty} → Var Γ τ → (Ctx.interp B Γ ⟶ τ.interp B)
  | _, _, .here => snd
  | _, _, .there v => v.interp ⊚ fst

/-- A term in context `Γ` of type `τ` is a morphism `⟦Γ⟧ ⟶ ⟦τ⟧`. -/
def Term.interp : {Γ : Ctx} → {τ : Ty} → Term Γ τ → (Ctx.interp B Γ ⟶ τ.interp B)
  | _, _, .var v => v.interp B
  | _, _, .lam t => curry t.interp
  | _, _, .app f a => eval ⊚ HasProducts.pair f.interp a.interp
  | _, _, .unit => toOne _
  | _, _, .pair a b => HasProducts.pair a.interp b.interp
  | _, _, .fst p => HasProducts.fst ⊚ p.interp
  | _, _, .snd p => HasProducts.snd ⊚ p.interp
-- ANCHOR_END: interp

-- ANCHOR: interp_ren
/-- A renaming `Γ → Δ` is a morphism `⟦Δ⟧ ⟶ ⟦Γ⟧` (note the direction: it
builds the old environment from the new one). -/
def Ren.interp {Δ : Ctx} : (Γ : Ctx) → Ren Γ Δ → (Ctx.interp B Δ ⟶ Ctx.interp B Γ)
  | [], _ => toOne _
  | _ :: Γ, r => pair (Ren.interp Γ fun v => r (.there v)) ((r .here).interp B)

/-- The same for substitutions. -/
def Sub.interp {Δ : Ctx} : (Γ : Ctx) → Sub Γ Δ → (Ctx.interp B Δ ⟶ Ctx.interp B Γ)
  | [], _ => toOne _
  | _ :: Γ, s => pair (Sub.interp Γ fun v => s (.there v)) ((s .here).interp B)
-- ANCHOR_END: interp_ren

/-! ### Renaming -/

theorem Ren.interp_var {Γ Δ τ} (r : Ren Γ Δ) (v : Var Γ τ) :
    (r v).interp B = v.interp B ⊚ Ren.interp B Γ r := by
  induction v with
  | here => exact (snd_pair _ _).symm
  | there v ih =>
    rw [Var.interp, ← Category.assoc, Ren.interp, fst_pair]
    exact ih (fun w => r (.there w))

/-- Weakening a renaming composes its meaning with the first projection. -/
theorem Ren.interp_there {Δ σ} : (Γ : Ctx) → (r : Ren Γ Δ) →
    Ren.interp B Γ (fun v => (Var.there (σ := σ) (r v))) = Ren.interp B Γ r ⊚ fst
  | [], _ => (toOne_unique _).trans (toOne_unique _).symm
  | _ :: Γ, r => by
    rw [Ren.interp, Ren.interp, pair_comp, Ren.interp_there Γ]
    rfl

theorem Ren.interp_id : (Γ : Ctx) → Ren.interp B Γ (fun v => v) = Category.id _
  | [] => (toOne_unique _).trans (toOne_unique _).symm
  | _ :: Γ => by
    rw [Ren.interp, Ren.interp_there B Γ (fun v => v), Ren.interp_id Γ,
      Category.id_comp]
    exact pair_fst_snd

theorem Ren.interp_lift {Γ Δ σ} (r : Ren Γ Δ) :
    Ren.interp B (σ :: Γ) r.lift = prodMap (Ren.interp B Γ r) (Category.id _) := by
  rw [Ren.interp]
  show pair (Ren.interp B Γ fun v => .there (r v)) snd = _
  rw [Ren.interp_there, prodMap, Category.id_comp]

theorem Term.interp_rename {Γ Δ τ} (r : Ren Γ Δ) (t : Term Γ τ) :
    (t.rename r).interp B = t.interp B ⊚ Ren.interp B Γ r := by
  induction t generalizing Δ with
  | var v => exact Ren.interp_var B r v
  | lam t ih =>
    rw [Term.rename, Term.interp, ih, Ren.interp_lift, curry_natural, Term.interp]
  | app f a ihf iha =>
    rw [Term.rename, Term.interp, ihf, iha, Term.interp, ← pair_comp, Category.assoc]
  | unit => exact (toOne_unique _).trans (toOne_unique _).symm
  | pair a b iha ihb => rw [Term.rename, Term.interp, iha, ihb, Term.interp, pair_comp]
  | fst p ih => rw [Term.rename, Term.interp, ih, Term.interp, Category.assoc]
  | snd p ih => rw [Term.rename, Term.interp, ih, Term.interp, Category.assoc]

/-! ### Substitution -/

theorem Sub.interp_var {Γ Δ τ} (s : Sub Γ Δ) (v : Var Γ τ) :
    (s v).interp B = v.interp B ⊚ Sub.interp B Γ s := by
  induction v with
  | here => exact (snd_pair _ _).symm
  | there v ih =>
    rw [Var.interp, ← Category.assoc, Sub.interp, fst_pair]
    exact ih (fun w => s (.there w))

theorem Sub.interp_weaken {Δ σ} : (Γ : Ctx) → (s : Sub Γ Δ) →
    Sub.interp B Γ (fun v => (s v).rename (Var.there (σ := σ))) =
      Sub.interp B Γ s ⊚ fst
  | [], _ => (toOne_unique _).trans (toOne_unique _).symm
  | _ :: Γ, s => by
    rw [Sub.interp, Sub.interp, pair_comp, Sub.interp_weaken Γ, Term.interp_rename,
      Ren.interp_there B _ (fun v => v), Ren.interp_id, Category.id_comp]

theorem Sub.interp_lift {Γ Δ σ} (s : Sub Γ Δ) :
    Sub.interp B (σ :: Γ) s.lift = prodMap (Sub.interp B Γ s) (Category.id _) := by
  rw [Sub.interp]
  show pair (Sub.interp B Γ fun v => (s v).rename .there) snd = _
  rw [Sub.interp_weaken, prodMap, Category.id_comp]

theorem Sub.interp_vars : (Γ : Ctx) → Sub.interp B Γ (fun v => Term.var v) = Category.id _
  | [] => (toOne_unique _).trans (toOne_unique _).symm
  | _ :: Γ => by
    rw [Sub.interp]
    show pair (Sub.interp B Γ fun v => (Term.var v).rename .there) snd = _
    rw [Sub.interp_weaken, Sub.interp_vars Γ, Category.id_comp]
    exact pair_fst_snd

-- ANCHOR: subst_lemma
/-- **The substitution lemma**: substituting is composing. -/
theorem Term.interp_subst {Γ Δ τ} (s : Sub Γ Δ) (t : Term Γ τ) :
    (t.subst s).interp B = t.interp B ⊚ Sub.interp B Γ s := by
  induction t generalizing Δ with
  | var v =>
    -- A variable: look it up in the substitution.
    exact Sub.interp_var B s v
  | lam t ih =>
    -- Under a binder the substitution is lifted, which means `⟦s⟧ × id`,
    -- and `curry` absorbs it by naturality.
    rw [Term.subst, Term.interp, ih, Sub.interp_lift, curry_natural, Term.interp]
  | app f a ihf iha =>
    -- `pair (⟦f⟧ ⊚ ⟦s⟧) (⟦a⟧ ⊚ ⟦s⟧) = pair ⟦f⟧ ⟦a⟧ ⊚ ⟦s⟧`, then associativity.
    rw [Term.subst, Term.interp, ihf, iha, Term.interp, ← pair_comp, Category.assoc]
  | unit =>
    -- Two morphisms into the terminal object are equal.
    exact (toOne_unique _).trans (toOne_unique _).symm
  | pair a b iha ihb => rw [Term.subst, Term.interp, iha, ihb, Term.interp, pair_comp]
  | fst p ih => rw [Term.subst, Term.interp, ih, Term.interp, Category.assoc]
  | snd p ih => rw [Term.subst, Term.interp, ih, Term.interp, Category.assoc]
-- ANCHOR_END: subst_lemma

-- ANCHOR: beta_eta
/-- **β is sound in every CCC**: `(λx. t) a` and `t[a/x]` have the same
meaning. -/
theorem beta {Γ σ τ} (t : Term (σ :: Γ) τ) (a : Term Γ σ) :
    (Term.app (.lam t) a).interp B = (t.subst (Sub.single a)).interp B := by
  -- Right side: ⟦t⟧ ⊚ ⟦[a/x]⟧ (substitution lemma).
  -- Left side:  eval ⊚ pair (curry ⟦t⟧) ⟦a⟧ = ⟦t⟧ ⊚ pair id ⟦a⟧ (categorical β).
  rw [Term.interp_subst, Term.interp, Term.interp, eval_pair_curry]
  -- Both sides are now `⟦t⟧ ⊚ _`; compare what follows `⟦t⟧`.
  congr 1
  -- The meaning of `[a/x]` is `pair ⟦vars⟧ ⟦a⟧`, and `⟦vars⟧ = id`.
  show _ = pair (Sub.interp B Γ fun v => Term.var v) (a.interp B)
  rw [Sub.interp_vars]

/-- **η is sound in every CCC**: `λx. f x` (with `f` weakened past `x`) and
`f` have the same meaning. -/
theorem eta {Γ σ τ} (f : Term Γ (.arr σ τ)) :
    (Term.lam (.app (f.rename .there) (.var .here))).interp B = f.interp B := by
  -- Unfold, and use that weakening `f` means precomposing with `fst`.
  rw [Term.interp, Term.interp, Term.interp_rename, Ren.interp_there B Γ (fun v => v),
    Ren.interp_id, Category.id_comp]
  -- Goal: curry (eval ⊚ pair (⟦f⟧ ⊚ fst) snd) = ⟦f⟧
  show curry (eval ⊚ pair (f.interp B ⊚ fst) snd) = _
  -- `pair (⟦f⟧ ⊚ fst) (id ⊚ snd)` is `prodMap ⟦f⟧ id`: this is `curry_unique`.
  rw [← Category.id_comp (snd (a := Ctx.interp B Γ) (b := σ.interp B))]
  exact curry_unique (f.interp B)
-- ANCHOR_END: beta_eta

end Interpretation

/-! ## Two models: programs and proofs -/

-- ANCHOR: examples
/-- `λp. (snd p, fst p) : o₀ × o₁ → o₁ × o₀` -/
def swap : Term [] (.arr (.prod (.base 0) (.base 1)) (.prod (.base 1) (.base 0))) :=
  .lam (.pair (.snd (.var .here)) (.fst (.var .here)))

/-- `λx. (x, x) : o₀ → o₀ × o₀`: the diagonal, which uses `x` twice. -/
def dup : Term [] (.arr (.base 0) (.prod (.base 0) (.base 0))) :=
  .lam (.pair (.var .here) (.var .here))

/-- `λf. λa. λb. f (a, b)`: currying, as a closed term. -/
def curryTerm (a b c : Ty) : Term [] (.arr (.arr (.prod a b) c) (.arr a (.arr b c))) :=
  .lam (.lam (.lam (.app (.var (.there (.there .here)))
    (.pair (.var (.there .here)) (.var .here)))))
-- ANCHOR_END: examples

-- ANCHOR: type_model
/-- In `Type`, with `o₀ = ℕ` and `o₁ = String`, `swap` means swapping. -/
def typeBase : ℕ → Type
  | 0 => ℕ
  | _ => String

example : (swap.interp typeBase) () ((7 : ℕ), "seven") = ("seven", (7 : ℕ)) := rfl

/-- `dup` means copying... -/
example : (dup.interp typeBase) () (3 : ℕ) = ((3 : ℕ), (3 : ℕ)) := rfl

/-- ...and `curryTerm` means currying. -/
example : (curryTerm (.base 0) (.base 0) (.base 0)).interp typeBase ()
    (fun (p : ℕ × ℕ) => p.1 + p.2) (2 : ℕ) (3 : ℕ) = (5 : ℕ) := rfl

/-- In `Type`, the β-law holds by computation alone: the meaning of a redex
*is* the meaning of the body in the extended environment. -/
example {Γ σ τ} (t : Term (σ :: Γ) τ) (a : Term Γ σ) (ρ : Ctx.interp typeBase Γ) :
    (Term.app (.lam t) a).interp typeBase ρ = t.interp typeBase (ρ, a.interp typeBase ρ) :=
  rfl
-- ANCHOR_END: type_model

-- ANCHOR: prop_model
/-- Three propositions as base types, in the thin category of `Prop`. -/
def propBase (p q r : Prop) : ℕ → Thin Prop
  | 0 => ⟨p⟩
  | 1 => ⟨q⟩
  | _ => ⟨r⟩

/-- The same term `swap`, interpreted in the Heyting algebra `Prop`: a proof
that `p ∧ q` implies `q ∧ p`. -/
example (p q : Prop) : p ∧ q → q ∧ p :=
  (swap.interp (propBase p q q)).down trivial

/-- `dup` becomes a proof of `p → p ∧ p`... -/
example (p : Prop) : p → p ∧ p :=
  (dup.interp (propBase p p p)).down trivial

/-- ...and `curryTerm` a proof of `((p ∧ q) → r) → p → q → r`. -/
example (p q r : Prop) : ((p ∧ q) → r) → p → q → r :=
  ((curryTerm (.base 0) (.base 1) (.base 2)).interp (propBase p q r)).down trivial
-- ANCHOR_END: prop_model

end Ch19.STLC
