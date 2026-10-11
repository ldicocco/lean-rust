/-!
# Chapter 8 · An intrinsically typed simply typed λ-calculus

Terms indexed by their context and their type, so that only well-typed terms
exist; variables as typed positions in the context; a denotational evaluator
into Lean's own types that is total and cannot go wrong; β and η for the
evaluator.
-/

namespace Ch08

-- ANCHOR: ty
/-- The simple types: unit, booleans, naturals, functions, pairs and sums. -/
inductive Ty where
  | unit
  | bool
  | nat
  | arrow (σ τ : Ty)
  | prod (σ τ : Ty)
  | sum (σ τ : Ty)
  deriving DecidableEq, Repr

/-- `σ ⇒ τ` is the function type (scoped: it does not leak into other files). -/
scoped infixr:25 " ⇒ " => Ty.arrow
-- ANCHOR_END: ty

open Ty

-- ANCHOR: denote
/-- What a type means: the Lean type of its values. -/
@[reducible] def Ty.denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat
  | arrow σ τ => σ.denote → τ.denote
  | prod σ τ => σ.denote × τ.denote
  | sum σ τ => σ.denote ⊕ τ.denote
-- ANCHOR_END: denote

-- ANCHOR: var
/-- `Var Γ τ` is a variable of type `τ` in the context `Γ`: a position in the
list `Γ` where `τ` occurs. `here` is the most recent binding (de Bruijn index
0); `there x` skips one binding. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : List Ty} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ
-- ANCHOR_END: var

-- ANCHOR: term
/-- `Term Γ τ` is a term of type `τ` in the context `Γ`. Each constructor is
a typing rule; an ill-typed term cannot even be written down. -/
inductive Term : List Ty → Ty → Type where
  | var {Γ τ} : Var Γ τ → Term Γ τ
  | lam {Γ σ τ} : Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  | app {Γ σ τ} : Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  | unit {Γ} : Term Γ .unit
  | tt {Γ} : Term Γ .bool
  | ff {Γ} : Term Γ .bool
  | ite {Γ τ} : Term Γ .bool → Term Γ τ → Term Γ τ → Term Γ τ
  | zero {Γ} : Term Γ .nat
  | succ {Γ} : Term Γ .nat → Term Γ .nat
  | iter {Γ τ} : Term Γ .nat → Term Γ τ → Term Γ (τ ⇒ τ) → Term Γ τ
  | pair {Γ σ τ} : Term Γ σ → Term Γ τ → Term Γ (.prod σ τ)
  | fst {Γ σ τ} : Term Γ (.prod σ τ) → Term Γ σ
  | snd {Γ σ τ} : Term Γ (.prod σ τ) → Term Γ τ
  | inl {Γ σ τ} : Term Γ σ → Term Γ (.sum σ τ)
  | inr {Γ σ τ} : Term Γ τ → Term Γ (.sum σ τ)
  | case {Γ σ τ ρ} :
      Term Γ (.sum σ τ) → Term (σ :: Γ) ρ → Term (τ :: Γ) ρ → Term Γ ρ
-- ANCHOR_END: term

-- ANCHOR: env
/-- An environment for `Γ`: a value of the right type for every variable. -/
abbrev Env (Γ : List Ty) : Type := ∀ {τ : Ty}, Var Γ τ → τ.denote

/-- The empty environment. There are no variables to look up. -/
def Env.nil : Env [] := fun x => nomatch x

/-- Extend an environment with a value for the new variable `here`. -/
def Env.cons {Γ : List Ty} {σ : Ty} (v : σ.denote) (ρ : Env Γ) : Env (σ :: Γ)
  | _, .here => v
  | _, .there x => ρ x
-- ANCHOR_END: env

-- ANCHOR: iterate
/-- `iterate f n a` applies `f` to `a`, `n` times. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => f (iterate f n a)
-- ANCHOR_END: iterate

-- ANCHOR: eval
/-- The evaluator: every term of type `τ` denotes a Lean value of type
`τ.denote`. There is no error case and no fuel: Lean checks that every case
is covered and that the recursion terminates. -/
def Term.eval {Γ : List Ty} {τ : Ty} : Term Γ τ → Env Γ → τ.denote
  | .var x, ρ => ρ x
  | .lam b, ρ => fun v => b.eval (ρ.cons v)
  | .app f a, ρ => f.eval ρ (a.eval ρ)
  | .unit, _ => ()
  | .tt, _ => true
  | .ff, _ => false
  | .ite c a b, ρ => if c.eval ρ then a.eval ρ else b.eval ρ
  | .zero, _ => 0
  | .succ n, ρ => n.eval ρ + 1
  | .iter n z s, ρ => iterate (s.eval ρ) (n.eval ρ) (z.eval ρ)
  | .pair a b, ρ => (a.eval ρ, b.eval ρ)
  | .fst p, ρ => (p.eval ρ).1
  | .snd p, ρ => (p.eval ρ).2
  | .inl a, ρ => .inl (a.eval ρ)
  | .inr b, ρ => .inr (b.eval ρ)
  | .case s l r, ρ =>
    match s.eval ρ with
    | .inl v => l.eval (ρ.cons v)
    | .inr v => r.eval (ρ.cons v)
-- ANCHOR_END: eval

-- ANCHOR: examples
/-- The numeral `n` as a term: `succ (succ (... zero))`. -/
def lit {Γ : List Ty} : Nat → Term Γ .nat
  | 0 => .zero
  | n + 1 => .succ (lit n)

/-- `twice = λf. λx. f (f x)`. In the body, `f` is `there here` (one binder
up) and `x` is `here`. -/
def twice : Term [] ((nat ⇒ nat) ⇒ nat ⇒ nat) :=
  .lam (.lam (.app (.var (.there .here)) (.app (.var (.there .here)) (.var .here))))

/-- `add = λm. λn. iter m n (λk. succ k)` -/
def add : Term [] (nat ⇒ nat ⇒ nat) :=
  .lam (.lam (.iter (.var (.there .here)) (.var .here) (.lam (.succ (.var .here)))))

/-- `swap = λp. (snd p, fst p)` -/
def swap {σ τ : Ty} : Term [] (.prod σ τ ⇒ .prod τ σ) :=
  .lam (.pair (.snd (.var .here)) (.fst (.var .here)))

/-- `toNat = λs. case s of inl n => n | inr b => if b then 1 else 0` -/
def toNat : Term [] (.sum nat bool ⇒ nat) :=
  .lam (.case (.var .here) (.var .here) (.ite (.var .here) (lit 1) (lit 0)))
-- ANCHOR_END: examples

-- ANCHOR: run
/-- info: 10 -/
#guard_msgs in
#eval (Term.app (.app twice (.app add (lit 3))) (lit 4)).eval Env.nil

/-- The meaning of `twice` is a Lean function, which we can apply to Lean
functions. -/
example : twice.eval Env.nil (· * 3) 5 = 45 := rfl

/-- info: (true, 7) -/
#guard_msgs in
#eval (Term.app (swap (σ := nat) (τ := bool)) (.pair (lit 7) .tt)).eval Env.nil

/-- info: 1 -/
#guard_msgs in
#eval (Term.app toNat (.inr .tt)).eval Env.nil
-- ANCHOR_END: run

-- ANCHOR: ill_typed
/--
error: Application type mismatch: The argument
  Term.zero
has type
  Term ?m.5 nat
but is expected to have type
  Term [] (nat ⇒ nat)
in the application
  Term.zero.app
-/
#guard_msgs in
example : Term [] .nat := .app .zero .zero
-- ANCHOR_END: ill_typed

-- ANCHOR: self_app
/--
error: Application type mismatch: The argument
  Var.here
has type
  Var (?m.11 :: ?m.10) ?m.11
but is expected to have type
  Var [σ] (σ ⇒ τ)
in the application
  Term.var Var.here
-/
#guard_msgs in
example (σ τ : Ty) : Term [] (σ ⇒ τ) := .lam (.app (.var .here) (.var .here))
-- ANCHOR_END: self_app

-- ANCHOR: beta
/-- β holds in the semantics, by computation: applying a λ means evaluating its
body with the argument's value bound to the parameter. -/
theorem eval_beta {Γ : List Ty} {σ τ : Ty} (b : Term (σ :: Γ) τ) (a : Term Γ σ)
    (ρ : Env Γ) : (Term.app (.lam b) a).eval ρ = b.eval (ρ.cons (a.eval ρ)) :=
  rfl

/-- So do the β-rules of the other types. -/
example {Γ : List Ty} {σ τ : Ty} (a : Term Γ σ) (b : Term Γ τ) (ρ : Env Γ) :
    (Term.fst (.pair a b)).eval ρ = a.eval ρ := rfl

example {Γ : List Ty} {τ : Ty} (z : Term Γ τ) (s : Term Γ (τ ⇒ τ)) (ρ : Env Γ) :
    (Term.iter .zero z s).eval ρ = z.eval ρ := rfl
-- ANCHOR_END: beta

-- ANCHOR: rename
/-- A renaming sends each variable of `Γ` to a variable of `Δ` with the same
type. -/
abbrev Ren (Γ Δ : List Ty) : Type := ∀ {τ : Ty}, Var Γ τ → Var Δ τ

/-- Going under a binder: the new variable stays `here`, the others move as
before, one position further out. -/
def Ren.ext {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ)
  | _, .here => .here
  | _, .there x => .there (r x)

/-- Apply a renaming to every variable of a term. -/
def Term.rename {Γ Δ : List Ty} (r : Ren Γ Δ) {τ : Ty} : Term Γ τ → Term Δ τ
  | .var x => .var (r x)
  | .lam b => .lam (b.rename r.ext)
  | .app f a => .app (f.rename r) (a.rename r)
  | .unit => .unit
  | .tt => .tt
  | .ff => .ff
  | .ite c a b => .ite (c.rename r) (a.rename r) (b.rename r)
  | .zero => .zero
  | .succ n => .succ (n.rename r)
  | .iter n z s => .iter (n.rename r) (z.rename r) (s.rename r)
  | .pair a b => .pair (a.rename r) (b.rename r)
  | .fst p => .fst (p.rename r)
  | .snd p => .snd (p.rename r)
  | .inl a => .inl (a.rename r)
  | .inr b => .inr (b.rename r)
  | .case e l rr => .case (e.rename r) (l.rename r.ext) (rr.rename r.ext)

/-- Weakening: a term of `Γ` is also a term of `σ :: Γ`. -/
def Term.weaken {Γ : List Ty} {σ τ : Ty} (t : Term Γ τ) : Term (σ :: Γ) τ :=
  t.rename Var.there
-- ANCHOR_END: rename

-- ANCHOR: eval_rename
/-- Evaluating a renamed term in `ρ` is evaluating the original term in an
environment `ρ'` that agrees with `ρ` through the renaming. -/
theorem eval_rename {Γ Δ : List Ty} {τ : Ty} (t : Term Γ τ) (r : Ren Γ Δ)
    (ρ : Env Δ) (ρ' : Env Γ) (h : ∀ {σ : Ty} (x : Var Γ σ), ρ' x = ρ (r x)) :
    (t.rename r).eval ρ = t.eval ρ' := by
  -- Under a binder, the extended environments still agree.
  have ext {σ : Ty} (v : σ.denote) {Γ Δ : List Ty} (r : Ren Γ Δ) (ρ : Env Δ)
      (ρ' : Env Γ) (h : ∀ {σ : Ty} (x : Var Γ σ), ρ' x = ρ (r x)) :
      ∀ {σ' : Ty} (x : Var (σ :: Γ) σ'), (ρ'.cons v) x = (ρ.cons v) (r.ext x) := by
    intro σ' x
    cases x with
    | here => rfl
    | there x => exact h x
  induction t generalizing Δ with
  | var x => exact (h x).symm
  | lam b ih =>
    funext v
    exact ih r.ext (ρ.cons v) (ρ'.cons v) (ext v r ρ ρ' h)
  | case e l rr ihe ihl ihr =>
    simp only [Term.rename, Term.eval, ihe r ρ ρ' h]
    split
    · exact ihl r.ext _ _ (ext _ r ρ ρ' h)
    · exact ihr r.ext _ _ (ext _ r ρ ρ' h)
  -- The remaining cases: rename the subterms, then use the induction
  -- hypotheses (`ih r ρ ρ' h` rewrites a renamed subterm's value).
  | app f a ihf iha => simp only [Term.rename, Term.eval, ihf r ρ ρ' h, iha r ρ ρ' h]
  | ite c a b ihc iha ihb =>
    simp only [Term.rename, Term.eval, ihc r ρ ρ' h, iha r ρ ρ' h, ihb r ρ ρ' h]
  | succ n ih => simp only [Term.rename, Term.eval, ih r ρ ρ' h]
  | iter n z s ihn ihz ihs =>
    simp only [Term.rename, Term.eval, ihn r ρ ρ' h, ihz r ρ ρ' h, ihs r ρ ρ' h]
  | pair a b iha ihb => simp only [Term.rename, Term.eval, iha r ρ ρ' h, ihb r ρ ρ' h]
  | fst p ih => simp only [Term.rename, Term.eval, ih r ρ ρ' h]
  | snd p ih => simp only [Term.rename, Term.eval, ih r ρ ρ' h]
  | inl a ih => simp only [Term.rename, Term.eval, ih r ρ ρ' h]
  | inr b ih => simp only [Term.rename, Term.eval, ih r ρ ρ' h]
  | unit | tt | ff | zero => rfl
-- ANCHOR_END: eval_rename

-- ANCHOR: eta
/-- η holds in the semantics: `λx. f x` means the same as `f` (when `x` is
not free in `f`, which the weakening guarantees). -/
theorem eval_eta {Γ : List Ty} {σ τ : Ty} (f : Term Γ (σ ⇒ τ)) (ρ : Env Γ) :
    (Term.lam (.app f.weaken (.var .here))).eval ρ = f.eval ρ := by
  funext v
  -- After unfolding `eval`: (f.weaken).eval (ρ.cons v) v = f.eval ρ v.
  show (f.rename Var.there).eval (ρ.cons v) v = f.eval ρ v
  rw [eval_rename f Var.there (ρ.cons v) ρ (fun _ => rfl)]
-- ANCHOR_END: eta

end Ch08
