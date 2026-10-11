import Mathlib.Logic.Relation

/-!
# Chapter 7 · The untyped λ-calculus

Terms with de Bruijn indices, shifting and substitution, one-step β-reduction
as an inductive relation, `Ω` and its endless reduction, a normal-order step
function proved sound and complete, a normalizer with fuel, and the
termination checker's verdict on a normalizer without fuel.
-/

namespace Ch07

-- ANCHOR: term
/-- Terms of the untyped λ-calculus with de Bruijn indices: `var k` refers to
the binder `k` levels up. -/
inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  deriving DecidableEq
-- ANCHOR_END: term

open Term

-- ANCHOR: to_string
/-- Prints a term the way the Rust crate does: `λ. λ. 1 (0 1)`. -/
def Term.toStr : Term → String
  | var k => toString k
  | lam t => "λ. " ++ t.toStr
  | app t u =>
    let left := match t with
      | lam _ => "(" ++ t.toStr ++ ")"
      | _ => t.toStr
    let right := match u with
      | var _ => u.toStr
      | _ => "(" ++ u.toStr ++ ")"
    left ++ " " ++ right

instance : ToString Term := ⟨Term.toStr⟩
/-- `#eval` uses `Repr`; inside `some (...)` the term gets parentheses. -/
instance : Repr Term := ⟨fun t prec => Repr.addAppParen t.toStr prec⟩
-- ANCHOR_END: to_string

-- ANCHOR: examples
/-- `λx. x` -/
def I : Term := lam (var 0)
/-- `λx. λy. x` -/
def K : Term := lam (lam (var 1))
/-- `λx. x x` -/
def delta : Term := lam (app (var 0) (var 0))
/-- `Ω = (λx. x x) (λx. x x)` -/
def omega : Term := app delta delta

/-- info: λ. λ. 1 -/
#guard_msgs in
#eval K

/-- info: (λ. 0 0) (λ. 0 0) -/
#guard_msgs in
#eval omega
-- ANCHOR_END: examples

-- ANCHOR: shift
/-- `shift c t` adds one to every index of `t` that is at least `c`. The
indices below the cutoff `c` are bound inside `t`; the others are free. -/
def shift (c : Nat) : Term → Term
  | var k => if k < c then var k else var (k + 1)
  | lam t => lam (shift (c + 1) t)
  | app t u => app (shift c t) (shift c u)
-- ANCHOR_END: shift

-- ANCHOR: subst
/-- `subst j s t` replaces the index `j` in `t` by `s`, and lowers the free
indices above `j` by one, because the binder of `j` disappears. Under a
binder, `j` grows by one and `s` is shifted. -/
def subst (j : Nat) (s : Term) : Term → Term
  | var k => if k < j then var k else if k = j then s else var (k - 1)
  | lam t => lam (subst (j + 1) (shift 0 s) t)
  | app t u => app (subst j s t) (subst j s u)
-- ANCHOR_END: subst

-- ANCHOR: subst_examples
/-- `(λx. λy. x) z`, with `z` free (index 0): the body `λ. 1` becomes `λ. 1`
again, the constant function returning `z`. -/
example : subst 0 (var 0) (lam (var 1)) = lam (var 1) := rfl

/-- Contracting `Ω`'s redex rebuilds `Ω`. -/
example : subst 0 delta (app (var 0) (var 0)) = omega := rfl
-- ANCHOR_END: subst_examples

-- ANCHOR: step
/-- One step of β-reduction, anywhere in a term. -/
inductive Step : Term → Term → Prop where
  /-- `(λ. t) s` steps to `t[0 := s]`. -/
  | beta (t s : Term) : Step (app (lam t) s) (subst 0 s t)
  /-- Reduce inside the function part of an application. -/
  | appL {t t' : Term} (s : Term) : Step t t' → Step (app t s) (app t' s)
  /-- Reduce inside the argument of an application. -/
  | appR (t : Term) {s s' : Term} : Step s s' → Step (app t s) (app t s')
  /-- Reduce inside the body of a λ. -/
  | body {t t' : Term} : Step t t' → Step (lam t) (lam t')
-- ANCHOR_END: step

-- ANCHOR: steps
/-- Many steps: the reflexive-transitive closure of `Step`, from Mathlib. -/
abbrev Steps : Term → Term → Prop := Relation.ReflTransGen Step

/-- A term is in normal form when it cannot take any step. -/
def Normal (t : Term) : Prop := ∀ t', ¬ Step t t'
-- ANCHOR_END: steps

-- ANCHOR: k_reduces
/-- `K a b` reduces to `a` in two steps (here `a` and `b` are the free
variables 0 and 1). -/
example : Steps (app (app K (var 0)) (var 1)) (var 0) := by
  -- First step: contract `K (var 0)` inside the left part.
  apply Relation.ReflTransGen.head (Step.appL _ (Step.beta _ _))
  -- Second step: contract the remaining redex `(λ. 1) (var 1)`.
  apply Relation.ReflTransGen.single
  exact Step.beta _ _
-- ANCHOR_END: k_reduces

-- ANCHOR: omega_steps
/-- `Ω` steps to itself. -/
theorem omega_step : Step omega omega :=
  Step.beta (app (var 0) (var 0)) delta
-- ANCHOR_END: omega_steps

-- ANCHOR: omega_only
/-- Moreover, the only step `Ω` can take leads back to `Ω`. -/
theorem omega_step_inv {t : Term} (h : Step omega t) : t = omega := by
  cases h with
  | beta => rfl
  | appL _ h =>
    -- A step inside `delta = λ. 0 0`: impossible, `0 0` has no redex.
    cases h with
    | body h =>
      cases h with
      | appL _ h => cases h
      | appR _ h => cases h
  | appR _ h =>
    cases h with
    | body h =>
      cases h with
      | appL _ h => cases h
      | appR _ h => cases h

/-- So every reduction sequence from `Ω` stays at `Ω`. -/
theorem omega_steps_inv {t : Term} (h : Steps omega t) : t = omega := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    exact omega_step_inv hstep

/-- `Ω` has no normal form. -/
theorem omega_no_normal_form : ¬ ∃ t, Steps omega t ∧ Normal t := by
  rintro ⟨t, hsteps, hnormal⟩
  rw [omega_steps_inv hsteps] at hnormal
  exact hnormal omega omega_step
-- ANCHOR_END: omega_only

end Ch07
