import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Tauto

/-!
# Chapter 27 · Variance

The four variances, their composition (a commutative monoid) and their
combination (a meet), with a meaning: a variance transforms a relation, and
composition of variances is composition of the transformations. Then a small
language of Rust-like types with one lifetime parameter, the variance that the
compiler infers for each type, and the theorem that the inference is sound:
if a type is covariant in `'x`, lengthening `'x` gives a subtype, and so on.
-/

namespace Ch27

-- ANCHOR: variance
/-- How a type depends on a parameter. -/
inductive Variance where
  | co      -- covariant: a longer parameter gives a subtype
  | contra  -- contravariant: a shorter parameter gives a subtype
  | inv     -- invariant: only the same parameter
  | bi      -- bivariant: the parameter does not matter
  deriving DecidableEq, Repr
-- ANCHOR_END: variance

namespace Variance

-- ANCHOR: mul
/-- `v * w` is the variance of a position of variance `w` nested inside a
position of variance `v`: like signs, two contravariances make a covariance. -/
def mul : Variance → Variance → Variance
  | bi, _ => bi
  | _, bi => bi
  | inv, _ => inv
  | _, inv => inv
  | co, w => w
  | contra, co => contra
  | contra, contra => co

instance : Mul Variance := ⟨mul⟩
instance : One Variance := ⟨co⟩
-- ANCHOR_END: mul

-- ANCHOR: meet
/-- Two occurrences of a parameter, with variances `v` and `w`: the parameter
may vary only in ways that both allow. -/
def meet : Variance → Variance → Variance
  | bi, w => w
  | v, bi => v
  | co, co => co
  | contra, contra => contra
  | _, _ => inv

@[inherit_doc] scoped infixl:65 " ⊓ " => meet
-- ANCHOR_END: meet

-- ANCHOR: monoid
/-- Composition of variances is associative, commutative, and `co` is its
unit: the variances form a commutative monoid. -/
instance : CommMonoid Variance where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

/-- info: Ch27.Variance.co -/
#guard_msgs in
#eval contra * contra

/-- info: Ch27.Variance.contra -/
#guard_msgs in
#eval contra ^ 3

/-- info: Ch27.Variance.inv -/
#guard_msgs in
#eval co ⊓ contra
-- ANCHOR_END: monoid

-- ANCHOR: apply
/-- The meaning of a variance: how it transforms a relation `R` on parameters
(for us, "outlives" on lifetimes) into a relation on parameters that is safe
to use for the type. -/
def apply {α : Type} : Variance → (α → α → Prop) → (α → α → Prop)
  | co, R => R
  | contra, R => fun a b => R b a
  | inv, R => fun a b => R a b ∧ R b a
  | bi, _ => fun _ _ => True
-- ANCHOR_END: apply

-- ANCHOR: apply_mul
/-- Composing variances is composing their meanings. -/
theorem apply_mul {α : Type} (v w : Variance) (R : α → α → Prop) (a b : α) :
    (v * w).apply R a b ↔ v.apply (w.apply R) a b := by
  cases v <;> cases w <;> simp [HMul.hMul, Mul.mul, mul, apply] <;> tauto

/-- Meeting variances is intersecting their meanings. -/
theorem apply_meet {α : Type} (v w : Variance) (R : α → α → Prop) (a b : α) :
    (v ⊓ w).apply R a b ↔ v.apply R a b ∧ w.apply R a b := by
  cases v <;> cases w <;> simp [meet, apply] <;> tauto
-- ANCHOR_END: apply_mul

end Variance

open Variance

/-! ## Variance inference for Rust-like types -/

-- ANCHOR: rty
/-- Rust-like types whose lifetimes are drawn from `L`. -/
inductive RTy (L : Type) where
  | i32
  | ref (a : L) (t : RTy L)       -- &'a T
  | refMut (a : L) (t : RTy L)    -- &'a mut T
  | fn (arg res : RTy L)          -- fn(T) -> U
  | cell (t : RTy L)              -- Cell<T>
  | box (t : RTy L)               -- Box<T>
  | pair (t u : RTy L)            -- a struct with two fields
  deriving Repr

/-- A lifetime in a type with one parameter: the parameter `'x`, or a fixed
scope, named by the point where it ends. -/
inductive Lft where
  | x
  | scope (n : ℕ)
  deriving Repr
-- ANCHOR_END: rty

-- ANCHOR: rsub
/-- Subtyping on closed types, whose lifetimes are end points: `'a` outlives
`'b` when `b ≤ a`. -/
inductive RSub : RTy ℕ → RTy ℕ → Prop where
  | refl (t : RTy ℕ) : RSub t t
  | trans {t u w : RTy ℕ} : RSub t u → RSub u w → RSub t w
  | ref {a b : ℕ} {t u : RTy ℕ} : b ≤ a → RSub t u → RSub (.ref a t) (.ref b u)
  | refMut {a b : ℕ} {t u : RTy ℕ} :
      b ≤ a → RSub t u → RSub u t → RSub (.refMut a t) (.refMut b u)
  | fn {t t' u u' : RTy ℕ} : RSub t' t → RSub u u' → RSub (.fn t u) (.fn t' u')
  | cell {t u : RTy ℕ} : RSub t u → RSub u t → RSub (.cell t) (.cell u)
  | box {t u : RTy ℕ} : RSub t u → RSub (.box t) (.box u)
  | pair {t t' u u' : RTy ℕ} : RSub t t' → RSub u u' → RSub (.pair t u) (.pair t' u')
-- ANCHOR_END: rsub

-- ANCHOR: infer
/-- The variance of a type in its lifetime parameter `'x`. -/
def Lft.var : Lft → Variance
  | .x => co
  | .scope _ => bi

/-- The variance of a type in `'x`: the meet over every occurrence of `'x`,
each weighted by the variances of the positions it sits in. -/
def RTy.var : RTy Lft → Variance
  | .i32 => bi
  | .ref a t => a.var ⊓ (co * t.var)
  | .refMut a t => a.var ⊓ (inv * t.var)
  | .fn t u => (contra * t.var) ⊓ (co * u.var)
  | .cell t => inv * t.var
  | .box t => co * t.var
  | .pair t u => t.var ⊓ u.var

/-- Replace the parameter `'x` by the scope ending at `a`. -/
def Lft.inst (a : ℕ) : Lft → ℕ
  | .x => a
  | .scope n => n

/-- Replace `'x` by the scope ending at `a` everywhere in a type. -/
def RTy.inst (a : ℕ) : RTy Lft → RTy ℕ
  | .i32 => .i32
  | .ref l t => .ref (l.inst a) (t.inst a)
  | .refMut l t => .refMut (l.inst a) (t.inst a)
  | .fn t u => .fn (t.inst a) (u.inst a)
  | .cell t => .cell (t.inst a)
  | .box t => .box (t.inst a)
  | .pair t u => .pair (t.inst a) (u.inst a)
-- ANCHOR_END: infer

-- ANCHOR: infer_eval
/-- `&'x i32` -/
def refX : RTy Lft := .ref .x .i32

/-- info: Ch27.Variance.co -/
#guard_msgs in
#eval refX.var

-- `&'s mut &'x i32`: the classic invariant position.
/-- info: Ch27.Variance.inv -/
#guard_msgs in
#eval (RTy.refMut (.scope 0) refX).var

-- `fn(&'x i32)` and `fn(fn(&'x i32))`
/-- info: Ch27.Variance.contra -/
#guard_msgs in
#eval (RTy.fn refX .i32).var

/-- info: Ch27.Variance.co -/
#guard_msgs in
#eval (RTy.fn (.fn refX .i32) .i32).var

-- `struct Holder<'x> { r: &'x i32, hits: Cell<i32> }`
/-- info: Ch27.Variance.co -/
#guard_msgs in
#eval (RTy.pair refX (.cell .i32)).var
-- ANCHOR_END: infer_eval

-- ANCHOR: infer_sound
/-- "`'a` outlives `'b`" on end points. -/
def Outlives (a b : ℕ) : Prop := b ≤ a

/-- **Variance inference is sound.** Whatever relation between `a` and `b` the
inferred variance asks for, instantiating `'x` with `a` gives a subtype of
instantiating it with `b`. -/
theorem RTy.var_sound (t : RTy Lft) :
    ∀ a b, t.var.apply Outlives a b → RSub (t.inst a) (t.inst b) := by
  induction t with
  | i32 => exact fun _ _ _ => RSub.refl _
  | ref l t ih =>
    intro a b h
    rw [RTy.var, apply_meet, apply_mul] at h
    obtain ⟨hl, ht⟩ := h
    apply RSub.ref _ (ih a b ht)
    -- The lifetime of the reference: `'x` itself, or a fixed scope.
    cases l with
    | x => exact hl
    | scope n => exact Nat.le_refl n
  | refMut l t ih =>
    intro a b h
    rw [RTy.var, apply_meet, apply_mul] at h
    -- Invariance gives both directions for the referent.
    obtain ⟨hl, ht₁, ht₂⟩ := h
    apply RSub.refMut _ (ih a b ht₁) (ih b a ht₂)
    cases l with
    | x => exact hl
    | scope n => exact Nat.le_refl n
  | fn t u iht ihu =>
    intro a b h
    rw [RTy.var, apply_meet, apply_mul, apply_mul] at h
    obtain ⟨ht, hu⟩ := h
    -- Contravariance swaps `a` and `b` for the argument.
    exact RSub.fn (iht b a ht) (ihu a b hu)
  | cell t ih =>
    intro a b h
    rw [RTy.var, apply_mul] at h
    exact RSub.cell (ih a b h.1) (ih b a h.2)
  | box t ih =>
    intro a b h
    rw [RTy.var, apply_mul] at h
    exact RSub.box (ih a b h)
  | pair t u iht ihu =>
    intro a b h
    rw [RTy.var, apply_meet] at h
    exact RSub.pair (iht a b h.1) (ihu a b h.2)
-- ANCHOR_END: infer_sound

-- ANCHOR: corollaries
/-- A covariant type: lengthening `'x` gives a subtype. -/
theorem RTy.covariant {t : RTy Lft} (h : t.var = co) {a b : ℕ} (hab : b ≤ a) :
    RSub (t.inst a) (t.inst b) :=
  t.var_sound a b (by rw [h]; exact hab)

/-- A contravariant type: *shortening* `'x` gives a subtype. -/
theorem RTy.contravariant {t : RTy Lft} (h : t.var = contra) {a b : ℕ}
    (hab : a ≤ b) : RSub (t.inst a) (t.inst b) :=
  t.var_sound a b (by rw [h]; exact hab)
-- ANCHOR_END: corollaries

end Ch27
