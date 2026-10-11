import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.EquivFin

/-!
# Chapter 12 · Church encodings in Lean

System F's Church encodings, written with Lean's dependent function types:
numerals `(α : Type) → (α → α) → α → α` (which live in `Type 1`), arithmetic on
them with proofs that it agrees with `ℕ`, the predicativity wall and how a
universe-polymorphic definition climbs over it, booleans and pairs, rank-2
functions as ordinary functions, impredicative encodings of the connectives in
`Prop`, and a non-standard numeral built with classical logic.
-/

namespace Ch12

-- ANCHOR: church
/-- Church numerals: the number `n` is "apply `f` to `x`, `n` times", for every
type `α`. The `∀α` makes it a type of `Type 1`. (`abbrev` is a definition that
Lean unfolds freely, like a `type` alias in Rust.) -/
abbrev Church : Type 1 := (α : Type) → (α → α) → α → α

namespace Church

def zero : Church := fun _ _ x => x
def succ (n : Church) : Church := fun α f x => f (n α f x)
def add (m n : Church) : Church := fun α f x => m α f (n α f x)
def mul (m n : Church) : Church := fun α f => m α (n α f)

/-- Read a numeral back: instantiate `α := ℕ`, `f := (· + 1)`, `x := 0`. -/
def toNat (n : Church) : ℕ := n ℕ (· + 1) 0

def ofNat : ℕ → Church
  | 0 => zero
  | k + 1 => succ (ofNat k)
-- ANCHOR_END: church

-- ANCHOR: church_eval
/-- info: 7 -/
#guard_msgs in
#eval toNat (add (ofNat 3) (ofNat 4))

/-- info: 12 -/
#guard_msgs in
#eval toNat (mul (ofNat 3) (ofNat 4))

-- The same numeral used at another type: three times "append a bang".
/-- info: "go!!!" -/
#guard_msgs in
#eval ofNat 3 String (· ++ "!") "go"
-- ANCHOR_END: church_eval

-- ANCHOR: church_iterate
/-- The numeral `ofNat k` applies `f` exactly `k` times: `f^[k]` is Mathlib's
notation for the `k`-th iterate of `f`. -/
theorem ofNat_apply (k : ℕ) (α : Type) (f : α → α) (x : α) :
    ofNat k α f x = f^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    -- ofNat (k + 1) α f x = f (ofNat k α f x) = f (f^[k] x) = f^[k + 1] x
    show f (ofNat k α f x) = f^[k + 1] x
    rw [ih, Function.iterate_succ_apply']

/-- The same fact about the function itself (by function extensionality). -/
theorem ofNat_eq_iterate (k : ℕ) (α : Type) (f : α → α) : ofNat k α f = f^[k] :=
  funext (ofNat_apply k α f)

/-- Counting up from 0, `k` times, gives `k`. -/
theorem succ_iterate (k : ℕ) : (· + 1)^[k] 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]

theorem toNat_ofNat (k : ℕ) : toNat (ofNat k) = k := by
  unfold toNat
  rw [ofNat_apply, succ_iterate]
-- ANCHOR_END: church_iterate

-- ANCHOR: church_arith
/-- Church addition is addition. The two numerals are functions, so we prove
them equal with `funext`: they agree on every type, function and start value. -/
theorem add_ofNat (a b : ℕ) : add (ofNat a) (ofNat b) = ofNat (a + b) := by
  funext α f x
  -- Goal: ofNat a α f (ofNat b α f x) = ofNat (a + b) α f x
  simp only [add, ofNat_apply, Function.iterate_add_apply]

/-- Church multiplication is multiplication: `f^[b]` iterated `a` times is
`f^[b * a]`. -/
theorem mul_ofNat (a b : ℕ) : mul (ofNat a) (ofNat b) = ofNat (a * b) := by
  funext α f x
  simp only [mul, ofNat_apply, ofNat_eq_iterate]
  -- Goal: f^[b]^[a] x = f^[a * b] x
  rw [← Function.iterate_mul, Nat.mul_comm]
-- ANCHOR_END: church_arith

end Church

-- ANCHOR: predicativity_wall
/--
error: Application type mismatch: The argument
  Church
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  n Church
-/
#guard_msgs in
def Church.pow (m n : Church) : Church := n Church (Church.mul m) (Church.ofNat 1)
-- ANCHOR_END: predicativity_wall

-- ANCHOR: church_universe
universe u

/-- Universe-polymorphic numerals: one type of numerals for each level `u`. -/
abbrev ChurchU : Type (u + 1) := (α : Type u) → (α → α) → α → α

def ChurchU.ofNat : ℕ → ChurchU.{u}
  | 0 => fun _ _ x => x
  | k + 1 => fun α f x => f (ChurchU.ofNat k α f x)

def ChurchU.mul (m n : ChurchU.{u}) : ChurchU.{u} := fun α f => m α (n α f)

/-- Exponentiation `m ^ n`: the exponent `n` is a numeral of the level above,
so it can iterate over the type of numerals of level 0. -/
def ChurchU.pow (m : ChurchU.{0}) (n : ChurchU.{1}) : ChurchU.{0} :=
  n ChurchU.{0} (ChurchU.mul m) (ChurchU.ofNat 1)

/-- info: 81 -/
#guard_msgs in
#eval ChurchU.pow (ChurchU.ofNat 3) (ChurchU.ofNat 4) ℕ (· + 1) 0
-- ANCHOR_END: church_universe

-- ANCHOR: church_bool_pair
/-- Booleans: a boolean chooses between two alternatives. -/
abbrev CBool : Type 1 := (α : Type) → α → α → α
def ctrue : CBool := fun _ t _ => t
def cfalse : CBool := fun _ _ f => f
def cnot (b : CBool) : CBool := fun α t f => b α f t
def CBool.toBool (b : CBool) : Bool := b Bool true false

/-- Pairs: a pair is "give me a two-argument consumer, and I will feed it". -/
abbrev CPair (α β : Type) : Type 1 := (γ : Type) → (α → β → γ) → γ
def CPair.mk {α β : Type} (a : α) (b : β) : CPair α β := fun _ k => k a b
def CPair.fst {α β : Type} (p : CPair α β) : α := p α (fun a _ => a)
def CPair.snd {α β : Type} (p : CPair α β) : β := p β (fun _ b => b)

/-- info: false -/
#guard_msgs in
#eval (cnot ctrue).toBool

/-- info: (3, "three") -/
#guard_msgs in
#eval let p := CPair.mk 3 "three"; (p.fst, p.snd)
-- ANCHOR_END: church_bool_pair

-- ANCHOR: rank2
/-- A rank-2 function: its *argument* is polymorphic, and it uses that argument
at two different types. In Lean this is an ordinary dependent function. -/
def onBoth (f : {α : Type} → List α → List α) (xs : List ℕ) (ys : List String) :
    List ℕ × List String :=
  (f xs, f ys)

/-- info: ([3, 2, 1], ["b", "a"]) -/
#guard_msgs in
#eval onBoth List.reverse [1, 2, 3] ["a", "b"]

/-- info: ([1], ["a"]) -/
#guard_msgs in
#eval onBoth (List.take 1) [1, 2, 3] ["a", "b"]
-- ANCHOR_END: rank2

-- ANCHOR: impredicative_prop
/-- "p and q", encoded impredicatively: for every proposition r, if p and q
together give r, then r. This quantifies over all of `Prop`, and is a `Prop`. -/
def CAnd (p q : Prop) : Prop := ∀ r : Prop, (p → q → r) → r

/-- "p or q": for every r, if each of p and q gives r, then r. -/
def COr (p q : Prop) : Prop := ∀ r : Prop, (p → r) → (q → r) → r

/-- "false": every proposition holds. -/
def CFalse : Prop := ∀ r : Prop, r

theorem cand_iff (p q : Prop) : CAnd p q ↔ p ∧ q := by
  constructor
  · intro h
    -- instantiate r := p ∧ q and give the pairing function
    exact h (p ∧ q) (fun hp hq => ⟨hp, hq⟩)
  · intro ⟨hp, hq⟩ r k
    exact k hp hq

theorem cor_iff (p q : Prop) : COr p q ↔ p ∨ q := by
  constructor
  · intro h
    exact h (p ∨ q) Or.inl Or.inr
  · intro h r kp kq
    cases h with
    | inl hp => exact kp hp
    | inr hq => exact kq hq

theorem cfalse_iff : CFalse ↔ False := by
  constructor
  · intro h
    exact h False
  · intro h
    exact h.elim
-- ANCHOR_END: impredicative_prop

/-! ## A numeral that is not a numeral -/

-- ANCHOR: weird
/-- The natural numbers and the booleans are different types. -/
theorem nat_ne_bool : ℕ ≠ Bool := by
  intro h
  -- If they were equal, ℕ would be finite, like Bool.
  have : Finite ℕ := h ▸ inferInstance
  exact not_finite ℕ

open Classical in
/-- With classical logic we can ask "is α the type Bool?" and behave
differently: once on `Bool`, twice everywhere else. -/
noncomputable def weird : Church :=
  fun α f x => if α = Bool then f x else f (f x)

/-- `weird` is not `ofNat k` for any `k`: on `Bool` with `not` it acts like an
odd numeral, on `ℕ` with `(· + 1)` like the numeral 2. -/
theorem weird_ne_ofNat (k : ℕ) : weird ≠ Church.ofNat k := by
  intro h
  have hb := congrFun (congrFun (congrFun h Bool) not) true
  have hn := congrFun (congrFun (congrFun h ℕ) (· + 1)) 0
  -- hb : weird Bool not true = ofNat k Bool not true, and so on
  simp [weird, Church.ofNat_apply, nat_ne_bool] at hb hn
  -- hb : not^[k] true = false        hn : 2 = (fun x => x + 1)^[k] 0
  rw [Church.succ_iterate] at hn
  subst hn
  -- hb : not^[2] true = false, but not (not true) = true
  exact absurd hb (by decide)
-- ANCHOR_END: weird

end Ch12
