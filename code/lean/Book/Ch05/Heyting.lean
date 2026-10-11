import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Book.Ch04.Deep

/-!
# Chapter 5 · Heyting algebras

A `HeytingAlgebra` class built from scratch (only the notation classes `LE`,
`Min`, `Max`, `HImp`, `Top`, `Bot` are borrowed from Lean and Mathlib), general
laws proved from the axioms, the two-element and three-element instances, and
soundness of the natural deduction of Chapter 4 in every Heyting algebra. The
three-element chain refutes excluded middle and double-negation elimination.
Then Mathlib's `HeytingAlgebra`, of which `Prop` is an instance.
-/

namespace Ch05

open Ch04

-- ANCHOR: class
/-- A Heyting algebra: a bounded lattice with an implication `⇨` that is
related to `⊓` by residuation. (Inside `namespace Ch05` this name shadows
Mathlib's `HeytingAlgebra`, which we meet at the end of the file.) -/
class HeytingAlgebra (H : Type) extends LE H, Min H, Max H, HImp H, Top H, Bot H where
  -- `≤` is a partial order
  le_refl : ∀ a : H, a ≤ a
  le_trans : ∀ a b c : H, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : H, a ≤ b → b ≤ a → a = b
  -- `a ⊓ b` is the greatest lower bound ("and")
  inf_le_left : ∀ a b : H, a ⊓ b ≤ a
  inf_le_right : ∀ a b : H, a ⊓ b ≤ b
  le_inf : ∀ a b c : H, a ≤ b → a ≤ c → a ≤ b ⊓ c
  -- `a ⊔ b` is the least upper bound ("or")
  le_sup_left : ∀ a b : H, a ≤ a ⊔ b
  le_sup_right : ∀ a b : H, b ≤ a ⊔ b
  sup_le : ∀ a b c : H, a ≤ c → b ≤ c → a ⊔ b ≤ c
  -- `⊥` is the least element ("false"), `⊤` the greatest ("true")
  bot_le : ∀ a : H, ⊥ ≤ a
  le_top : ∀ a : H, a ≤ ⊤
  -- residuation: `b ⇨ c` is the largest `a` with `a ⊓ b ≤ c` ("implies")
  le_himp_iff : ∀ a b c : H, a ≤ b ⇨ c ↔ a ⊓ b ≤ c
-- ANCHOR_END: class

-- ANCHOR: neg
/-- Negation is implication into the bottom element. -/
def neg {H : Type} [HeytingAlgebra H] (a : H) : H := a ⇨ ⊥
-- ANCHOR_END: neg

/-! ## Soundness of natural deduction in every Heyting algebra -/

-- ANCHOR: interp
/-- The value of a formula in a Heyting algebra, given a value for each atom. -/
def interp {H : Type} [HeytingAlgebra H] (f : Nat → H) : Formula → H
  | .var n   => f n
  | .top     => ⊤
  | .bot     => ⊥
  | .and A B => interp f A ⊓ interp f B
  | .or A B  => interp f A ⊔ interp f B
  | .imp A B => interp f A ⇨ interp f B

/-- A context is the meet of its formulas (the empty context is `⊤`). -/
def interpCtx {H : Type} [HeytingAlgebra H] (f : Nat → H) : List Formula → H
  | []     => ⊤
  | A :: Γ => interp f A ⊓ interpCtx f Γ
-- ANCHOR_END: interp

namespace HeytingAlgebra

variable {H : Type} [HeytingAlgebra H]

/-! Inside this namespace, `le_trans`, `le_himp_iff`, ... refer to the fields
of our class, not to Mathlib's lemmas of the same names. -/

-- ANCHOR: laws
/-- Meet is commutative (as an inequality; equality follows by antisymmetry). -/
theorem inf_comm_le (a b : H) : a ⊓ b ≤ b ⊓ a :=
  le_inf _ _ _ (inf_le_right a b) (inf_le_left a b)

/-- Modus ponens: `(a ⇨ b) ⊓ a ≤ b`. Residuation, read from right to left,
applied to `a ⇨ b ≤ a ⇨ b`. -/
theorem himp_inf_le (a b : H) : (a ⇨ b) ⊓ a ≤ b :=
  (le_himp_iff _ _ _).mp (le_refl _)

/-- `a ≤ ¬¬a`: unfolding, `a ≤ (a ⇨ ⊥) ⇨ ⊥`, which by residuation is
`a ⊓ (a ⇨ ⊥) ≤ ⊥`, modus ponens after swapping the meet. -/
theorem le_neg_neg (a : H) : a ≤ neg (neg a) :=
  (le_himp_iff _ _ _).mpr
    (le_trans _ _ _ (inf_comm_le _ _) (himp_inf_le a ⊥))

/-- Negation reverses the order. -/
theorem neg_anti {a b : H} (h : a ≤ b) : neg b ≤ neg a :=
  (le_himp_iff _ _ _).mpr
    (le_trans _ _ _
      (le_inf _ _ _ (inf_le_left _ _) (le_trans _ _ _ (inf_le_right _ _) h))
      (himp_inf_le b ⊥))

/-- Triple negation collapses: `¬¬¬a = ¬a`. -/
theorem neg_neg_neg (a : H) : neg (neg (neg a)) = neg a :=
  le_antisymm _ _ (neg_anti (le_neg_neg a)) (le_neg_neg (neg a))

/-- Non-contradiction: `a ⊓ ¬a ≤ ⊥`. -/
theorem inf_neg_le_bot (a : H) : a ⊓ neg a ≤ ⊥ :=
  le_trans _ _ _ (inf_comm_le _ _) (himp_inf_le a ⊥)
-- ANCHOR_END: laws

-- ANCHOR: distrib
/-- Every Heyting algebra is distributive. By residuation it suffices to
show `a ⊔ b ≤ c ⇨ d` for `d = (a ⊓ c) ⊔ (b ⊓ c)`, and a join is below
something when both parts are. -/
theorem sup_inf_le (a b c : H) : (a ⊔ b) ⊓ c ≤ (a ⊓ c) ⊔ (b ⊓ c) := by
  apply (le_himp_iff _ _ _).mp
  apply sup_le
  · exact (le_himp_iff _ _ _).mpr (le_sup_left _ _)
  · exact (le_himp_iff _ _ _).mpr (le_sup_right _ _)
-- ANCHOR_END: distrib

-- ANCHOR: heyting_soundness
/-- **Soundness.** If `Γ ⊢ A` then `⟦Γ⟧ ≤ ⟦A⟧` in every Heyting algebra, for
every interpretation of the atoms. -/
theorem soundness {Γ : List Formula} {A : Formula} (h : Proves Γ A) :
    ∀ {H : Type} [HeytingAlgebra H] (f : Nat → H), interpCtx f Γ ≤ interp f A := by
  induction h with
  | hyp hmem =>
    intro H _ f
    induction hmem with
    | head => exact inf_le_left _ _
    | tail _ _ ih => exact le_trans _ _ _ (inf_le_right _ _) ih
  | topI => intro H _ f; exact le_top _
  | botE _ ih => intro H _ f; exact le_trans _ _ _ (ih f) (bot_le _)
  | andI _ _ ih₁ ih₂ => intro H _ f; exact le_inf _ _ _ (ih₁ f) (ih₂ f)
  | andE1 _ ih => intro H _ f; exact le_trans _ _ _ (ih f) (inf_le_left _ _)
  | andE2 _ ih => intro H _ f; exact le_trans _ _ _ (ih f) (inf_le_right _ _)
  | orI1 _ ih => intro H _ f; exact le_trans _ _ _ (ih f) (le_sup_left _ _)
  | orI2 _ ih => intro H _ f; exact le_trans _ _ _ (ih f) (le_sup_right _ _)
  | orE _ _ _ ih ihA ihB =>
    -- ⟦Γ⟧ ≤ (a ⊔ b) ⊓ ⟦Γ⟧ ≤ (a ⊓ ⟦Γ⟧) ⊔ (b ⊓ ⟦Γ⟧) ≤ c
    intro H _ f
    apply le_trans _ _ _ (le_inf _ _ _ (ih f) (le_refl _))
    apply le_trans _ _ _ (sup_inf_le _ _ _)
    exact sup_le _ _ _ (ihA f) (ihB f)
  | impI _ ih =>
    -- residuation turns `a ⊓ ⟦Γ⟧ ≤ b` into `⟦Γ⟧ ≤ a ⇨ b`
    intro H _ f
    apply (le_himp_iff _ _ _).mpr
    exact le_trans _ _ _ (inf_comm_le _ _) (ih f)
  | impE _ _ ih₁ ih₂ =>
    -- ⟦Γ⟧ ≤ (a ⇨ b) ⊓ a ≤ b
    intro H _ f
    exact le_trans _ _ _ (le_inf _ _ _ (ih₁ f) (ih₂ f)) (himp_inf_le _ _)
-- ANCHOR_END: heyting_soundness

end HeytingAlgebra

/-! ## Two instances -/

-- ANCHOR: bool
/-- The two-element Heyting algebra: the truth values. `a ⇨ b` is `!a || b`. -/
instance : HeytingAlgebra Bool where
  le a b := a = true → b = true
  min a b := a && b
  max a b := a || b
  himp a b := !a || b
  top := true
  bot := false
  -- Each law is checked on every combination of elements: up to 27 cases.
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  bot_le a := by cases a <;> decide
  le_top a := by cases a <;> decide
  le_himp_iff a b c := by cases a <;> cases b <;> cases c <;> decide
-- ANCHOR_END: bool

-- ANCHOR: three
/-- The three-element chain `0 < ½ < 1`: "false", "undecided", "true". -/
inductive Three where
  | zero | half | one
  deriving DecidableEq, Repr

/-- The position of an element in the chain. -/
def Three.rank : Three → Nat
  | .zero => 0
  | .half => 1
  | .one  => 2

/-- In a chain, `a ⇨ b` is `1` when `a ≤ b`, and `b` otherwise. -/
instance : HeytingAlgebra Three where
  le a b := a.rank ≤ b.rank
  min a b := if a.rank ≤ b.rank then a else b
  max a b := if a.rank ≤ b.rank then b else a
  himp a b := if a.rank ≤ b.rank then .one else b
  top := .one
  bot := .zero
  -- Each law is checked on every combination of elements: up to 27 cases.
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide
  le_inf a b c := by cases a <;> cases b <;> cases c <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le a b c := by cases a <;> cases b <;> cases c <;> decide
  bot_le a := by cases a <;> decide
  le_top a := by cases a <;> decide
  le_himp_iff a b c := by cases a <;> cases b <;> cases c <;> decide
-- ANCHOR_END: three

-- ANCHOR: three_facts
/-- info: Ch05.Three.zero -/
#guard_msgs in
#eval neg Three.half

/-- info: Ch05.Three.one -/
#guard_msgs in
#eval neg (neg Three.half)

/-- Excluded middle fails at `½`: `½ ⊔ ¬½ = ½ ⊔ 0 = ½`, not `1`. -/
example : Three.half ⊔ neg Three.half ≠ ⊤ := by decide

/-- Double-negation elimination fails at `½`: `¬¬½ = 1`, which is not `≤ ½`. -/
example : ¬ (neg (neg Three.half) ≤ Three.half) := by decide

/-- In `Bool`, both hold for every element. -/
example : ∀ a : Bool, a ⊔ neg a = ⊤ ∧ neg (neg a) = a := by decide
-- ANCHOR_END: three_facts

-- ANCHOR: three_soundness
/-- A second proof that excluded middle is not derivable, this time
algebraic: interpret the atom `P` as `½`. -/
theorem lem_not_derivable' : ¬ Proves [] (.or P P.neg) := by
  intro h
  have := HeytingAlgebra.soundness h (fun _ => Three.half)
  revert this
  decide
-- ANCHOR_END: three_soundness

/-! ## In Mathlib -/

-- ANCHOR: mathlib
/-- Mathlib's class states residuation in the same form as ours. -/
example {α : Type} [_root_.HeytingAlgebra α] (a b c : α) :
    a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  le_himp_iff

/-- `Prop` is a Heyting algebra: `≤` is `→`, `⊓` is `∧`, `⊔` is `∨`, `⇨` is
`→`, and the complement `ᶜ` is `¬`. All of these hold by `rfl`. -/
example (p q : Prop) : (p ≤ q) = (p → q) := rfl
example (p q : Prop) : (p ⊓ q) = (p ∧ q) := rfl
example (p q : Prop) : (p ⊔ q) = (p ∨ q) := rfl
example (p q : Prop) : (p ⇨ q) = (p → q) := rfl
example (p : Prop) : pᶜ = ¬p := rfl

/-- The general laws we proved by hand are in Mathlib too. -/
example {α : Type} [_root_.HeytingAlgebra α] (a : α) : a ≤ aᶜᶜ := le_compl_compl
example {α : Type} [_root_.HeytingAlgebra α] (a : α) : aᶜᶜᶜ = aᶜ := compl_compl_compl a
-- ANCHOR_END: mathlib

-- ANCHOR: mathlib_bool
/-- Excluded middle holds in every Boolean algebra... -/
theorem em_boolean {α : Type} [BooleanAlgebra α] (a : α) : a ⊔ aᶜ = ⊤ :=
  sup_compl_eq_top

/-- ...and Mathlib makes `Prop` a Boolean algebra, using classical logic. -/
theorem em_prop (p : Prop) : p ⊔ pᶜ = ⊤ := em_boolean p

/-- info: 'Ch05.em_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms em_prop
-- ANCHOR_END: mathlib_bool

end Ch05
