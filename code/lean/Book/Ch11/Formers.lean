import Mathlib.Data.Nat.Notation

/-!
# Chapter 11 · The type formers in Lean

Sums, products, the unit type and the empty type defined from scratch as
inductive types and structures, with their elimination rules, and Lean's
exhaustiveness check (the elimination rule for sums demands a case for every
constructor).
-/

namespace Ch11

-- ANCHOR: formers
/-- A + B: a value is built by `inl` from an `α` or by `inr` from a `β`. -/
inductive MySum (α β : Type) where
  | inl : α → MySum α β
  | inr : β → MySum α β

/-- A × B: one constructor with two fields. -/
structure MyProd (α β : Type) where
  fst : α
  snd : β

/-- 1: one constructor with no fields. -/
inductive MyUnit where
  | star : MyUnit

/-- 0: no constructors at all. -/
inductive MyEmpty : Type
-- ANCHOR_END: formers

-- ANCHOR: eliminators
/-- Rule +E: to use a sum, say what to do in each case. -/
def MySum.elim {α β γ : Type} (f : α → γ) (g : β → γ) : MySum α β → γ
  | .inl a => f a
  | .inr b => g b

/-- Rule 0E: from a value of the empty type, anything. There is no case to
write, and `nomatch` says so. -/
def MyEmpty.elim {γ : Type} (e : MyEmpty) : γ := nomatch e

/-- Rule ×E: the projections come with the structure; pattern matching works
too. -/
def MyProd.swap {α β : Type} : MyProd α β → MyProd β α
  | ⟨a, b⟩ => ⟨b, a⟩
-- ANCHOR_END: eliminators

-- ANCHOR: builtin
/-- info: Sum.inl 3 : ℕ ⊕ String -/
#guard_msgs in
#check (Sum.inl 3 : ℕ ⊕ String)

/-- info: (3, "three") : ℕ × String -/
#guard_msgs in
#check ((3, "three") : ℕ × String)

/-- info: "3" -/
#guard_msgs in
#eval (Sum.elim toString id (Sum.inl 3 : ℕ ⊕ String) : String)
-- ANCHOR_END: builtin

-- ANCHOR: payment
inductive Payment where
  | card (last4 : ℕ)
  | invoice (days : ℕ)
  | voucher (code : ℕ)

/--
error: Missing cases:
(voucher _)
-/
#guard_msgs in
def Payment.describe : Payment → String
  | .card last4 => s!"card ending in {last4}"
  | .invoice days => s!"invoice, due in {days} days"
-- ANCHOR_END: payment

end Ch11
