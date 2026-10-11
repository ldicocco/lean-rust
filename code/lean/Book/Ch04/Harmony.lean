/-!
# Chapter 4 · Harmony in Lean

Three observations:

* An `inductive` proposition is defined by its introduction rules (the
  constructors); Lean *derives* the elimination rule (the recursor). The
  derived eliminators have exactly the shapes of ∧E, ∨E, ⊤ (useless) and ⊥E.
* Prior's `tonk` cannot exist: any operation on propositions with tonk's two
  rules proves `False`, and no truth table validates both rules.
* Local soundness and local completeness are the β and η equations, visible
  on data (pairs, functions, sums) rather than on proofs.
-/

namespace Ch04

-- ANCHOR: inductive_connectives
/-- Conjunction: one introduction rule with two premises. -/
inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b

/-- Disjunction: two introduction rules. -/
inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

/-- Truth: one introduction rule with no premises. -/
inductive MyTrue : Prop where
  | intro : MyTrue

/-- Falsity: no introduction rules at all. -/
inductive MyFalse : Prop
-- ANCHOR_END: inductive_connectives

-- ANCHOR: recursors
/--
info: @MyOr.rec : ∀ {a b : Prop} {motive : MyOr a b → Prop},
  (∀ (a_1 : a), motive ⋯) → (∀ (a_1 : b), motive ⋯) → ∀ (t : MyOr a b), motive t
-/
#guard_msgs in
#check @MyOr.rec

/--
info: @MyTrue.rec : {motive : MyTrue → Sort u_1} → motive MyTrue.intro → (t : MyTrue) → motive t
-/
#guard_msgs in
#check @MyTrue.rec

/-- info: MyFalse.rec : (motive : MyFalse → Sort u_1) → (t : MyFalse) → motive t -/
#guard_msgs in
#check @MyFalse.rec
-- ANCHOR_END: recursors

-- ANCHOR: derived_elims
/-- ∧E₁, derived from the recursor: take the pair apart, keep the left part. -/
theorem MyAnd.left {a b : Prop} (h : MyAnd a b) : a :=
  MyAnd.rec (motive := fun _ => a) (fun ha _ => ha) h

/-- ∨E, derived from the recursor with a constant motive `c`. -/
theorem MyOr.elim {a b c : Prop} (h : MyOr a b) (left : a → c) (right : b → c) : c :=
  MyOr.rec (motive := fun _ => c) left right h

/-- ⊥E, derived from the recursor: zero cases to handle. -/
theorem MyFalse.elim {c : Prop} (h : MyFalse) : c :=
  MyFalse.rec (motive := fun _ => c) h
-- ANCHOR_END: derived_elims

-- ANCHOR: tonk
/-- No operation on propositions obeys both of Prior's rules for `tonk`:
if one did, `False` would be provable. -/
theorem no_tonk (tonk : Prop → Prop → Prop)
    (tonkI : ∀ {a b : Prop}, a → tonk a b)
    (tonkE : ∀ {a b : Prop}, tonk a b → b) : False :=
  tonkE (tonkI trivial)

/-- No truth table for `tonk` makes both rules sound: tonk-I needs
`a → tonk a b`, tonk-E needs `tonk a b → b`, and the row `a = true`,
`b = false` cannot satisfy both. -/
theorem no_tonk_table : ¬ ∃ f : Bool → Bool → Bool,
    (∀ a b, a = true → f a b = true) ∧ (∀ a b, f a b = true → b = true) := by
  intro ⟨f, hI, hE⟩
  have h : false = true := hE true false (hI true false rfl)
  contradiction
-- ANCHOR_END: tonk

-- ANCHOR: beta
/-! Local soundness, on data: an introduction followed by an elimination
computes away. All three hold by `rfl`: Lean evaluates both sides. -/
example (α β : Type) (a : α) (b : β) : (a, b).1 = a := rfl

example (α β : Type) (f : α → β) (a : α) : (fun x => f x) a = f a := rfl

example (α β γ : Type) (f : α → γ) (g : β → γ) (a : α) :
    Sum.elim f g (Sum.inl a) = f a := rfl
-- ANCHOR_END: beta

-- ANCHOR: eta
/-! Local completeness, on data: eliminating and re-introducing gives back
what we started with. For pairs, functions and `Unit` Lean knows this by
`rfl` (definitional η); for sums it needs a case analysis. -/
example (α β : Type) (p : α × β) : (p.1, p.2) = p := rfl

example (α β : Type) (f : α → β) : (fun x => f x) = f := rfl

example (u : Unit) : u = () := rfl

example (α β : Type) (s : α ⊕ β) : Sum.elim Sum.inl Sum.inr s = s := by
  cases s <;> rfl
-- ANCHOR_END: eta

end Ch04
