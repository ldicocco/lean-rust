import Mathlib.Data.Nat.Notation

/-!
# Chapter 12 · Implicit arguments and universes

Type arguments in Lean: implicit arguments, explicit type application with `@`
and named arguments. Then the universe hierarchy: every type has a type,
`Type : Type 1 : Type 2 : ...`, polymorphic types live one level up
(predicativity), `Prop` is the exception (impredicativity), `Sort u` names all
the levels at once, and definitions can be universe polymorphic.
-/

namespace Ch12

-- ANCHOR: twice
/-- Apply a function twice. The type `α` is an *implicit* argument: callers do
not pass it, Lean works it out from the other arguments. -/
def twice {α : Type} (f : α → α) (a : α) : α := f (f a)
-- ANCHOR_END: twice

-- ANCHOR: type_application
/-- info: 16 -/
#guard_msgs in
#eval twice (· + 3) 10

-- `@` makes every argument explicit: here we pass the type ourselves.
/-- info: 16 -/
#guard_msgs in
#eval @twice ℕ (· + 3) 10

/-- info: "hi!!" -/
#guard_msgs in
#eval twice (α := String) (· ++ "!") "hi"

/-- info: @twice : {α : Type} → (α → α) → α → α -/
#guard_msgs in
#check @twice
-- ANCHOR_END: type_application

-- ANCHOR: types_have_types
/-- info: ℕ : Type -/
#guard_msgs in
#check ℕ

/-- info: ℕ → List ℕ : Type -/
#guard_msgs in
#check ℕ → List ℕ

/-- info: Type : Type 1 -/
#guard_msgs in
#check Type

/-- info: Type 1 : Type 2 -/
#guard_msgs in
#check Type 1
-- ANCHOR_END: types_have_types

-- ANCHOR: predicative
/-- info: (α : Type) → α → α : Type 1 -/
#guard_msgs in
#check (α : Type) → α → α

/--
error: Type mismatch
  (α : Type) → α → α
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs in
def PolyId : Type := (α : Type) → α → α

/-- The type of polymorphic identity functions is fine one level up. -/
def PolyId' : Type 1 := (α : Type) → α → α

/-- Its only (sensible) inhabitant. -/
def polyId : PolyId' := fun _ a => a
-- ANCHOR_END: predicative

-- ANCHOR: type_in_type
/--
error: Type mismatch
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs in
example : Type := Type
-- ANCHOR_END: type_in_type

-- ANCHOR: prop
/-- info: Prop : Type -/
#guard_msgs in
#check Prop

/-- info: 2 + 2 = 4 : Prop -/
#guard_msgs in
#check 2 + 2 = 4

-- A quantifier over *all* propositions is still a proposition:
-- `Prop` is impredicative.
/-- info: ∀ (p : Prop), p → p : Prop -/
#guard_msgs in
#check ∀ p : Prop, p → p

theorem polyIdProof : ∀ p : Prop, p → p := fun _ hp => hp
-- ANCHOR_END: prop

-- ANCHOR: sort
/-- info: Prop : Type -/
#guard_msgs in
#check Sort 0

/-- info: Type : Type 1 -/
#guard_msgs in
#check Sort 1

/-- info: Type 1 : Type 2 -/
#guard_msgs in
#check Sort 2
-- ANCHOR_END: sort

-- ANCHOR: universe_poly
universe u

/-- One identity function for every universe: `u` is a *universe variable*. -/
def myId {α : Sort u} (a : α) : α := a

/-- info: myId 3 : ℕ -/
#guard_msgs in
#check myId 3            -- α := ℕ,       ℕ : Type   = Sort 1

/-- info: myId ℕ : Type -/
#guard_msgs in
#check myId ℕ            -- α := Type,    Type : Type 1 = Sort 2

/-- info: myId polyIdProof : ∀ (p : Prop), p → p -/
#guard_msgs in
#check myId polyIdProof  -- α is a proposition, α : Prop = Sort 0

/-- info: List.{u} (α : Type u) : Type u -/
#guard_msgs in
#check List
-- ANCHOR_END: universe_poly

-- ANCHOR: ulift
/-- `ULift` copies a type into a higher universe, when an API demands one. -/
def liftedThree : ULift.{1} ℕ := ULift.up 3

/-- info: ULift ℕ : Type 1 -/
#guard_msgs in
#check ULift.{1} ℕ

/-- info: 3 -/
#guard_msgs in
#eval liftedThree.down
-- ANCHOR_END: ulift

-- ANCHOR: self_app
/--
error: Application type mismatch: The argument
  (α : Type) → α → α
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  x ((α : Type) → α → α)
-/
#guard_msgs in
def selfApp (x : (α : Type) → α → α) : (α : Type) → α → α :=
  x ((α : Type) → α → α) x

/-- In `Prop`, the same self-application is accepted: `Prop` is impredicative. -/
theorem selfAppProp (x : ∀ p : Prop, p → p) : ∀ p : Prop, p → p :=
  x (∀ p : Prop, p → p) x

/-- In `Type`, a polymorphic identity of level 1 can take one of level 0. -/
def PolyIdU : Type (u + 1) := (α : Type u) → α → α

def applyUp (x : PolyIdU.{1}) (y : PolyIdU.{0}) : PolyIdU.{0} :=
  x PolyIdU.{0} y
-- ANCHOR_END: self_app

end Ch12
