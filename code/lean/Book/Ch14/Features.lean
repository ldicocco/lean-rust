/-!
# Chapter 14 · More of the type-class toolbox in Lean

Default methods, output parameters (`outParam`, Lean's counterpart of Rust's
associated types), and two classes from Lean's core library that the book has
already used: `Decidable` (a class whose instances are decision procedures)
and `Inhabited` (Rust's `Default`).
-/

namespace Ch14

-- ANCHOR: default_method
/-- A class with a default method: `describe` has a default implementation,
written in terms of `name`. -/
class Describe (α : Type) where
  name : α → String
  describe : α → String := fun x => s!"<{name x}>"

/-- This instance uses the default `describe`. -/
instance : Describe Nat where
  name n := s!"nat {n}"

/-- This instance overrides it. -/
instance : Describe Bool where
  name b := toString b
  describe b := if b then "yes" else "no"

/-- info: "<nat 5>" -/
#guard_msgs in
#eval Describe.describe (5 : Nat)

/-- info: "yes" -/
#guard_msgs in
#eval Describe.describe true
-- ANCHOR_END: default_method

-- ANCHOR: out_param
/-- Sensors and their readings. `reading` is an *output* parameter: once the
sensor type is known, resolution determines the reading type, as an
associated type does in Rust. -/
class Sensor (σ : Type) (reading : outParam Type) where
  read : σ → reading

/-- The same class with an ordinary (input) parameter. -/
class Sensor' (σ : Type) (reading : Type) where
  read : σ → reading

structure Thermometer where
  tenths : Int

instance : Sensor Thermometer Int := ⟨fun t => t.tenths⟩
instance : Sensor' Thermometer Int := ⟨fun t => t.tenths⟩

def readTwice {σ r : Type} [Sensor σ r] (s : σ) : r × r :=
  (Sensor.read s, Sensor.read s)

def readTwice' {σ r : Type} [Sensor' σ r] (s : σ) : r × r :=
  (Sensor'.read s, Sensor'.read s)

/-- info: (215, 215) -/
#guard_msgs in
#eval readTwice (Thermometer.mk 215)
-- ANCHOR_END: out_param

-- ANCHOR: stuck
/--
error: typeclass instance problem is stuck
  Sensor' Thermometer ?m.3

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Sensor'` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
#eval readTwice' (Thermometer.mk 215)

/-- info: (215, 215) -/
#guard_msgs in
#eval (readTwice' (Thermometer.mk 215) : Int × Int)
-- ANCHOR_END: stuck

-- ANCHOR: hadd
/--
info: @HAdd.hAdd : {α : Type u_1} → {β : Type u_2} → {γ : outParam (Type u_3)} → [self : HAdd α β γ] → α → β → γ
-/
#guard_msgs in
#check @HAdd.hAdd
-- ANCHOR_END: hadd

-- ANCHOR: decidable
/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in
#print Decidable

/-- A batch of readings is *paired* when it has an even number of entries
(every measurement is taken twice). This is a proposition, not a `Bool`. -/
def Paired (xs : List Int) : Prop := xs.length % 2 = 0

/-- The instance is a decision procedure: it decides `Paired xs` for every
`xs`, producing a proof either way. Here we reuse the instance for equality
of natural numbers. -/
instance (xs : List Int) : Decidable (Paired xs) :=
  inferInstanceAs (Decidable (xs.length % 2 = 0))

/-- info: "paired" -/
#guard_msgs in
#eval if Paired [215, 218, 221, 219] then "paired" else "unpaired"

example : Paired [215, 218] := by decide
example : ¬ Paired [215] := by decide
-- ANCHOR_END: decidable

-- ANCHOR: undecidable
/-- A proposition about all natural numbers has no `Decidable` instance. -/
def AllEven (f : Nat → Nat) : Prop := ∀ n, f n % 2 = 0

/--
error: failed to synthesize instance of type class
  Decidable (AllEven fun n => 2 * n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval if AllEven (fun n => 2 * n) then "yes" else "no"
-- ANCHOR_END: undecidable

-- ANCHOR: inhabited
/--
info: class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Inhabited.default : α
constructor:
  Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α
-/
#guard_msgs in
#print Inhabited

structure Reading where
  sensor : String
  value : Int
  deriving Repr, Inhabited

/-- info: { sensor := "", value := 0 } -/
#guard_msgs in
#eval (default : Reading)

/-- info: (0, "", []) -/
#guard_msgs in
#eval (default : Nat × String × List Bool)
-- ANCHOR_END: inhabited

end Ch14
