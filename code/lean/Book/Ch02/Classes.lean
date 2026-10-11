import Std.Data.HashMap

/-!
# Chapter 2 · Type classes for Rust programmers

A class of our own (Lean's `trait`), instances (Lean's `impl`), generic
functions with instance arguments (trait bounds), an instance that depends on
another (a blanket impl), default methods, and the standard classes that
correspond to Rust's most common derivable traits.
-/

namespace Ch02

-- ANCHOR: summary_class
/-- Rust: `trait Summary { fn summary(&self) -> String; fn tag(&self) -> String
{ ... } }`. A class lists the operations an instance must provide; `tag` has
a default implementation, like a default method. -/
class Summary (α : Type) where
  summary : α → String
  tag : α → String := fun _ => "item"
-- ANCHOR_END: summary_class

-- ANCHOR: summary_instances
structure Sensor where
  name : String
  celsius : Int

/-- Rust: `impl Summary for Sensor { ... }`. -/
instance : Summary Sensor where
  summary s := s!"{s.name}: {s.celsius} °C"
  tag _ := "sensor"

/-- An instance that uses the default `tag`. -/
instance : Summary Nat where
  summary n := s!"the number {n}"

/-- Rust: `impl<T: Summary> Summary for Vec<T>`. The instance for `List α`
needs an instance for `α`, written as an instance argument `[Summary α]`. -/
instance {α : Type} [Summary α] : Summary (List α) where
  summary xs := ", ".intercalate (xs.map Summary.summary)
  tag _ := "list"
-- ANCHOR_END: summary_instances

-- ANCHOR: report
/-- Rust: `fn report<T: Summary>(x: &T) -> String`. The square brackets ask
Lean to find the instance by itself, at every call site. -/
def report {α : Type} [Summary α] (x : α) : String :=
  s!"[{Summary.tag x}] {Summary.summary x}"

/-- info: "[sensor] boiler: 74 °C" -/
#guard_msgs in
#eval report (Sensor.mk "boiler" 74)

/-- info: "[item] the number 7" -/
#guard_msgs in
#eval report 7

/-- info: "[list] the number 1, the number 2" -/
#guard_msgs in
#eval report [1, 2]
-- ANCHOR_END: report

-- ANCHOR: missing_instance
/--
error: failed to synthesize instance of type class
  Summary String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval report "hello"
-- ANCHOR_END: missing_instance

-- ANCHOR: standard_classes
/-- `deriving` asks Lean to write the instances, like `#[derive]`. -/
structure Endpoint where
  host : String
  port : Nat
  deriving Repr, BEq, Hashable, Inhabited

/-- `ToString` is Rust's `Display`: we write it by hand. -/
instance : ToString Endpoint where
  toString e := s!"{e.host}:{e.port}"

def api : Endpoint := { host := "api.example.com", port := 443 }
-- ANCHOR_END: standard_classes

-- ANCHOR: standard_classes_eval
/-- info: { host := "api.example.com", port := 443 } -/
#guard_msgs in
#eval api                                   -- uses Repr, like {:?}

/-- info: "connecting to api.example.com:443" -/
#guard_msgs in
#eval s!"connecting to {api}"               -- uses ToString, like {}

/-- info: true -/
#guard_msgs in
#eval api == { host := "api.example.com", port := 443 }   -- uses BEq

/-- info: { host := "", port := 0 } -/
#guard_msgs in
#eval (default : Endpoint)                  -- uses Inhabited, like Default
-- ANCHOR_END: standard_classes_eval

-- ANCHOR: hashmap
open Std in
/-- `Std.HashMap` needs `BEq` and `Hashable` keys, as Rust's `HashMap` needs
`Eq` and `Hash`. -/
def failures : HashMap Endpoint Nat :=
  ({} : HashMap Endpoint Nat) |>.insert api 2 |>.insert { host := "db", port := 5432 } 1

/-- info: (some 2, none) -/
#guard_msgs in
#eval (failures.get? api, failures.get? default)
-- ANCHOR_END: hashmap

end Ch02
