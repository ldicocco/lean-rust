/-!
# Chapter 15 · Existential types in Lean

Dependent pairs as existential packages: a value with a hidden type and the
operations on it (Lean's `Box<dyn Display>`), and an abstract data type of
counters as a structure with a type field. Packing and unpacking, the scoping
that makes the hidden type abstract, the universe bump (a structure with a
`Type` field lives in `Type 1`, with practical consequences), and `Exists`
versus `Sigma` once more.
-/

namespace Ch15

-- ANCHOR: sigma_check
/-- info: (α : Type) × (α → String) : Type 1 -/
#guard_msgs in
#check ((α : Type) × (α → String))

/-- info: (α : Type) × α × (α → String) : Type 1 -/
#guard_msgs in
#check ((α : Type) × α × (α → String))
-- ANCHOR_END: sigma_check

-- ANCHOR: showable
/-- A value of some hidden type, packed with a way to display it: the
counterpart of Rust's `Box<dyn Display>`. -/
abbrev Showable := (α : Type) × α × (α → String)

/-- Packing: choose the hidden type, give a value and an implementation. -/
def readings : List Showable :=
  [⟨Nat, 42, fun n => s!"{n} ticks"⟩,
   ⟨String, "fridge", fun s => s!"sensor {s}"⟩,
   ⟨Bool, true, fun b => if b then "door open" else "door closed"⟩]

/-- Unpacking: the client sees a type `α`, a value of type `α` and a function
on `α`, and can only combine them. -/
def Showable.show (p : Showable) : String :=
  match p with
  | ⟨_, x, f⟩ => f x

/-- info: ["42 ticks", "sensor fridge", "door open"] -/
#guard_msgs in
#eval readings.map Showable.show
-- ANCHOR_END: showable

-- ANCHOR: counter_adt
/-- The operations of a counter whose states have type `σ`. -/
structure CounterOps (σ : Type) where
  init : σ
  step : σ → σ
  get : σ → Nat

/-- An abstract data type: ∃σ. CounterOps σ. A value of this structure is
a package of a type and an implementation. -/
structure Counter where
  State : Type
  ops : CounterOps State
-- ANCHOR_END: counter_adt

-- ANCHOR: universe
/-- info: Ch15.Counter : Type 1 -/
#guard_msgs in
#check Counter

/-- info: CounterOps Nat : Type -/
#guard_msgs in
#check CounterOps Nat
-- ANCHOR_END: universe

-- ANCHOR: implementations
/-- Counting with a natural number. -/
def natOps : CounterOps Nat := { init := 0, step := (· + 1), get := id }

/-- Counting with a list of `()`, one per step: a different representation. -/
def unaryOps : CounterOps (List Unit) :=
  { init := [], step := (() :: ·), get := List.length }

/-- Counting by ten: a different behavior. -/
def tenOps : CounterOps Nat := { init := 0, step := (· + 10), get := id }

/-- Three packages: each hides its state type behind the `Counter` interface. -/
def byOne : Counter := ⟨Nat, natOps⟩
def unary : Counter := ⟨List Unit, unaryOps⟩
def byTen : Counter := ⟨Nat, tenOps⟩
-- ANCHOR_END: implementations

-- ANCHOR: pack_unpack
/-- Rule T-Pack: a type and an implementation for that type make a package. -/
def Counter.pack (σ : Type) (ops : CounterOps σ) : Counter := ⟨σ, ops⟩

/-- Rule T-Unpack: the client `k` must work for every state type `σ`, and its
result type `ρ` is fixed before `σ` is in scope, so it cannot mention `σ`. -/
def Counter.unpack {ρ : Type} (c : Counter) (k : (σ : Type) → CounterOps σ → ρ) : ρ :=
  k c.State c.ops

/-- The computation rule: unpacking a package hands its contents to the client. -/
theorem Counter.unpack_pack {ρ : Type} (σ : Type) (ops : CounterOps σ)
    (k : (σ : Type) → CounterOps σ → ρ) :
    (Counter.pack σ ops).unpack k = k σ ops := rfl
-- ANCHOR_END: pack_unpack

-- ANCHOR: client
/-- Apply `f` to `s`, `n` times. -/
def iterate {σ : Type} (f : σ → σ) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => iterate f n (f s)

/-- A client: take `n` steps from the initial state and read the value. It is
written once and works for every package. -/
def Counter.run (c : Counter) (n : Nat) : Nat :=
  c.unpack (fun _ ops => ops.get (iterate ops.step n ops.init))

/-- A heterogeneous list: three packages with two different hidden types. -/
def counters : List Counter := [byOne, unary, byTen]

/-- info: [3, 3, 30] -/
#guard_msgs in
#eval counters.map (·.run 3)
-- ANCHOR_END: client

-- ANCHOR: abstract
/--
error: Type mismatch
  c.ops.init
has type
  c.State
but is expected to have type
  Nat
-/
#guard_msgs in
def peek (c : Counter) : Nat := c.ops.init
-- ANCHOR_END: abstract

-- ANCHOR: transparent
/-- For a *specific* package, Lean can see through the type field. -/
example : byOne.State = Nat := rfl

def peekOne : Nat := byOne.ops.init
-- ANCHOR_END: transparent

-- ANCHOR: bump_errors
/--
error: Type mismatch
  Counter
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs in
def CounterType : Type := Counter

/--
error: Application type mismatch: The argument
  Counter
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  IO Counter
-/
#guard_msgs in
def chooseCounter : IO Counter := pure byOne
-- ANCHOR_END: bump_errors

-- ANCHOR: exists_vs_sigma
/-- info: ∃ σ, Nonempty (CounterOps σ) : Prop -/
#guard_msgs in
#check ∃ σ : Type, Nonempty (CounterOps σ)

/-- The proposition is provable: `Nat`, with `natOps`, is a witness. -/
theorem some_counter_exists : ∃ σ : Type, Nonempty (CounterOps σ) :=
  ⟨Nat, ⟨natOps⟩⟩

/--
error: Invalid projection: Cannot project a value of non-propositional type
  Type
from the expression
  h
which has propositional type
  ∃ σ, Nonempty (CounterOps σ)
-/
#guard_msgs in
def witness (h : ∃ σ : Type, Nonempty (CounterOps σ)) : Type := h.1
-- ANCHOR_END: exists_vs_sigma

end Ch15
