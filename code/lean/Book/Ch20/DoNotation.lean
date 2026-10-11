/-!
# Chapter 20 · Lean's `Monad` class and `do` notation

Lean's own monad classes (`Pure`, `Bind`, `Monad`), `do` notation and what it
desugars into, the laws of `LawfulMonad` used as rewriting rules for `do`
blocks, and `IO`.

Nothing in this file uses the class of `Book.Ch20.Monad`: here `Monad`, `pure`,
`bind` and `>>=` are Lean's.
-/

namespace Ch20.Do

-- ANCHOR: core_ops
/-- info: @pure : {f : Type u_1 → Type u_2} → [self : Pure f] → {α : Type u_1} → α → f α -/
#guard_msgs in
#check @pure

/--
info: @bind : {m : Type u_1 → Type u_2} → [self : Bind m] → {α β : Type u_1} → m α → (α → m β) → m β
-/
#guard_msgs in
#check @bind
-- ANCHOR_END: core_ops

-- ANCHOR: read_qty
def parseQty (s : String) : Option Nat := s.toNat?

def checkQty (n : Nat) : Option Nat := if 1 ≤ n ∧ n ≤ 100 then some n else none

/-- Parse, check, and compute the number of boxes (two units per box). -/
def boxes (s : String) : Option Nat := do
  let n ← parseQty s
  let q ← checkQty n
  return (q + 1) / 2

/-- info: [some 6, none, none] -/
#guard_msgs in
#eval ["12", "twelve", "500"].map boxes
-- ANCHOR_END: read_qty

-- ANCHOR: desugar
/--
info: def Ch20.Do.boxes : String → Option Nat :=
fun s => bind (parseQty s) fun n => bind (checkQty n) fun q => pure (HDiv.hDiv (HAdd.hAdd q 1) 2)
-/
#guard_msgs in
set_option pp.notation false in
#print boxes

/-- The `do` block and the chain of binds are the same term. -/
example (s : String) :
    boxes s = (parseQty s >>= fun n => checkQty n >>= fun q => pure ((q + 1) / 2)) :=
  rfl
-- ANCHOR_END: desugar

-- ANCHOR: nested
/-- `(← e)` runs `e` first and uses its result in place. -/
def totalQty (a b : String) : Option Nat := do
  return (← parseQty a) + (← parseQty b)

/--
info: def Ch20.Do.totalQty : String → String → Option Nat :=
fun a b =>
  bind (parseQty a) fun __do_lift => bind (parseQty b) fun __do_lift_1 => pure (HAdd.hAdd __do_lift __do_lift_1)
-/
#guard_msgs in
set_option pp.notation false in
#print totalQty
-- ANCHOR_END: nested

-- ANCHOR: laws_as_rewrites
section Laws

variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type}

/-- Left identity: a `pure` step can be inlined. -/
example (a : α) (f : α → m β) : (do let x ← pure a; f x) = f a := by
  simp only [pure_bind]

/-- Right identity: binding into `pure` changes nothing. -/
example (x : m α) : (x >>= fun a => pure a) = x := by
  simp only [bind_pure]

/-- The `do` elaborator applies right identity by itself: this block *is* `x`. -/
example (x : m α) : (do let a ← x; pure a) = x := rfl

/-- Associativity: extracting a sub-block into a helper (or inlining it) does
not change the program. -/
example (x : m α) (f : α → m β) (g : β → m γ) :
    (do let b ← (do let a ← x; f a); g b) = (do let a ← x; let b ← f a; g b) := by
  simp only [bind_assoc]

end Laws
-- ANCHOR_END: laws_as_rewrites

-- ANCHOR: lawful_instances
example : LawfulMonad Option := inferInstance
example : LawfulMonad (Except String) := inferInstance
example : LawfulMonad (StateM Nat) := inferInstance
-- ANCHOR_END: lawful_instances

-- ANCHOR: io
/-- An `IO` action: a description of a computation that interacts with the
world. Defining it prints nothing. -/
def greet (name : String) : IO Unit := do
  IO.println s!"Hello, {name}."
  IO.println "Your order has shipped."

/--
info: Hello, Ada.
Your order has shipped.
-/
#guard_msgs in
#eval greet "Ada"
-- ANCHOR_END: io

-- ANCHOR: io_values
/-- Actions are values: we can put them in a list, reorder them, and run them
later. A mutable reference (`IO.mkRef`) is an effect of `IO` too. -/
def countdown : IO Nat := do
  let counter ← IO.mkRef 0
  let steps : List (IO Unit) :=
    [1, 2, 3].map fun i => do
      IO.println s!"step {i}"
      counter.modify (· + 1)
  for step in steps.reverse do
    step
  counter.get

/--
info: step 3
step 2
step 1
---
info: 3
-/
#guard_msgs in
#eval countdown
-- ANCHOR_END: io_values

-- ANCHOR: io_def
/-- info: @[reducible] def IO : Type → Type :=
EIO IO.Error -/
#guard_msgs in
#print IO

/-- info: def EIO : Type → Type → Type :=
fun ε α => EST ε IO.RealWorld α -/
#guard_msgs in
#print EIO

/-- info: def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α -/
#guard_msgs in
#print EST
-- ANCHOR_END: io_def

end Ch20.Do
