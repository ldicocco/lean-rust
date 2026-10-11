import Book.Ch20.Monad

/-!
# Chapter 20 · State, Reader and Writer

Three monads whose computations are functions or pairs rather than containers:
`State σ` threads a value of type `σ` through a computation, `Reader ρ` gives
read-only access to an environment, and `Writer` accumulates a log. Each one is
an instance of the class of `Book.Ch20.Monad`, with the laws proved. A small
labeling program in the state monad, and a theorem about it proved for all
inputs.
-/

namespace Ch20

-- ANCHOR: state_def
/-- A computation with a state of type `σ`: given the current state, it returns
a result and the new state. -/
def State (σ α : Type) : Type := σ → α × σ

/-- Run a stateful computation from an initial state. -/
def State.run {σ α : Type} (m : State σ α) (s : σ) : α × σ := m s
-- ANCHOR_END: state_def

-- ANCHOR: state_monad
instance stateMonad (σ : Type) : Monad (State σ) where
  pure a := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'
  -- All three laws hold by computation: both sides of each equation unfold to
  -- the same function.
  pure_bind _ _ := rfl
  bind_pure _ := rfl
  bind_assoc _ _ _ := rfl
-- ANCHOR_END: state_monad

-- ANCHOR: state_ops
/-- Read the state. -/
def get {σ : Type} : State σ σ := fun s => (s, s)

/-- Replace the state. -/
def set {σ : Type} (s : σ) : State σ Unit := fun _ => ((), s)

/-- Return a fresh number from a counter and advance the counter. -/
def fresh : State Nat Nat :=
  Monad.bind get (fun n => Monad.bind (set (n + 1)) (fun _ => Monad.pure n))
-- ANCHOR_END: state_ops

-- ANCHOR: label
/-- Give every order line a fresh ticket number, in order. -/
def label : List String → State Nat (List (Nat × String))
  | [] => Monad.pure []
  | x :: xs =>
    Monad.bind fresh (fun n =>
      Monad.bind (label xs) (fun rest =>
        Monad.pure ((n, x) :: rest)))

/-- info: ([(100, "bolts"), (101, "nuts"), (102, "washers")], 103) -/
#guard_msgs in
#eval (label ["bolts", "nuts", "washers"]).run 100
-- ANCHOR_END: label

-- ANCHOR: label_counter
/-- Labeling `xs` advances the counter by exactly `xs.length`, whatever the
starting value. -/
theorem label_counter (xs : List String) (n : Nat) :
    ((label xs).run n).2 = n + xs.length := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
    -- Running `label (x :: xs)` from `n` runs `label xs` from `n + 1`.
    show ((label xs).run (n + 1)).2 = n + (x :: xs).length
    rw [ih (n + 1), List.length_cons]
    omega
-- ANCHOR_END: label_counter

-- ANCHOR: reader
/-- A computation that reads an environment of type `ρ`. -/
def Reader (ρ α : Type) : Type := ρ → α

instance readerMonad (ρ : Type) : Monad (Reader ρ) where
  pure a := fun _ => a
  bind m f := fun r => f (m r) r
  pure_bind _ _ := rfl
  bind_pure _ := rfl
  bind_assoc _ _ _ := rfl

/-- Ask for the environment. -/
def ask {ρ : Type} : Reader ρ ρ := fun r => r

/-- Pricing parameters, read by every step but changed by none. -/
structure Pricing where
  unitPrice : Nat
  shipping : Nat

def subtotal (qty : Nat) : Reader Pricing Nat :=
  Monad.bind ask (fun p => Monad.pure (qty * p.unitPrice))

def total (qty : Nat) : Reader Pricing Nat :=
  Monad.bind (subtotal qty) (fun s =>
    Monad.bind ask (fun p => Monad.pure (s + p.shipping)))

/-- info: 85 -/
#guard_msgs in
#eval total 3 { unitPrice := 25, shipping := 10 }
-- ANCHOR_END: reader

-- ANCHOR: writer
/-- A computation that also produces a log. -/
def Writer (α : Type) : Type := α × List String

instance writerMonad : Monad Writer where
  pure a := (a, [])
  bind m f :=
    let (b, w) := f m.1
    (b, m.2 ++ w)
  -- Each law of the monad is a law of the log: `[]` is a unit for `++`,
  -- and `++` is associative.
  pure_bind a f := by
    show ((f a).1, [] ++ (f a).2) = f a
    rw [List.nil_append]
    -- Goal: ((f a).1, (f a).2) = f a, true by the eta rule for pairs.
    rfl
  bind_pure m := by
    show (m.1, m.2 ++ []) = m
    rw [List.append_nil]
    rfl
  bind_assoc m f g := by
    show ((g (f m.1).1).1, (m.2 ++ (f m.1).2) ++ (g (f m.1).1).2)
       = ((g (f m.1).1).1, m.2 ++ ((f m.1).2 ++ (g (f m.1).1).2))
    rw [List.append_assoc]

/-- Add a line to the log. -/
def tell (line : String) : Writer Unit := ((), [line])

def reserveLogged (item : String) (qty : Nat) : Writer Nat :=
  Monad.bind (tell s!"reserve {qty} x {item}") (fun _ => Monad.pure qty)

/-- info: (5, ["reserve 2 x bolts", "reserve 3 x nuts"]) -/
#guard_msgs in
#eval Monad.bind (reserveLogged "bolts" 2) (fun a =>
        Monad.bind (reserveLogged "nuts" 3) (fun b => Monad.pure (a + b)))
-- ANCHOR_END: writer

end Ch20
