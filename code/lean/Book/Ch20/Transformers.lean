/-!
# Chapter 20 · Monad transformers: an order workflow

An order-processing workflow that needs two effects at once: a mutable stock
(state) and failures (exceptions). The workflow is written once, against the
classes `MonadStateOf` and `MonadExceptOf`, and run in two different stacks of
monad transformers, `StateT Stock (Except OrderError)` and
`ExceptT OrderError (StateM Stock)`. The two stacks disagree about what happens
to the stock when an order fails.
-/

namespace Ch20.Shop

-- ANCHOR: transformer_defs
example (σ α : Type) (m : Type → Type) : StateT σ m α = (σ → m (α × σ)) := rfl
example (ε α : Type) (m : Type → Type) : ExceptT ε m α = m (Except ε α) := rfl
example (ρ α : Type) (m : Type → Type) : ReaderT ρ m α = (ρ → m α) := rfl
example (σ α : Type) : StateM σ α = StateT σ Id α := rfl
-- ANCHOR_END: transformer_defs

-- ANCHOR: domain
/-- What can go wrong with an order. -/
inductive OrderError where
  | emptyOrder
  | unknownItem (item : String)
  | outOfStock (item : String) (wanted available : Nat)
  deriving Repr

/-- The stock of a warehouse: item names and the quantities on hand. -/
abbrev Stock := List (String × Nat)

/-- Set the quantity of `item` to `n`. -/
def Stock.update (stock : Stock) (item : String) (n : Nat) : Stock :=
  stock.map fun (i, q) => if i == item then (i, n) else (i, q)
-- ANCHOR_END: domain

-- ANCHOR: reserve
/-- Take `qty` units of `item` out of the stock. The function works in every
monad `m` that has a state of type `Stock` and errors of type `OrderError`. -/
def reserve {m : Type → Type} [Monad m] [MonadStateOf Stock m]
    [MonadExceptOf OrderError m] (item : String) (qty : Nat) : m Unit := do
  let stock ← get
  match stock.lookup item with
  | none => throw (.unknownItem item)
  | some available =>
    if qty ≤ available then
      set (stock.update item (available - qty))
    else
      throw (.outOfStock item qty available)

/-- Reserve every line of an order; return the number of units. -/
def placeOrder {m : Type → Type} [Monad m] [MonadStateOf Stock m]
    [MonadExceptOf OrderError m] (lines : List (String × Nat)) : m Nat := do
  if lines.isEmpty then
    throw .emptyOrder
  for (item, qty) in lines do
    reserve item qty
  return (lines.map (·.2)).sum
-- ANCHOR_END: reserve

-- ANCHOR: stacks
/-- State outside, errors inside: a failed run returns no state at all. -/
abbrev AllOrNothing := StateT Stock (Except OrderError)

/-- Errors outside, state inside: a failed run still returns the state. -/
abbrev KeepGoing := ExceptT OrderError (StateM Stock)

example (α : Type) : AllOrNothing α = (Stock → Except OrderError (α × Stock)) := rfl
example (α : Type) : KeepGoing α = (Stock → Except OrderError α × Stock) := rfl
-- ANCHOR_END: stacks

-- ANCHOR: runs
def warehouse : Stock := [("bolts", 10), ("nuts", 4)]

def good : List (String × Nat) := [("bolts", 3), ("nuts", 2)]
def bad : List (String × Nat) := [("bolts", 3), ("nuts", 9)]

/-- info: Except.ok (5, [("bolts", 7), ("nuts", 2)]) -/
#guard_msgs in
#eval (placeOrder good : AllOrNothing Nat).run warehouse

/-- info: Except.error (Ch20.Shop.OrderError.outOfStock "nuts" 9 4) -/
#guard_msgs in
#eval (placeOrder bad : AllOrNothing Nat).run warehouse

/-- info: (Except.ok 5, [("bolts", 7), ("nuts", 2)]) -/
#guard_msgs in
#eval (placeOrder good : KeepGoing Nat).run.run warehouse

/--
info: (Except.error (Ch20.Shop.OrderError.outOfStock "nuts" 9 4), [("bolts", 7), ("nuts", 4)])
-/
#guard_msgs in
#eval (placeOrder bad : KeepGoing Nat).run.run warehouse
-- ANCHOR_END: runs

-- ANCHOR: atomically
/-- Run `action`; if it fails, put the stock back the way it was and fail with
the same error. -/
def atomically {m : Type → Type} {α : Type} [Monad m] [MonadStateOf Stock m]
    [MonadExceptOf OrderError m] (action : m α) : m α := do
  let saved ← get
  try
    action
  catch e =>
    set saved
    throw e

/--
info: (Except.error (Ch20.Shop.OrderError.outOfStock "nuts" 9 4), [("bolts", 10), ("nuts", 4)])
-/
#guard_msgs in
#eval (atomically (placeOrder bad) : KeepGoing Nat).run.run warehouse
-- ANCHOR_END: atomically

-- ANCHOR: lift
/-- A check that needs only errors, written in the plain `Except` monad. -/
def checkLines (lines : List (String × Nat)) : Except OrderError Unit :=
  if lines.isEmpty then throw .emptyOrder else pure ()

/-- Inside the stack, the `Except` computation is lifted automatically. -/
def placeChecked (lines : List (String × Nat)) : AllOrNothing Nat := do
  checkLines lines
  for (item, qty) in lines do
    reserve item qty
  return (lines.map (·.2)).sum

/-- info: Except.error (Ch20.Shop.OrderError.emptyOrder) -/
#guard_msgs in
#eval (placeChecked []).run warehouse
-- ANCHOR_END: lift

end Ch20.Shop
