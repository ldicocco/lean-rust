import Std.Data.TreeMap

/-!
# Chapter 2 · An order book in Lean

The order book of `code/rust/examples/ch02_orders.rs`, written in Lean: the
same types, the same operations and the same output. The Rust version mutates
the book through `&mut self`; this one returns a new book. Properties of the
program are proved in `Book/Ch02/FirstProofs.lean`.
-/

namespace Ch02

-- ANCHOR: types
/-- Which side of the book an order is on. -/
inductive Side where
  | buy
  | sell
  deriving Repr, DecidableEq

/-- A resting limit order. Prices are in cents, so that they are exact. -/
structure Order where
  id : Nat
  trader : String
  side : Side
  price : Nat
  qty : Nat
  deriving Repr, BEq

/-- Why an order or a cancellation was rejected. -/
inductive OrderError where
  | zeroQuantity
  | zeroPrice
  | wouldCross (best : Nat)
  | unknownOrder (id : Nat)
  deriving Repr, BEq, DecidableEq

/-- The resting orders, oldest first, and the id the next order will get. -/
structure Book where
  orders : List Order
  nextId : Nat
  deriving Repr
-- ANCHOR_END: types

-- ANCHOR: display
/-- A price in cents, printed as dollars and cents. -/
def showPrice (cents : Nat) : String :=
  let c := cents % 100
  let pad := if c < 10 then "0" else ""
  s!"{cents / 100}.{pad}{c}"

instance : ToString Order where
  toString o :=
    let verb := match o.side with
      | .buy => "buys"
      | .sell => "sells"
    s!"#{o.id} {o.trader} {verb} {o.qty} @ {showPrice o.price}"

instance : ToString OrderError where
  toString
    | .zeroQuantity => "quantity must be positive"
    | .zeroPrice => "price must be positive"
    | .wouldCross best => s!"would cross the best price {showPrice best}"
    | .unknownOrder id => s!"no order #{id}"
-- ANCHOR_END: display

namespace Book

-- ANCHOR: queries
def empty : Book := { orders := [], nextId := 1 }

/-- The orders on one side, oldest first. -/
def onSide (book : Book) (side : Side) : List Order :=
  book.orders.filter (fun o => o.side == side)

/-- The highest price a buyer is offering. -/
def bestBid (book : Book) : Option Nat :=
  (book.onSide .buy |>.map (·.price)).max?

/-- The lowest price a seller is asking. -/
def bestAsk (book : Book) : Option Nat :=
  (book.onSide .sell |>.map (·.price)).min?

/-- The gap between the best ask and the best bid. -/
def spread (book : Book) : Option Nat := do
  let bid ← book.bestBid
  let ask ← book.bestAsk
  return ask - bid

/-- The total quantity of a list of orders. -/
def totalQty : List Order → Nat
  | [] => 0
  | o :: os => o.qty + totalQty os

/-- The total quantity on one side. -/
def volume (book : Book) (side : Side) : Nat :=
  totalQty (book.onSide side)

/-- The total quantity at each price on one side, by increasing price.
`Std.TreeMap` is the counterpart of Rust's `BTreeMap`. -/
def depth (book : Book) (side : Side) : List (Nat × Nat) :=
  let addOrder (levels : Std.TreeMap Nat Nat) (o : Order) :=
    levels.alter o.price (fun q => some (q.getD 0 + o.qty))
  (book.onSide side |>.foldl addOrder ∅).toList

/-- The order with a given id, if it is in the book. -/
def find? (book : Book) (id : Nat) : Option Order :=
  book.orders.find? (fun o => o.id == id)
-- ANCHOR_END: queries

-- ANCHOR: commands
/-- The best price on the other side, if an order at `price` would trade
against it. -/
def crossing (book : Book) (side : Side) (price : Nat) : Option Nat :=
  match side with
  | .buy => book.bestAsk.filter (fun ask => ask ≤ price)
  | .sell => book.bestBid.filter (fun bid => price ≤ bid)

/-- Validate an order and add it to the book. The result is the new order's
id together with the *new* book; the old book is unchanged. -/
def place (book : Book) (trader : String) (side : Side) (price qty : Nat) :
    Except OrderError (Nat × Book) :=
  if qty = 0 then .error .zeroQuantity
  else if price = 0 then .error .zeroPrice
  else match book.crossing side price with
    | some best => .error (.wouldCross best)
    | none =>
      let order := { id := book.nextId, trader, side, price, qty }
      .ok (book.nextId, { orders := book.orders ++ [order], nextId := book.nextId + 1 })

/-- Remove an order from the book; return it with the new book. -/
def cancel (book : Book) (id : Nat) : Except OrderError (Order × Book) :=
  match book.find? id with
  | none => .error (.unknownOrder id)
  | some order => .ok (order, { book with orders := book.orders.filter (·.id != id) })
-- ANCHOR_END: commands

end Book

-- ANCHOR: demo
def requests : List (String × Side × Nat × Nat) :=
  [("alice", .buy, 10050, 10), ("bob", .sell, 10125, 5),
   ("carol", .buy, 10075, 7), ("dave", .sell, 10125, 8),
   ("gina", .sell, 10200, 4), ("erin", .buy, 10150, 3),
   ("frank", .sell, 9900, 0)]

/-- The book after all the requests, ignoring the rejected ones. -/
def demoBook : Book :=
  requests.foldl (init := Book.empty) fun book (trader, side, price, qty) =>
    match book.place trader side price qty with
    | .ok (_, book') => book'
    | .error _ => book

def cancelAndReport (book : Book) (id : Nat) : IO Book := do
  match book.cancel id with
  | .ok (order, book') =>
    IO.println s!"cancelled {order}"
    return book'
  | .error e =>
    IO.println s!"rejected cancel: {e}"
    return book

def demo : IO Unit := do
  let mut book := Book.empty
  for (trader, side, price, qty) in requests do
    match book.place trader side price qty with
    | .ok (id, book') =>
      book := book'
      if let some order := book.find? id then
        IO.println s!"placed   {order}"
    | .error e => IO.println s!"rejected {trader}: {e}"
  if let (some bid, some ask, some spread) := (book.bestBid, book.bestAsk, book.spread) then
    IO.println s!"best bid {showPrice bid}, best ask {showPrice ask}, spread {showPrice spread}"
  IO.println s!"volume: {book.volume .buy} to buy, {book.volume .sell} to sell"
  for (price, qty) in book.depth .sell do
    IO.println s!"sell depth at {showPrice price}: {qty}"
  book ← cancelAndReport book 3
  book ← cancelAndReport book 3
  if let some bid := book.bestBid then
    IO.println s!"best bid now {showPrice bid}"
-- ANCHOR_END: demo

-- ANCHOR: demo_eval
/--
info: placed   #1 alice buys 10 @ 100.50
placed   #2 bob sells 5 @ 101.25
placed   #3 carol buys 7 @ 100.75
placed   #4 dave sells 8 @ 101.25
placed   #5 gina sells 4 @ 102.00
rejected erin: would cross the best price 101.25
rejected frank: quantity must be positive
best bid 100.75, best ask 101.25, spread 0.50
volume: 17 to buy, 17 to sell
sell depth at 101.25: 13
sell depth at 102.00: 4
cancelled #3 carol buys 7 @ 100.75
rejected cancel: no order #3
best bid now 100.50
-/
#guard_msgs in
#eval demo
-- ANCHOR_END: demo_eval

end Ch02
