import Book.Ch02.Orders

/-!
# Chapter 2 · First proofs about the order book

`theorem` and `example`; the tactics `rfl`, `decide`, `simp`, `omega` and
`induction`; reading goals and errors; `sorry`; and properties of the order
book of `Book/Ch02/Orders.lean` proved for every book, not just tested on one.
-/

namespace Ch02

open Book

-- ANCHOR: unit_tests
/-- Facts about the demo book, proved by computation. These are unit tests
that Lean runs every time the file is checked. -/
example : demoBook.bestBid = some 10075 := rfl

example : demoBook.spread = some 50 := by rfl

example : demoBook.volume .sell = 17 := by decide

example : demoBook.depth .sell = [(10125, 13), (10200, 4)] := by decide
-- ANCHOR_END: unit_tests

-- ANCHOR: place_zero
/-- An order with quantity zero is rejected, whatever the book, trader, side
and price. -/
theorem place_zero_qty (book : Book) (trader : String) (side : Side) (price : Nat) :
    book.place trader side price 0 = .error .zeroQuantity := by
  simp [Book.place]

/-- An order with price zero (and a positive quantity) is rejected. -/
theorem place_zero_price (book : Book) (trader : String) (side : Side) (qty : Nat)
    (h : qty ≠ 0) : book.place trader side 0 qty = .error .zeroPrice := by
  simp [Book.place, h]
-- ANCHOR_END: place_zero

-- ANCHOR: unsolved
/--
error: unsolved goals
case cons
ys : List Order
o : Order
os : List Order
ih : totalQty (os ++ ys) = totalQty os + totalQty ys
⊢ o.qty + (totalQty os + totalQty ys) = o.qty + totalQty os + totalQty ys
-/
#guard_msgs in
example (xs ys : List Order) :
    totalQty (xs ++ ys) = totalQty xs + totalQty ys := by
  induction xs with
  | nil => simp [totalQty]
  | cons o os ih => simp [totalQty, ih]
-- ANCHOR_END: unsolved

-- ANCHOR: total_qty_append
/-- The total quantity of two lists of orders, one after the other. -/
theorem totalQty_append (xs ys : List Order) :
    totalQty (xs ++ ys) = totalQty xs + totalQty ys := by
  induction xs with
  | nil =>
    -- Goal: totalQty ([] ++ ys) = totalQty [] + totalQty ys
    simp [totalQty]
  | cons o os ih =>
    -- ih   : totalQty (os ++ ys) = totalQty os + totalQty ys
    -- Goal : totalQty (o :: os ++ ys) = totalQty (o :: os) + totalQty ys
    simp [totalQty, ih]
    -- Goal : o.qty + (totalQty os + totalQty ys) = o.qty + totalQty os + totalQty ys
    omega
-- ANCHOR_END: total_qty_append

-- ANCHOR: omega_fails
/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  a ≥ 0
  a - b ≥ 1
where
 a := ↑(totalQty ys)
 b := ↑(totalQty xs)
-/
#guard_msgs in
example (xs ys : List Order) : totalQty xs ≥ totalQty ys := by
  omega
-- ANCHOR_END: omega_fails

-- ANCHOR: place_ok
/-- What a successful `place` did: the order did not cross the book, and it
was appended to the orders with the next id. -/
theorem place_ok {book book' : Book} {trader : String} {side : Side}
    {price qty id : Nat} (h : book.place trader side price qty = .ok (id, book')) :
    book.crossing side price = none ∧
      book'.orders = book.orders ++ [{ id := book.nextId, trader, side, price, qty }] := by
  unfold Book.place at h
  split at h            -- the `if qty = 0` in `place`
  · contradiction       -- that branch returned an error, not `.ok`
  · split at h          -- the `if price = 0`
    · contradiction
    · split at h        -- the `match` on `book.crossing side price`
      · contradiction
      · rename_i hcross -- hcross : book.crossing side price = none
        cases h         -- `.ok (book.nextId, {...}) = .ok (id, book')` fixes id and book'
        exact ⟨hcross, rfl⟩
-- ANCHOR_END: place_ok

-- ANCHOR: volume_place
/-- Placing an order adds its quantity to the volume of its side... -/
theorem volume_place {book book' : Book} {trader : String} {side : Side}
    {price qty id : Nat} (h : book.place trader side price qty = .ok (id, book')) :
    book'.volume side = book.volume side + qty := by
  have hord := (place_ok h).2
  simp [Book.volume, Book.onSide, hord, List.filter_append, totalQty_append, totalQty]

/-- ...and leaves the other side alone. -/
theorem volume_place_other {book book' : Book} {trader : String} {side other : Side}
    {price qty id : Nat} (h : book.place trader side price qty = .ok (id, book'))
    (hother : other ≠ side) : book'.volume other = book.volume other := by
  have hord := (place_ok h).2
  simp [Book.volume, Book.onSide, hord, List.filter_append, Ne.symm hother]
-- ANCHOR_END: volume_place

-- ANCHOR: cancel
/-- After a successful cancellation, no order with that id is left. -/
theorem cancel_removes {book book' : Book} {id : Nat} {order : Order}
    (h : book.cancel id = .ok (order, book')) : book'.find? id = none := by
  unfold Book.cancel at h
  split at h
  · contradiction
  · cases h
    simp [Book.find?]
-- ANCHOR_END: cancel

-- ANCHOR: sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem unfinished (book : Book) : book.volume .buy ≤ totalQty book.orders := by
  sorry

/-- info: 'Ch02.unfinished' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms unfinished
-- ANCHOR_END: sorry

/-! ## The book is never crossed

The proofs below use tactics that Chapter 4 introduces properly (`intro`,
`obtain`, `rcases`, `cases` on a hypothesis) and two lemmas about `List.max?`
and `List.min?` from Lean's core library. -/

-- ANCHOR: uncrossed_def
/-- A book is *uncrossed* when every bid is strictly below every ask. -/
def Book.Uncrossed (book : Book) : Prop :=
  ∀ b ∈ book.orders, ∀ s ∈ book.orders,
    b.side = .buy → s.side = .sell → b.price < s.price
-- ANCHOR_END: uncrossed_def

/-- If a sell at `price` does not cross, every bid is below `price`. -/
theorem lt_of_not_crossing_sell {book : Book} {price : Nat}
    (h : book.crossing .sell price = none) {b : Order}
    (hb : b ∈ book.orders) (hbuy : b.side = .buy) : b.price < price := by
  have hmem : b.price ∈ (book.onSide .buy).map (·.price) := by
    simp only [Book.onSide, List.mem_map, List.mem_filter]
    exact ⟨b, ⟨hb, by simp [hbuy]⟩, rfl⟩
  cases hbid : book.bestBid with
  | none =>
    simp only [Book.bestBid, List.max?_eq_none_iff] at hbid
    simp [hbid] at hmem
  | some m =>
    have hle : b.price ≤ m := (List.max?_le_iff hbid).1 (Nat.le_refl m) _ hmem
    simp [Book.crossing, hbid, Option.filter] at h
    omega

/-- If a buy at `price` does not cross, every ask is above `price`. -/
theorem lt_of_not_crossing_buy {book : Book} {price : Nat}
    (h : book.crossing .buy price = none) {s : Order}
    (hs : s ∈ book.orders) (hsell : s.side = .sell) : price < s.price := by
  have hmem : s.price ∈ (book.onSide .sell).map (·.price) := by
    simp only [Book.onSide, List.mem_map, List.mem_filter]
    exact ⟨s, ⟨hs, by simp [hsell]⟩, rfl⟩
  cases hask : book.bestAsk with
  | none =>
    simp only [Book.bestAsk, List.min?_eq_none_iff] at hask
    simp [hask] at hmem
  | some m =>
    have hle : m ≤ s.price := (List.le_min?_iff hask).1 (Nat.le_refl m) _ hmem
    simp [Book.crossing, hask, Option.filter] at h
    omega

-- ANCHOR: place_uncrossed
/-- `place` preserves the invariant: an uncrossed book stays uncrossed. -/
theorem place_uncrossed {book book' : Book} {trader : String} {side : Side}
    {price qty id : Nat} (hinv : book.Uncrossed)
    (h : book.place trader side price qty = .ok (id, book')) : book'.Uncrossed := by
  obtain ⟨hcross, hord⟩ := place_ok h
  intro b hb s hs hbuy hsell
  rw [hord, List.mem_append, List.mem_singleton] at hb hs
  rcases hb with hb | rfl <;> rcases hs with hs | rfl
  · -- an old bid and an old ask: the invariant of the old book
    exact hinv b hb s hs hbuy hsell
  · -- an old bid and the new ask: the new order is a sell that did not cross
    simp only at hsell
    subst hsell
    exact lt_of_not_crossing_sell hcross hb hbuy
  · -- the new bid and an old ask: the new order is a buy that did not cross
    simp only at hbuy
    subst hbuy
    exact lt_of_not_crossing_buy hcross hs hsell
  · -- the new order would be both a buy and a sell
    simp only at hbuy hsell
    rw [hbuy] at hsell
    contradiction
-- ANCHOR_END: place_uncrossed

-- ANCHOR: spread_safe
/-- In an uncrossed book the best bid is below the best ask, so the
subtraction in `spread` (and in Rust's `spread`) never truncates. -/
theorem bestBid_lt_bestAsk {book : Book} (hinv : book.Uncrossed) {bid ask : Nat}
    (hbid : book.bestBid = some bid) (hask : book.bestAsk = some ask) : bid < ask := by
  have hb := List.max?_mem hbid
  have ha := List.min?_mem hask
  simp only [Book.onSide, List.mem_map, List.mem_filter] at hb ha
  obtain ⟨b, ⟨hb, hbuy⟩, rfl⟩ := hb
  obtain ⟨s, ⟨hs, hsell⟩, rfl⟩ := ha
  exact hinv b hb s hs (by simpa using hbuy) (by simpa using hsell)
-- ANCHOR_END: spread_safe

-- ANCHOR: empty_uncrossed
theorem empty_uncrossed : Book.empty.Uncrossed := by
  simp [Book.Uncrossed, Book.empty]

example : demoBook.Uncrossed := by
  unfold Book.Uncrossed
  decide
-- ANCHOR_END: empty_uncrossed

end Ch02
