import Mathlib.Data.Nat.Notation

/-!
# Chapter 11 · Zippers

The derivative of the list type is a pair of lists (the elements before and
after a hole). Plugging a value into the hole gives a list with a focused
position: a *zipper*. We define it, move the focus, and prove that moving never
changes the underlying list and that a move to the right can be undone by a
move to the left.
-/

namespace Ch11

-- ANCHOR: zipper
/-- A list with one position in focus. `before` holds the elements to the left
of the focus, nearest first (so it is stored reversed). -/
structure Zipper (α : Type) where
  before : List α
  focus : α
  after : List α
deriving Repr

namespace Zipper

variable {α : Type}

/-- Forget the focus: the list the zipper represents. -/
def toList (z : Zipper α) : List α := z.before.reverse ++ z.focus :: z.after

/-- Focus on the first element of a nonempty list. -/
def ofList : List α → Option (Zipper α)
  | [] => none
  | a :: as => some ⟨[], a, as⟩

/-- Move the focus one step right, if there is an element there. -/
def right (z : Zipper α) : Option (Zipper α) :=
  match z.after with
  | [] => none
  | b :: bs => some ⟨z.focus :: z.before, b, bs⟩

/-- Move the focus one step left, if there is an element there. -/
def left (z : Zipper α) : Option (Zipper α) :=
  match z.before with
  | [] => none
  | b :: bs => some ⟨bs, b, z.focus :: z.after⟩

/-- Change the focused element: constant time, wherever the focus is. -/
def modify (f : α → α) (z : Zipper α) : Zipper α := { z with focus := f z.focus }
-- ANCHOR_END: zipper

-- ANCHOR: zipper_eval
/-- info: some [1, 2, 300, 4] -/
#guard_msgs in
#eval do
  let z ← ofList [1, 2, 3, 4]
  let z ← z.right
  let z ← z.right
  pure (z.modify (· * 100)).toList
-- ANCHOR_END: zipper_eval

-- ANCHOR: zipper_proofs
/-- Moving right does not change the list. -/
theorem toList_right {z z' : Zipper α} (h : z.right = some z') :
    z'.toList = z.toList := by
  rcases z with ⟨bef, x, aft⟩
  cases aft with
  | nil =>
    -- `right` returned `none`, so `h : none = some z'` is impossible.
    simp [right] at h
  | cons b bs =>
    -- `right` returned the zipper ⟨x :: bef, b, bs⟩, so that is z'.
    simp only [right, Option.some.injEq] at h
    subst h
    -- Goal: (x :: bef).reverse ++ b :: bs = bef.reverse ++ x :: b :: bs
    simp [toList]

/-- A step right followed by a step left comes back to the same zipper. -/
theorem left_of_right {z z' : Zipper α} (h : z.right = some z') :
    z'.left = some z := by
  rcases z with ⟨bef, x, aft⟩
  cases aft with
  | nil => simp [right] at h
  | cons b bs =>
    simp only [right, Option.some.injEq] at h
    subst h
    rfl

/-- Focusing on a list does not change it either. -/
theorem toList_ofList {xs : List α} {z : Zipper α} (h : ofList xs = some z) :
    z.toList = xs := by
  cases xs with
  | nil => simp [ofList] at h
  | cons a as =>
    simp only [ofList, Option.some.injEq] at h
    subst h
    rfl
-- ANCHOR_END: zipper_proofs

end Zipper

end Ch11
