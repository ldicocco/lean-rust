import Mathlib.Data.Nat.Notation

/-!
# Chapter 31 · Induction on lists and trees

Why an induction hypothesis must sometimes be generalized (a tail-recursive
reverse), structural induction on binary trees with two induction hypotheses,
`simp` lemmas, and `simp?`.
-/

namespace Ch31

variable {α : Type}

-- ANCHOR: rev_acc
/-- Reverse with an accumulator: tail-recursive, and linear time. -/
def revAcc : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def fastReverse (xs : List α) : List α := revAcc xs []
-- ANCHOR_END: rev_acc

-- ANCHOR: rev_acc_stuck
/--
error: unsolved goals
case cons
α : Type
x : α
xs : List α
ih : revAcc xs [] = xs.reverse
⊢ revAcc xs [x] = xs.reverse ++ [x]
-/
#guard_msgs in
theorem fastReverse_eq_attempt (xs : List α) : revAcc xs [] = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [revAcc, List.reverse_cons]
-- ANCHOR_END: rev_acc_stuck

-- ANCHOR: rev_acc_general
/-- The general statement: for *every* accumulator. -/
theorem revAcc_eq (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
    -- goal: revAcc [] acc = [].reverse ++ acc
    rfl
  | cons x xs ih =>
    -- ih   : ∀ (acc : List α), revAcc xs acc = xs.reverse ++ acc
    -- goal : revAcc (x :: xs) acc = (x :: xs).reverse ++ acc
    rw [revAcc, ih (x :: acc)]
    -- goal : xs.reverse ++ x :: acc = (x :: xs).reverse ++ acc
    simp

theorem fastReverse_eq (xs : List α) : fastReverse xs = xs.reverse := by
  rw [fastReverse, revAcc_eq, List.append_nil]
-- ANCHOR_END: rev_acc_general

-- ANCHOR: tree
/-- Binary trees with a value at every node. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

namespace Tree

def size : Tree α → ℕ
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

/-- The elements from left to right. -/
def toList : Tree α → List α
  | leaf => []
  | node l x r => l.toList ++ [x] ++ r.toList

/-- Swap the children of every node. -/
def mirror : Tree α → Tree α
  | leaf => leaf
  | node l x r => node r.mirror x l.mirror
-- ANCHOR_END: tree

-- ANCHOR: tree_theorems
/-- The induction principle for trees gives two hypotheses, one per child. -/
theorem mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    -- ihl : l.mirror.mirror = l,  ihr : r.mirror.mirror = r
    rw [mirror, mirror, ihl, ihr]

theorem length_toList (t : Tree α) : t.toList.length = t.size := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    simp only [toList, size, List.length_append, List.length_singleton, ihl, ihr]

@[simp] theorem toList_mirror (t : Tree α) : t.mirror.toList = t.toList.reverse := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    simp [mirror, toList, ihl, ihr]
-- ANCHOR_END: tree_theorems

-- ANCHOR: simp_attr
/-- Because `toList_mirror` is tagged `@[simp]`, `simp` uses it on its own. -/
example (t : Tree α) : t.mirror.mirror.toList = t.toList := by
  simp

/--
info: Try this:
  [apply] simp only [toList_mirror, List.reverse_reverse]
-/
#guard_msgs in
example (t : Tree α) : t.mirror.mirror.toList = t.toList := by
  simp?
-- ANCHOR_END: simp_attr

end Tree

end Ch31
