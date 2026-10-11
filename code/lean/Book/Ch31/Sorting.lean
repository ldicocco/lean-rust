import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Chapter 31 · A verified insertion sort

Insertion sort on lists of integers, with its specification (the output is
sorted and is a permutation of the input) stated with Mathlib's
`List.SortedLE` and `List.Perm`, proved from scratch, and packaged as a subtype.
Then: a sorted permutation is unique, so our sort equals Mathlib's
`List.insertionSort` and core Lean's `List.mergeSort` on every input; and a
bound on the number of comparisons, proved with `calc`, `ring` and `linarith`.
-/

namespace Ch31

-- `l₁ ~ l₂` is notation for `List.Perm l₁ l₂`; it lives in the `List` namespace.
open scoped List

-- ANCHOR: insert
/-- Insert `x` into a list, before the first element that is at least `x`.
If the list is sorted, so is the result. -/
def insertSorted (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Sort the tail, then insert the head. -/
def isort : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertSorted x (isort xs)
-- ANCHOR_END: insert

-- ANCHOR: isort_eval
/-- info: [-3, 1, 2, 5, 5, 9] -/
#guard_msgs in
#eval isort [5, 2, 9, -3, 5, 1]
-- ANCHOR_END: isort_eval

-- ANCHOR: perm_def
/--
info: inductive List.Perm.{u} : {α : Type u} → List α → List α → Prop
number of parameters: 1
constructors:
List.Perm.nil : ∀ {α : Type u}, [] ~ []
List.Perm.cons : ∀ {α : Type u} (x : α) {l₁ l₂ : List α}, l₁ ~ l₂ → x :: l₁ ~ x :: l₂
List.Perm.swap : ∀ {α : Type u} (x y : α) (l : List α), y :: x :: l ~ x :: y :: l
List.Perm.trans : ∀ {α : Type u} {l₁ l₂ l₃ : List α}, l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃
-/
#guard_msgs in
#print List.Perm
-- ANCHOR_END: perm_def

-- ANCHOR: sorted_def
example (l : List ℤ) : l.SortedLE ↔ l.Pairwise (· ≤ ·) := List.sortedLE_iff_pairwise

example : [1, 2, 2, 7].SortedLE := by decide
example : ¬ [1, 3, 2].SortedLE := by decide
-- ANCHOR_END: sorted_def

-- ANCHOR: perm_insert
/-- Inserting `x` gives a permutation of `x :: l`. -/
theorem perm_insertSorted (x : ℤ) (l : List ℤ) : insertSorted x l ~ x :: l := by
  induction l with
  | nil => exact List.Perm.refl [x]
  | cons y ys ih =>
    -- ih : insertSorted x ys ~ x :: ys
    rw [insertSorted]
    split
    · -- case x ≤ y: the result is literally x :: y :: ys
      exact List.Perm.refl _
    · -- case ¬ x ≤ y: goal y :: insertSorted x ys ~ x :: y :: ys
      calc y :: insertSorted x ys
          ~ y :: x :: ys := List.Perm.cons y ih
        _ ~ x :: y :: ys := List.Perm.swap x y ys

theorem mem_insertSorted {x z : ℤ} {l : List ℤ} :
    z ∈ insertSorted x l ↔ z = x ∨ z ∈ l := by
  rw [(perm_insertSorted x l).mem_iff, List.mem_cons]
-- ANCHOR_END: perm_insert

-- ANCHOR: sorted_insert
/-- Inserting into a sorted list gives a sorted list. -/
theorem sorted_insertSorted (x : ℤ) (l : List ℤ) (h : l.Pairwise (· ≤ ·)) :
    (insertSorted x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    -- h : (y :: ys).Pairwise (· ≤ ·), which unfolds to two facts:
    rw [List.pairwise_cons] at h
    obtain ⟨hy, hys⟩ := h       -- hy : ∀ b ∈ ys, y ≤ b    hys : ys.Pairwise (· ≤ ·)
    rw [insertSorted]
    split
    · -- case x ≤ y: goal (x :: y :: ys).Pairwise (· ≤ ·)
      rename_i hxy
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, hy, hys⟩
      -- goal: ∀ b ∈ y :: ys, x ≤ b
      intro b hb
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hxy                         -- b = y
      · calc x ≤ y := hxy                 -- b ∈ ys
          _ ≤ b := hy b hb
    · -- case ¬ x ≤ y: goal (y :: insertSorted x ys).Pairwise (· ≤ ·)
      rename_i hxy
      rw [List.pairwise_cons]
      refine ⟨?_, ih hys⟩
      -- goal: ∀ b ∈ insertSorted x ys, y ≤ b
      intro b hb
      rw [mem_insertSorted] at hb
      rcases hb with rfl | hb
      · omega                             -- b = x, and ¬ x ≤ y
      · exact hy b hb
-- ANCHOR_END: sorted_insert

-- ANCHOR: isort_correct
theorem isort_perm (xs : List ℤ) : isort xs ~ xs := by
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs ih =>
    -- goal: insertSorted x (isort xs) ~ x :: xs
    calc insertSorted x (isort xs)
        ~ x :: isort xs := perm_insertSorted x (isort xs)
      _ ~ x :: xs := List.Perm.cons x ih

theorem isort_pairwise (xs : List ℤ) : (isort xs).Pairwise (· ≤ ·) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact sorted_insertSorted x (isort xs) ih

theorem isort_sorted (xs : List ℤ) : (isort xs).SortedLE :=
  (isort_pairwise xs).sortedLE
-- ANCHOR_END: isort_correct

-- ANCHOR: sort_subtype
/-- The specification as a type: a list, together with proofs that it is
sorted and that it is a permutation of the input. -/
def sort (xs : List ℤ) : { ys : List ℤ // ys.SortedLE ∧ ys ~ xs } :=
  ⟨isort xs, isort_sorted xs, isort_perm xs⟩
-- ANCHOR_END: sort_subtype

-- ANCHOR: sort_eval
/-- info: [-3, 1, 2, 5, 5, 9] -/
#guard_msgs in
#eval (sort [5, 2, 9, -3, 5, 1]).val
-- ANCHOR_END: sort_eval

-- ANCHOR: grind
/-- The same theorem as `sorted_insertSorted`, with the case analysis, the
membership reasoning and the arithmetic left to `grind`. -/
theorem sorted_insertSorted' (x : ℤ) (l : List ℤ) (h : l.Pairwise (· ≤ ·)) :
    (insertSorted x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih => grind [insertSorted, List.pairwise_cons, mem_insertSorted]
-- ANCHOR_END: grind

-- ANCHOR: run
/-- The kernel can run the sort inside a proof: slow, but trusted. -/
example : isort [3, 1, 2] = [1, 2, 3] := by decide

/-- The numbers below 1009 that `n * 7919 % 1009` hits for `n < 1000`, in a
scrambled order. `#eval` runs the sort through Lean's compiler: fast, but
outside the kernel. -/
def scrambled : List ℤ := (List.range 1000).map fun n => (((n * 7919) % 1009 : ℕ) : ℤ)

/-- info: (1000, [0, 1, 2, 3, 4]) -/
#guard_msgs in
#eval ((sort scrambled).val.length, (sort scrambled).val.take 5)
-- ANCHOR_END: run

-- ANCHOR: unique
/-- The specification determines the output: two sorted permutations of the
same list are equal. -/
theorem sorted_perm_unique {ys zs : List ℤ} (hy : ys.SortedLE) (hz : zs.SortedLE)
    (h : ys ~ zs) : ys = zs :=
  List.Perm.eq_of_sortedLE hy hz h

/-- So our sort agrees with Mathlib's insertion sort on every input... -/
theorem isort_eq_insertionSort (xs : List ℤ) :
    isort xs = xs.insertionSort (· ≤ ·) := by
  apply sorted_perm_unique (isort_sorted xs) List.sortedLE_insertionSort
  -- goal: isort xs ~ List.insertionSort (· ≤ ·) xs
  exact (isort_perm xs).trans (List.perm_insertionSort _ xs).symm

/-- ... and with the merge sort of Lean's core library. -/
theorem isort_eq_mergeSort (xs : List ℤ) : isort xs = xs.mergeSort := by
  apply sorted_perm_unique (isort_sorted xs) List.sortedLE_mergeSort
  exact (isort_perm xs).trans (List.mergeSort_perm xs _).symm
-- ANCHOR_END: unique

-- ANCHOR: cost
/-- The number of comparisons `insertSorted x l` makes. -/
def insertCost (x : ℤ) : List ℤ → ℕ
  | [] => 0
  | y :: ys => if x ≤ y then 1 else 1 + insertCost x ys

/-- The number of comparisons `isort` makes. -/
def isortCost : List ℤ → ℕ
  | [] => 0
  | x :: xs => insertCost x (isort xs) + isortCost xs
-- ANCHOR_END: cost

-- ANCHOR: cost_bound
theorem insertCost_le (x : ℤ) (l : List ℤ) : insertCost x l ≤ l.length := by
  induction l with
  | nil => simp [insertCost]
  | cons y ys ih =>
    simp only [insertCost, List.length_cons]
    split <;> omega

/-- At most `n (n - 1) / 2` comparisons for a list of length `n`, stated
without subtraction or division. -/
theorem isortCost_le (xs : List ℤ) :
    2 * isortCost xs + xs.length ≤ xs.length * xs.length := by
  induction xs with
  | nil => simp [isortCost]
  | cons x xs ih =>
    -- one insertion into a list of length `xs.length`
    have hc : insertCost x (isort xs) ≤ xs.length := by
      have h := insertCost_le x (isort xs)
      rwa [(isort_perm xs).length_eq] at h
    rw [isortCost, List.length_cons]
    calc 2 * (insertCost x (isort xs) + isortCost xs) + (xs.length + 1)
        = (2 * isortCost xs + xs.length) + 2 * insertCost x (isort xs) + 1 := by ring
      _ ≤ xs.length * xs.length + 2 * xs.length + 1 := by linarith
      _ = (xs.length + 1) * (xs.length + 1) := by ring
-- ANCHOR_END: cost_bound

-- ANCHOR: cost_eval
/-- info: (15, 5, 3) -/
#guard_msgs in
#eval (isortCost [6, 5, 4, 3, 2, 1], isortCost [1, 2, 3, 4, 5, 6], isortCost [1, 1, 1, 1])
-- ANCHOR_END: cost_eval

end Ch31
