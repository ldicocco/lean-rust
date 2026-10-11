import Book.Ch31.Sorting

/-!
# Chapter 31 · A verified binary search

Binary search on an array of integers, defined by well-founded recursion on the
width of the search interval, with proofs that a returned index points at the
key (soundness) and that `none` is returned only when the key is absent from a
sorted array (completeness). Sortedness for arrays is connected to Mathlib's
`List.SortedLE`, so the output of the verified sort can be searched.
-/

namespace Ch31

open scoped List

-- ANCHOR: search
/-- Search for `x` in the index interval `[lo, hi)` of `a`. -/
def searchFrom (a : Array ℤ) (x : ℤ) (lo hi : ℕ) (hhi : hi ≤ a.size) : Option ℕ :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    -- `a[mid]` below needs this fact; Lean finds it in the context.
    have hmid : mid < a.size := by omega
    if x < a[mid] then searchFrom a x lo mid (by omega)
    else if a[mid] < x then searchFrom a x (mid + 1) hi hhi
    else some mid
  else none
termination_by hi - lo

def search (a : Array ℤ) (x : ℤ) : Option ℕ :=
  searchFrom a x 0 a.size (Nat.le_refl _)
-- ANCHOR_END: search

-- ANCHOR: search_eval
/-- info: [some 0, some 3, none, none, none] -/
#guard_msgs in
#eval [2, 11, 4, 1, 20].map (search #[2, 3, 7, 11, 13])
-- ANCHOR_END: search_eval

-- ANCHOR: sorted_arr
/-- Sorted, for arrays: an element is never larger than a later one. -/
def SortedArr (a : Array ℤ) : Prop :=
  ∀ (i j : ℕ) (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]
-- ANCHOR_END: sorted_arr

-- ANCHOR: search_sound
/-- Soundness: a returned index is in bounds and points at `x`. -/
theorem searchFrom_some (a : Array ℤ) (x : ℤ) (lo hi : ℕ) (hhi : hi ≤ a.size) (i : ℕ) :
    searchFrom a x lo hi hhi = some i → ∃ h : i < a.size, a[i] = x := by
  fun_induction searchFrom a x lo hi hhi with
  | case1 lo hi hhi h mid hmid hlt ih =>
    -- went left: the goal is literally the induction hypothesis
    exact ih
  | case2 lo hi hhi h mid hmid hnlt hgt ih =>
    -- went right: the same
    exact ih
  | case3 lo hi hhi h mid hmid hnlt hngt =>
    -- found: the result is `some mid`
    intro hsome
    injection hsome with hmi        -- hmi : mid = i
    subst hmi
    exact ⟨hmid, by omega⟩          -- ¬ x < a[mid] and ¬ a[mid] < x give a[mid] = x
  | case4 lo hi hhi h =>
    -- empty interval: the result is `none`, which is not `some i`
    intro hnone
    cases hnone
-- ANCHOR_END: search_sound

-- ANCHOR: search_complete
/-- Completeness: on a sorted array, `none` means that no index in `[lo, hi)`
holds `x`. -/
theorem searchFrom_none (a : Array ℤ) (hs : SortedArr a) (x : ℤ) (lo hi : ℕ)
    (hhi : hi ≤ a.size) :
    searchFrom a x lo hi hhi = none →
      ∀ (k : ℕ) (hk : k < a.size), lo ≤ k → k < hi → a[k] ≠ x := by
  fun_induction searchFrom a x lo hi hhi with
  | case1 lo hi hhi h mid hmid hlt ih =>
    -- x < a[mid]: we searched [lo, mid); everything from mid on is too big
    intro hnone k hk hlo hkhi
    by_cases hkm : k < mid
    · exact ih hnone k hk hlo hkm
    · have hle : a[mid] ≤ a[k] := hs mid k hmid hk (by omega)
      omega                          -- x < a[mid] ≤ a[k], so a[k] ≠ x
  | case2 lo hi hhi h mid hmid hnlt hgt ih =>
    -- a[mid] < x: we searched [mid + 1, hi); everything up to mid is too small
    intro hnone k hk hlo hkhi
    by_cases hkm : mid < k
    · exact ih hnone k hk (by omega) hkhi
    · have hle : a[k] ≤ a[mid] := hs k mid hk hmid (by omega)
      omega                          -- a[k] ≤ a[mid] < x
  | case3 lo hi hhi h mid hmid hnlt hngt =>
    -- found: `some mid` is not `none`
    intro hnone
    cases hnone
  | case4 lo hi hhi h =>
    -- empty interval: there is no k with lo ≤ k < hi
    intro _ k hk hlo hkhi
    omega
-- ANCHOR_END: search_complete

-- ANCHOR: search_spec
theorem search_some {a : Array ℤ} {x : ℤ} {i : ℕ} (h : search a x = some i) :
    ∃ h : i < a.size, a[i] = x :=
  searchFrom_some a x 0 a.size _ i h

theorem search_none {a : Array ℤ} {x : ℤ} (hs : SortedArr a) (h : search a x = none) :
    x ∉ a := by
  intro hx
  obtain ⟨k, hk, hkx⟩ := Array.mem_iff_getElem.mp hx
  exact searchFrom_none a hs x 0 a.size _ h k hk (Nat.zero_le k) hk hkx

/-- The whole specification in one line, for sorted arrays. -/
theorem search_isSome_iff {a : Array ℤ} {x : ℤ} (hs : SortedArr a) :
    (search a x).isSome ↔ x ∈ a := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hlt, heq⟩ := search_some hi
    exact Array.mem_iff_getElem.mpr ⟨i, hlt, heq⟩
  · intro hx
    cases hr : search a x with
    | none => exact absurd hx (search_none hs hr)
    | some i => rfl
-- ANCHOR_END: search_spec

-- ANCHOR: search_subtype
/-- The specification as a type, once more. -/
def searchChecked (a : Array ℤ) (hs : SortedArr a) (x : ℤ) :
    { r : Option ℕ //
      (∀ i, r = some i → ∃ h : i < a.size, a[i] = x) ∧ (r = none → x ∉ a) } :=
  ⟨search a x, fun _ h => search_some h, fun h => search_none hs h⟩
-- ANCHOR_END: search_subtype

-- ANCHOR: sorted_bridge
/-- Mathlib's sortedness of the underlying list gives ours. -/
theorem sortedArr_of_sortedLE {a : Array ℤ} (h : a.toList.SortedLE) : SortedArr a := by
  intro i j hi hj hij
  have hl := List.sortedLE_iff_getElem_le_getElem_of_le.mp h
    (i := i) (j := j) (hi := by simpa using hi) (hj := by simpa using hj) hij
  simpa using hl

/-- Searching the output of the verified sort finds exactly the input's elements. -/
theorem search_isort (xs : List ℤ) (x : ℤ) :
    (search (isort xs).toArray x).isSome ↔ x ∈ xs := by
  have hs : SortedArr (isort xs).toArray :=
    sortedArr_of_sortedLE (by simpa using isort_sorted xs)
  rw [search_isSome_iff hs, List.mem_toArray]
  exact (isort_perm xs).mem_iff
-- ANCHOR_END: sorted_bridge

-- ANCHOR: axioms
/-- info: 'Ch31.search_isort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms search_isort
-- ANCHOR_END: axioms

end Ch31
