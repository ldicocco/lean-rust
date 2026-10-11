import Book.Ch31.BinarySearch

/-!
# Chapter 31 · Expected outputs for differential testing

The verified models of `Sorting.lean` and `BinarySearch.lean`, run on a fixed
set of inputs. The table they print is pinned by `#guard_msgs` (so it is
re-checked every time this file is built) and read by the Rust example
`code/rust/examples/ch31_sort.rs`, which runs its own implementations on the
same inputs and compares the results line by line.
-/

namespace Ch31

-- ANCHOR: inputs
/-- A linear congruential generator: reproducible pseudo-random numbers. -/
def lcgNext (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random integers between -9 and 9, starting from seed `s`. -/
def randomList : ℕ → ℕ → List ℤ
  | _, 0 => []
  | s, n + 1 =>
    let s' := lcgNext s
    let x : ℤ := ((s' / 65536 % 19 : ℕ) : ℤ) - 9
    x :: randomList s' n

/-- Edge cases first, then pseudo-random lists with many duplicates. -/
def sortInputs : List (List ℤ) :=
  [[], [5], [2, 1], [4, 3, 2, 1], [5, -2, 5, 0, -2]] ++
    (List.range 4).map fun k => randomList (k + 1) (k + 6)

/-- Keys to look for in a sorted list: its smallest element (often repeated),
zero (sometimes present) and ten (never present). -/
def searchKeys (ys : List ℤ) : List ℤ := [ys.headD 0, 0, 10]
-- ANCHOR_END: inputs

-- ANCHOR: lines
def showResult : Option ℕ → String
  | some i => s!"some {i}"
  | none => "none"

def sortLine (xs : List ℤ) : String :=
  s!"sort {xs} = {(sort xs).val}"

def searchLine (xs : List ℤ) (x : ℤ) : String :=
  s!"search {xs} {x} = {showResult (search xs.toArray x)}"

/-- Every sort case, then every key in the sorted random lists. -/
def table : List String :=
  sortInputs.map sortLine ++
    ((sortInputs.drop 4).map isort).flatMap fun ys => (searchKeys ys).map (searchLine ys)
-- ANCHOR_END: lines

-- ANCHOR: table
/--
info: sort [] = []
sort [5] = [5]
sort [2, 1] = [1, 2]
sort [4, 3, 2, 1] = [1, 2, 3, 4]
sort [5, -2, 5, 0, -2] = [-2, -2, 0, 5, 5]
sort [-5, -8, -4, 7, -4, -6] = [-8, -6, -5, -4, -4, 7]
sort [6, 8, 8, 4, 7, -8, 4] = [-8, 4, 4, 6, 7, 8, 8]
sort [-8, -8, 1, 0, -2, -2, 3, -8] = [-8, -8, -8, -2, -2, 0, 1, 3]
sort [3, 8, -6, -3, 8, 3, -5, 1, -8] = [-8, -6, -5, -3, 1, 3, 3, 8, 8]
search [-2, -2, 0, 5, 5] -2 = some 1
search [-2, -2, 0, 5, 5] 0 = some 2
search [-2, -2, 0, 5, 5] 10 = none
search [-8, -6, -5, -4, -4, 7] -8 = some 0
search [-8, -6, -5, -4, -4, 7] 0 = none
search [-8, -6, -5, -4, -4, 7] 10 = none
search [-8, 4, 4, 6, 7, 8, 8] -8 = some 0
search [-8, 4, 4, 6, 7, 8, 8] 0 = none
search [-8, 4, 4, 6, 7, 8, 8] 10 = none
search [-8, -8, -8, -2, -2, 0, 1, 3] -8 = some 2
search [-8, -8, -8, -2, -2, 0, 1, 3] 0 = some 5
search [-8, -8, -8, -2, -2, 0, 1, 3] 10 = none
search [-8, -6, -5, -3, 1, 3, 3, 8, 8] -8 = some 0
search [-8, -6, -5, -3, 1, 3, 3, 8, 8] 0 = none
search [-8, -6, -5, -3, 1, 3, 3, 8, 8] 10 = none
-/
#guard_msgs in
#eval for line in table do IO.println line
-- ANCHOR_END: table

end Ch31
