import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Chapter 30 · Matrices with dimensions in their types

Integer matrices indexed by their dimensions, built from scratch (`Mat m n`):
multiplication whose type demands matching inner dimensions, transpose,
identity, vertical stacking with `m + n` rows, and the laws (associativity,
identity, transpose of a product, stacking distributes over products), all
proved. Then Mathlib's `Matrix (Fin m) (Fin n) α`, and a proof that our
multiplication agrees with Mathlib's.
-/

namespace Ch30

-- ANCHOR: mat
/-- An `m × n` matrix of integers: an entry for every row index `i : Fin m` and
column index `j : Fin n`. -/
@[ext]
structure Mat (m n : ℕ) where
  entry : Fin m → Fin n → ℤ
-- ANCHOR_END: mat

namespace Mat

variable {m n p q : ℕ}

-- ANCHOR: ops
/-- `(m × n) * (n × p) = (m × p)`: the inner dimensions are the same `n`. -/
def mul (A : Mat m n) (B : Mat n p) : Mat m p :=
  ⟨fun i k => ∑ j, A.entry i j * B.entry j k⟩

instance : HMul (Mat m n) (Mat n p) (Mat m p) := ⟨mul⟩

def transpose (A : Mat m n) : Mat n m := ⟨fun i j => A.entry j i⟩

/-- The identity matrix exists only for square shapes. -/
def one (n : ℕ) : Mat n n := ⟨fun i j => if i = j then 1 else 0⟩

/-- Stack `A` on top of `B`: the result has `m + n` rows. -/
def vstack (A : Mat m q) (B : Mat n q) : Mat (m + n) q :=
  ⟨Fin.append A.entry B.entry⟩
-- ANCHOR_END: ops

-- ANCHOR: entry_lemmas
/-- How to compute an entry of each operation. The `simp` attribute lets the
`simp` tactic use these equations, left to right, on its own. -/
@[simp] theorem mul_entry (M : Mat m n) (N : Mat n p) (i : Fin m) (k : Fin p) :
    (M * N).entry i k = ∑ j, M.entry i j * N.entry j k := rfl

@[simp] theorem transpose_entry (M : Mat m n) (i : Fin n) (j : Fin m) :
    M.transpose.entry i j = M.entry j i := rfl

@[simp] theorem one_entry (i j : Fin n) :
    (one n).entry i j = if i = j then 1 else 0 := rfl
-- ANCHOR_END: entry_lemmas

-- ANCHOR: lists
/-- The rows, for printing. -/
def toLists (A : Mat m n) : List (List ℤ) :=
  List.ofFn fun i => List.ofFn fun j => A.entry i j

/-- From run-time data: succeeds only if the shape is exactly `m × n`. -/
def ofLists? (m n : ℕ) (rows : List (List ℤ)) : Option (Mat m n) :=
  if h : rows.length = m ∧ ∀ r ∈ rows, r.length = n then
    some ⟨fun i j =>
      let row := rows[i.val]'(by omega)
      row[j.val]'(by
        have hr : row.length = n := h.2 row (List.getElem_mem _)
        omega)⟩
  else
    none
-- ANCHOR_END: lists

-- ANCHOR: samples
def A : Mat 2 3 := ⟨![![1, 2, 3], ![4, 5, 6]]⟩
def B : Mat 3 2 := ⟨![![7, 8], ![9, 10], ![11, 12]]⟩
-- ANCHOR_END: samples

-- ANCHOR: samples_eval
/-- info: [[58, 64], [139, 154]] -/
#guard_msgs in
#eval (A * B).toLists

/-- info: [[39, 54, 69], [49, 68, 87], [59, 82, 105]] -/
#guard_msgs in
#eval (B * A).toLists

/-- info: [[1, 2, 3], [4, 5, 6], [1, 4], [2, 5], [3, 6]] -/
#guard_msgs in
#eval A.toLists ++ A.transpose.toLists

/-- info: [[1, 2, 3], [4, 5, 6], [1, 2, 3], [4, 5, 6]] -/
#guard_msgs in
#eval (A.vstack A).toLists
-- ANCHOR_END: samples_eval

-- ANCHOR: of_lists_eval
/-- info: some [[1, 2, 3], [4, 5, 6]] -/
#guard_msgs in
#eval (ofLists? 2 3 [[1, 2, 3], [4, 5, 6]]).map toLists

/-- info: none -/
#guard_msgs in
#eval (ofLists? 2 3 [[1, 2, 3], [4, 5]]).map toLists
-- ANCHOR_END: of_lists_eval

-- ANCHOR: mismatch
/--
error: Application type mismatch: The last
  A
argument has type
  Mat 2 3
but is expected to have type
  Mat 3 ?m.5
in the application
  A.mul A
-/
#guard_msgs in
example := A.mul A
-- ANCHOR_END: mismatch

-- ANCHOR: laws
theorem transpose_transpose (M : Mat m n) : M.transpose.transpose = M := rfl

theorem transpose_mul (M : Mat m n) (N : Mat n p) :
    (M * N).transpose = N.transpose * M.transpose := by
  ext k i
  -- goal: (M * N).transpose.entry k i = (N.transpose * M.transpose).entry k i
  simp only [transpose_entry, mul_entry]
  -- goal: ∑ j, M.entry i j * N.entry j k = ∑ j, N.entry j k * M.entry i j
  simp only [Int.mul_comm]

theorem mul_one (M : Mat m n) : M * one n = M := by
  ext i j
  -- goal after the simp lemmas: ∑ k, M.entry i k * (if k = j then 1 else 0) = M.entry i j
  simp

theorem mul_assoc (L : Mat m n) (M : Mat n p) (N : Mat p q) :
    (L * M) * N = L * (M * N) := by
  ext i l
  simp only [mul_entry]
  -- goal: ∑ k, (∑ j, L i j * M j k) * N k l = ∑ j, L i j * ∑ k, M j k * N k l
  simp only [Finset.sum_mul, Finset.mul_sum]   -- push the products inside the sums
  rw [Finset.sum_comm]                          -- swap the order of summation
  simp only [Int.mul_assoc]
-- ANCHOR_END: laws

-- ANCHOR: vstack_mul
/-- Multiplying a stack multiplies each block. -/
theorem vstack_mul (A₁ : Mat m n) (A₂ : Mat p n) (B : Mat n q) :
    (vstack A₁ A₂) * B = vstack (A₁ * B) (A₂ * B) := by
  ext i k
  -- a row index of the stack is a row of `A₁` or a row of `A₂`
  cases i using Fin.addCases with
  | left i => simp [vstack]
  | right i => simp [vstack]
-- ANCHOR_END: vstack_mul

-- ANCHOR: to_matrix
/-- Our matrices are Mathlib's, with the dimensions turned into index types. -/
def toMatrix (M : Mat m n) : Matrix (Fin m) (Fin n) ℤ := M.entry

theorem toMatrix_mul (M : Mat m n) (N : Mat n p) :
    toMatrix (M * N) = toMatrix M * toMatrix N := by
  ext i k
  rw [Matrix.mul_apply]   -- Mathlib's definition of an entry of a product
  rfl                     -- ... is ours, entry by entry
-- ANCHOR_END: to_matrix

-- ANCHOR: transfer
theorem toMatrix_injective {M N : Mat m n} (h : toMatrix M = toMatrix N) : M = N :=
  Mat.ext h

/-- Associativity again, this time borrowed from Mathlib's `Matrix.mul_assoc`. -/
theorem mul_assoc' (L : Mat m n) (M : Mat n p) (N : Mat p q) :
    (L * M) * N = L * (M * N) := by
  apply toMatrix_injective
  rw [toMatrix_mul, toMatrix_mul, toMatrix_mul, toMatrix_mul]
  exact Matrix.mul_assoc (toMatrix L) (toMatrix M) (toMatrix N)
-- ANCHOR_END: transfer

end Mat

-- ANCHOR: some_mat
/-- A matrix of some shape, known only at run time: a Σ-type with two
indices. -/
abbrev SomeMat := (m : ℕ) × (n : ℕ) × Mat m n

/-- Read the shape from the data, then check that the data has that shape. -/
def SomeMat.ofLists (rows : List (List ℤ)) : Option SomeMat :=
  let m := rows.length
  let n := (rows.headD []).length
  (Mat.ofLists? m n rows).map fun M => ⟨m, n, M⟩

/-- Multiply two matrices of unknown shapes. The test `h : n' = n` is decided
at run time; its proof turns `B : Mat n' p` into a `Mat n p`, and from there on
the dimension-checked `*` takes over. -/
def SomeMat.mul : SomeMat → SomeMat → Option SomeMat
  | ⟨m, n, A⟩, ⟨n', p, B⟩ =>
    if h : n' = n then some ⟨m, p, A * (h ▸ B)⟩ else none

def SomeMat.toLists (M : SomeMat) : List (List ℤ) := M.2.2.toLists

/-- Parse both inputs and multiply them, or explain what went wrong. -/
def multiplyText (xs ys : List (List ℤ)) : String :=
  match SomeMat.ofLists xs, SomeMat.ofLists ys with
  | some A, some B =>
    match A.mul B with
    | some C => s!"{A.1}x{A.2.1} * {B.1}x{B.2.1} = {C.toLists}"
    | none => s!"cannot multiply {A.1}x{A.2.1} by {B.1}x{B.2.1}"
  | _, _ => "ragged input"
-- ANCHOR_END: some_mat

-- ANCHOR: some_mat_eval
/-- info: "2x3 * 3x2 = [[58, 64], [139, 154]]" -/
#guard_msgs in
#eval multiplyText [[1, 2, 3], [4, 5, 6]] [[7, 8], [9, 10], [11, 12]]

/-- info: "cannot multiply 2x3 by 2x3" -/
#guard_msgs in
#eval multiplyText [[1, 2, 3], [4, 5, 6]] [[1, 2, 3], [4, 5, 6]]

/-- info: "ragged input" -/
#guard_msgs in
#eval multiplyText [[1, 2, 3], [4, 5]] [[1], [2], [3]]
-- ANCHOR_END: some_mat_eval

-- ANCHOR: mathlib
/-- info: !![58, 64; 139, 154] -/
#guard_msgs in
#eval !![1, 2, 3; 4, 5, 6] * !![7, 8; 9, 10; 11, 12]

-- ANCHOR_END: mathlib

-- ANCHOR: from_rows
/--
info: Matrix.fromRows.{u_1, u_3, u_4, u_5} {R : Type u_1} {m₁ : Type u_3} {m₂ : Type u_4} {n : Type u_5} (A₁ : Matrix m₁ n R)
  (A₂ : Matrix m₂ n R) : Matrix (m₁ ⊕ m₂) n R
-/
#guard_msgs in
#check Matrix.fromRows
-- ANCHOR_END: from_rows

end Ch30
