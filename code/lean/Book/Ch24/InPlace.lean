/-!
# Chapter 24 · Reference counting and in-place updates

Lean has no destructors that a programmer can write: memory is managed by
reference counting, and an object is freed when its count drops to zero. The
same counts let the runtime update an *unshared* value in place, even though
the language is purely functional ("functional but in place").

`dbgTraceIfShared` makes the runtime's decision observable: it prints a
message when its argument is shared (reference count above one) and is the
identity otherwise. To the logic it is just the identity, which we prove.
-/

namespace Ch24.InPlace

-- ANCHOR: bump
/-- Overwrite the first element. `Array.set!` updates the array in place when
it is the only reference to it, and copies it otherwise; `dbgTraceIfShared`
reports the copying case. -/
def bump (xs : Array Nat) : Array Nat :=
  (dbgTraceIfShared "bump" xs).set! 0 99

/-- A fresh array whose contents depend on the argument `n`, so that Lean
cannot precompute it once and share it. -/
def fresh (n : Nat) : Array Nat := Array.replicate n 0
-- ANCHOR_END: bump

-- ANCHOR: unique
/-- The array from `fresh n` has exactly one reference, which `bump` consumes. -/
def bumpFresh (n : Nat) : Array Nat := bump (fresh n)

/-- info: #[99, 0, 0] -/
#guard_msgs in
#eval bumpFresh 3
-- ANCHOR_END: unique

-- ANCHOR: shared
/-- Here `xs` is still needed after the call: it is shared, so `bump` copies. -/
def bumpAndKeep (n : Nat) : Array Nat × Array Nat :=
  let xs := fresh n
  (bump xs, xs)

/--
info: shared RC bump
---
info: (#[99, 0, 0], #[0, 0, 0])
-/
#guard_msgs in
#eval bumpAndKeep 3
-- ANCHOR_END: shared

-- ANCHOR: loop
/-- A loop that writes every slot. The array is never shared, so all `n`
updates happen in place: no message is printed. -/
def stamp (n : Nat) : Array Nat := Id.run do
  let mut xs := fresh n
  for i in [0:n] do
    xs := (dbgTraceIfShared "stamp" xs).set! i (i + 1)
  return xs

/-- info: #[1, 2, 3, 4, 5] -/
#guard_msgs in
#eval stamp 5

/-- The same loop, but every intermediate version is kept in a history. Each
update now finds the array shared (the history holds a reference), and copies. -/
def stampWithHistory (n : Nat) : List (Array Nat) := Id.run do
  let mut xs := fresh n
  let mut history := []
  for i in [0:n] do
    history := xs :: history
    xs := (dbgTraceIfShared "history" xs).set! i (i + 1)
  return (xs :: history).reverse

/--
info: shared RC history
shared RC history
shared RC history
---
info: [#[0, 0, 0], #[1, 0, 0], #[1, 2, 0], #[1, 2, 3]]
-/
#guard_msgs in
#eval stampWithHistory 3
-- ANCHOR_END: loop

-- ANCHOR: constant
/-- A closed term: computed once, stored, and shared by every use. -/
def calibration : Array Nat := #[5, 6, 7]

/--
info: shared RC bump
---
info: #[99, 6, 7]
-/
#guard_msgs in
#eval bump calibration
-- ANCHOR_END: constant

/-! ## What the logic sees -/

-- ANCHOR: logic
/-- To the logic, `dbgTraceIfShared` is the identity function: the message is
a side channel that proofs cannot observe. -/
theorem dbgTraceIfShared_eq {α : Type} (msg : String) (a : α) :
    dbgTraceIfShared msg a = a := rfl

/-- Whether `bump` copies or not, its result is the same value. -/
theorem bump_size (xs : Array Nat) : (bump xs).size = xs.size := by
  simp [bump, dbgTraceIfShared_eq]

theorem bump_first (xs : Array Nat) (h : 0 < xs.size) :
    (bump xs)[0]? = some 99 := by
  simp [bump, dbgTraceIfShared_eq, h]

theorem bump_rest (xs : Array Nat) (i : Nat) (hi : 0 < i) :
    (bump xs)[i]? = xs[i]? := by
  simp [bump, dbgTraceIfShared_eq, Nat.ne_of_lt hi]

/-- The two results of `bumpAndKeep` are different values, as the semantics
of an immutable language demands: the copy is what makes this true. -/
theorem bumpAndKeep_spec (n : Nat) (h : 0 < n) :
    (bumpAndKeep n).1[0]? = some 99 ∧ (bumpAndKeep n).2[0]? = some 0 := by
  simp [bumpAndKeep, bump, fresh, dbgTraceIfShared_eq, h]
-- ANCHOR_END: logic

end Ch24.InPlace
