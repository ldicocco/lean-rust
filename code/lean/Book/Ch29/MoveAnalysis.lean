import Book.Ch29.Dataflow
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Chapter 29 · Move analysis and liveness on `maybe_archive`

The control-flow graph of `maybe_archive` (the same seven basic blocks that
`mini-nll` builds and prints in `ch29_mir`), three gen/kill analyses solved
with the fuel-based solver of `Dataflow.lean`, the drop-flag decision, and
the least-solution theorem applied to them.
-/

namespace Ch29.MoveAnalysis

open Ch29

-- ANCHOR: gen_kill
/-- A gen/kill transfer function: add the facts `gen`, remove the facts
`kill`, keep the rest. -/
def genKill {β : Type} [DecidableEq β] (gen kill : Finset β) (x : Finset β) : Finset β :=
  gen ∪ (x \ kill)

/-- Every gen/kill function is monotone. -/
theorem genKill_mono {β : Type} [DecidableEq β] (gen kill : Finset β) :
    Monotone (genKill gen kill) := by
  intro x y hxy
  -- `≤` on finite sets is `⊆`; union and difference respect it.
  exact Finset.union_subset_union (le_refl gen) (Finset.sdiff_subset_sdiff hxy (le_refl kill))
-- ANCHOR_END: gen_kill

-- ANCHOR: cfg
/-- The basic blocks `bb0 ... bb6` and the locals `_0 ... _5`. -/
abbrev Block := Fin 7
abbrev Loc := Fin 6

/-- `bb0→bb1, bb1→bb4, bb1→bb2, bb2→bb3, bb3→bb5, bb4→bb5, bb5→bb6`. -/
def preds : Block → List Block := fun b =>
  match b.val with
  | 1 => [0] | 2 => [1] | 3 => [2] | 4 => [1] | 5 => [3, 4] | 6 => [5] | _ => []

def succs : Block → List Block := fun b =>
  match b.val with
  | 0 => [1] | 1 => [4, 2] | 2 => [3] | 3 => [5] | 4 => [5] | 5 => [6] | _ => []
-- ANCHOR_END: cfg

-- ANCHOR: maybe_uninit
/-- Maybe-uninitialized locals (forward). The gen/kill sets summarize each
block: in `bb2`, `_5 = move _2` and `archive(move _5)` move out of `_2` and
`_5` (gen) and the call initializes `_4` (kill). -/
def maybeUninit : Problem Block (Finset Loc) where
  inputs := preds
  entry := fun b => if b = 0 then {0, 2, 3, 4, 5} else ∅
  transfer := fun b =>
    match b.val with
    | 0 => genKill ∅ {2}         -- `_2 = String::from(..)`
    | 1 => genKill ∅ {3}         -- `_3 = copy _1`
    | 2 => genKill {2, 5} {4}    -- moves of `_2`, `_5`; `_4 = archive(..)`
    | 3 => genKill {4, 5} {0}    -- `StorageDead(_5)`, `StorageDead(_4)`, `_0 = ()`
    | 4 => genKill ∅ {0}         -- `_0 = ()`
    | 5 => genKill {2, 3} ∅      -- `StorageDead(_3)`, `drop(_2)`
    | _ => genKill {2} ∅         -- `StorageDead(_2)`
-- ANCHOR_END: maybe_uninit

/-- Maybe-initialized locals (forward), the dual analysis. -/
def maybeInit : Problem Block (Finset Loc) where
  inputs := preds
  entry := fun b => if b = 0 then {1} else ∅
  transfer := fun b =>
    match b.val with
    | 0 => genKill {2} ∅
    | 1 => genKill {3} ∅
    | 2 => genKill {4} {2, 5}
    | 3 => genKill {0} {4, 5}
    | 4 => genKill {0} ∅
    | 5 => genKill ∅ {2, 3}
    | _ => genKill ∅ {2}

-- ANCHOR: liveness
/-- Live locals (backward): the facts at a block are those live on *exit*,
and they flow in from the successors through each successor's transfer
function `uses ∪ (live \ defs)`. -/
def liveness : Problem Block (Finset Loc) where
  inputs := succs
  entry := fun _ => ∅
  transfer := fun b =>
    match b.val with
    | 0 => genKill ∅ {2}
    | 1 => genKill {1, 2} {3}
    | 2 => genKill {2} {4, 5}
    | 3 => genKill ∅ {0, 4, 5}
    | 4 => genKill ∅ {0}
    | 5 => genKill {2} {3}
    | _ => genKill {0} {2}
-- ANCHOR_END: liveness

/-- The facts at each block, as sorted lists of local numbers. -/
def table (r : Block → Finset Loc) : List (List ℕ) :=
  (List.finRange 7).map fun b => ((r b).sort (· ≤ ·)).map Fin.val

-- ANCHOR: eval
/-- info: some [[0, 2, 3, 4, 5], [0, 3, 4, 5], [0, 4, 5], [0, 2, 5], [0, 4, 5], [2, 4, 5], [2, 3, 4, 5]] -/
#guard_msgs in
#eval (maybeUninit.solve 10 ⊥).map table

/-- info: some [[1], [1, 2], [1, 2, 3], [1, 3, 4], [1, 2, 3], [0, 1, 2, 3], [0, 1]] -/
#guard_msgs in
#eval (maybeInit.solve 10 ⊥).map table

/-- info: some [[1, 2], [2], [2], [0, 2], [0, 2], [0], []] -/
#guard_msgs in
#eval (liveness.solve 10 ⊥).map table
-- ANCHOR_END: eval

-- ANCHOR: drop_flag
/-- Drop elaboration's question at `drop(_2)` in `bb5`: is `_2` both maybe
initialized and maybe uninitialized there? -/
def needsDropFlag : Bool :=
  match maybeInit.solve 10 ⊥, maybeUninit.solve 10 ⊥ with
  | some init, some uninit => decide (2 ∈ init 5 ∧ 2 ∈ uninit 5)
  | _, _ => false

theorem drop_needs_flag : needsDropFlag = true := by decide
-- ANCHOR_END: drop_flag

-- ANCHOR: least
/-- All three analyses have monotone transfer functions... -/
theorem maybeUninit_mono : ∀ b, Monotone (maybeUninit.transfer b) := by
  intro b
  simp only [maybeUninit]
  split <;> exact genKill_mono _ _

/-- ...so the solver's answer is below every other solution: it is the most
precise one. Any `t` that satisfies the dataflow constraints says "maybe
uninitialized" at least wherever `r` does. -/
theorem maybeUninit_least {r t : Block → Finset Loc}
    (h : maybeUninit.solve 10 ⊥ = some r) (ht : maybeUninit.IsSolution t) : r ≤ t :=
  maybeUninit.solve_bot_least maybeUninit_mono ht h

/-- And the solver always terminates, without our having to run it. -/
theorem maybeUninit_terminates :
    (maybeUninit.solve (Fintype.card (Block → Finset Loc) + 1) ⊥).isSome :=
  maybeUninit.solve_terminates maybeUninit_mono
-- ANCHOR_END: least

end Ch29.MoveAnalysis
