import Book.Ch29.MoveAnalysis

/-!
# Chapter 29 · Regions as sets of points, on `branch_borrow`

The program point graph of `branch_borrow` (with the statements that do not
matter for borrowing left out), liveness of its references, and region
inference written as one more dataflow problem: the nodes are the region
variables, the edges are the outlives constraints, and the transfer function
is the identity. Solving it with liveness gives the non-lexical regions;
solving it with scopes gives the lexical ones. A general theorem from
`Dataflow.lean` says the first are always contained in the second.
-/

namespace Ch29.Regions

open Ch29 Ch29.MoveAnalysis

-- ANCHOR: points
/-- The program points of `branch_borrow`:

    0: _3 = &'L mut _2          let tail = &mut log;
    1: switchInt(_5)            if verbose
    2: _7 = &'R mut (*_3)       tail.push(1)       (then)
    3: Vec::push(move _7, 1)
    4: _9 = &'E mut _2          log.push(2)        (else)
    5: Vec::push(move _9, 2)
    6: _0 = move _2             log
    7: StorageDead(_3)          }
    8: return
-/
abbrev Point := Fin 9

def next : Point → List Point := fun p =>
  match p.val with
  | 0 => [1] | 1 => [2, 4] | 2 => [3] | 3 => [6] | 4 => [5] | 5 => [6]
  | 6 => [7] | 7 => [8] | _ => []

/-- The references: `tail` (`_3`), and the receivers `_7` and `_9`. -/
abbrev Ref := Fin 3
-- ANCHOR_END: points

-- ANCHOR: live
/-- Liveness of the references at each point (backward, live on entry):
point 0 defines `tail`, point 2 uses it and defines `_7`, and so on. -/
def liveRefs : Problem Point (Finset Ref) where
  inputs := next
  entry := fun _ => ∅
  transfer := fun p =>
    match p.val with
    | 0 => genKill ∅ {0}       -- def tail
    | 2 => genKill {0} {1}     -- use tail, def _7
    | 3 => genKill {1} ∅       -- use _7
    | 4 => genKill ∅ {2}       -- def _9
    | 5 => genKill {2} ∅       -- use _9
    | _ => genKill ∅ ∅

/-- The solver stores facts "flowing in" from the successors, which for a
backward problem is *live on exit*; live on entry applies the point's own
transfer function once more. -/
def liveIn (p : Point) : Finset Ref :=
  match liveRefs.solve 20 ⊥ with
  | some out => liveRefs.transfer p (out p)
  | none => ∅

/-- info: [[], [0], [0], [1], [], [2], [], [], []] -/
#guard_msgs in
#eval (List.finRange 9).map fun p => ((liveIn p).sort (· ≤ ·)).map Fin.val
-- ANCHOR_END: live

-- ANCHOR: regions
/-- The region variables: `'t`, `'7`, `'9` (in the types of `tail`, `_7` and
`_9`) and the loan regions `'L`, `'R`, `'E`. -/
abbrev Region := Fin 6

/-- The region in the type of each reference. -/
def typeRegion : Ref → Region := fun x => ⟨x.val, by omega⟩

/-- The outlives constraints `'a: 'b`, listed as the regions `'b` whose points
must flow into each `'a`:
`'L: 't` (point 0), `'R: '7` (point 2), `'t: 'R` (point 2, the reborrow of
`*tail`), `'E: '9` (point 4). -/
def outlives : Region → List Region := fun r =>
  match r.val with
  | 3 => [0] | 4 => [1] | 0 => [4] | 5 => [2] | _ => []

/-- Each loan region contains the point of its borrow. -/
def borrowPoint : Region → Finset Point := fun r =>
  match r.val with
  | 3 => {0} | 4 => {2} | 5 => {4} | _ => ∅

/-- Region inference as a dataflow problem: identity transfer functions,
the constraint graph as edges, and the starting points as boundary facts. -/
def inference (start : Region → Finset Point) : Problem Region (Finset Point) where
  inputs := outlives
  entry := start
  transfer := fun _ x => x

/-- NLL: a region contains the points where a reference whose type mentions
it is live. -/
def nllStart (r : Region) : Finset Point :=
  borrowPoint r ∪ Finset.univ.filter fun p => ∃ x ∈ liveIn p, typeRegion x = r

/-- Lexical: a region contains the points where such a reference is in scope
(from its `StorageLive` to its `StorageDead`). -/
def scope (x : Ref) : Finset Point :=
  match x.val with
  | 0 => {0, 1, 2, 3, 4, 5, 6, 7}    -- tail: to the end of the function
  | 1 => {2, 3}                      -- _7: the statement `tail.push(1)`
  | _ => {4, 5}                      -- _9: the statement `log.push(2)`

def lexicalStart (r : Region) : Finset Point :=
  borrowPoint r ∪ Finset.univ.filter fun p => ∃ x, p ∈ scope x ∧ typeRegion x = r

def regionsOf (start : Region → Finset Point) : Region → Finset Point :=
  match (inference start).solve 20 ⊥ with
  | some r => r
  | none => fun _ => Finset.univ

def regionTable (start : Region → Finset Point) : List (List ℕ) :=
  (List.finRange 6).map fun r => ((regionsOf start r).sort (· ≤ ·)).map Fin.val

/-- info: [[1, 2, 3], [3], [5], [0, 1, 2, 3], [2, 3], [4, 5]] -/
#guard_msgs in
#eval regionTable nllStart

/-- info: [[0, 1, 2, 3, 4, 5, 6, 7], [2, 3], [4, 5], [0, 1, 2, 3, 4, 5, 6, 7], [2, 3], [4, 5]] -/
#guard_msgs in
#eval regionTable lexicalStart
-- ANCHOR_END: regions

-- ANCHOR: verdict
/-- The loan `'L` of `log` (for `tail`) is not in scope at point 4, where the
`else` branch borrows `log` again, nor at point 6, where `log` is moved: NLL
accepts the program. -/
theorem nll_accepts : 4 ∉ regionsOf nllStart 3 ∧ 6 ∉ regionsOf nllStart 3 := by decide

/-- With lexical regions the loan reaches both points: E0499 at 4, E0505 at 6. -/
theorem lexical_rejects : 4 ∈ regionsOf lexicalStart 3 ∧ 6 ∈ regionsOf lexicalStart 3 := by
  decide

/-- The NLL region of the loan is not an interval of the source: it contains
the `then` branch (points 2 and 3) but not the `else` branch. -/
theorem nll_region : regionsOf nllStart 3 = {0, 1, 2, 3} := by decide
-- ANCHOR_END: verdict

-- ANCHOR: nll_le_lexical
/-- In general: if every live reference is in scope, every NLL region is
contained in the corresponding lexical region. The proof is `solve_mono_entry`:
the two problems differ only in their boundary facts. -/
theorem nll_le_lexical (hstart : nllStart ≤ lexicalStart) :
    regionsOf nllStart ≤ regionsOf lexicalStart := by
  unfold regionsOf
  split
  · rename_i rn hn
    split
    · rename_i rl hl
      exact Problem.solve_mono_entry (inference nllStart) (inference lexicalStart)
        rfl rfl hstart (fun _ => monotone_id) hn hl
    · intro r; exact Finset.subset_univ _
  · -- The NLL solver did not converge: impossible here, as `decide` shows.
    rename_i hn
    exact absurd hn (by decide)

/-- For `branch_borrow` the hypothesis holds: a live reference is in scope. -/
theorem live_in_scope : nllStart ≤ lexicalStart := by decide

theorem nll_regions_smaller : regionsOf nllStart ≤ regionsOf lexicalStart :=
  nll_le_lexical live_in_scope
-- ANCHOR_END: nll_le_lexical

end Ch29.Regions
