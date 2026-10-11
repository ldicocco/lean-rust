import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Chapter 29 · Dataflow analysis as a monotone fixpoint

A dataflow problem on a graph: facts in a join-semilattice with a least
element, a transfer function per node, and the equations "the facts at a node
are the join of what flows in". The solver iterates from `⊥` with fuel. We
prove that a converged result is a fixpoint, that a fixpoint satisfies every
dataflow constraint, that the result is the *least* solution (for monotone
transfer functions), that it grows with the boundary facts, and that enough
fuel always suffices on a finite lattice.
-/

namespace Ch29

-- ANCHOR: problem
/-- A dataflow problem with nodes `ι` and facts `α`. For a forward analysis
the `inputs` of a node are its predecessors in the control-flow graph; for a
backward analysis they are its successors. -/
structure Problem (ι α : Type) [SemilatticeSup α] [OrderBot α] where
  /-- The nodes whose facts flow into each node. -/
  inputs : ι → List ι
  /-- Facts that hold at a node whatever flows in (the boundary condition). -/
  entry : ι → α
  /-- The transfer function of each node. -/
  transfer : ι → α → α
-- ANCHOR_END: problem

variable {ι α : Type} [SemilatticeSup α] [OrderBot α]

-- ANCHOR: join_all
/-- The join of a list of facts: `x₁ ⊔ x₂ ⊔ ... ⊔ ⊥`. -/
def joinAll : List α → α
  | [] => ⊥
  | x :: xs => x ⊔ joinAll xs

/-- Every element of the list is below the join... -/
theorem le_joinAll {x : α} : ∀ {xs : List α}, x ∈ xs → x ≤ joinAll xs
  | _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_sup_left
    · exact le_trans (le_joinAll h) le_sup_right

/-- ...and the join is below every upper bound of the list. -/
theorem joinAll_le {y : α} : ∀ {xs : List α}, (∀ x ∈ xs, x ≤ y) → joinAll xs ≤ y
  | [], _ => bot_le
  | x :: _, h =>
    sup_le (h x List.mem_cons_self)
      (joinAll_le fun z hz => h z (List.mem_cons_of_mem x hz))
-- ANCHOR_END: join_all

namespace Problem

-- ANCHOR: step
/-- One round of the dataflow equations, at every node at once. -/
def step (P : Problem ι α) (s : ι → α) : ι → α :=
  fun v => P.entry v ⊔ joinAll ((P.inputs v).map fun u => P.transfer u (s u))

/-- A solution satisfies every constraint: the boundary facts, and every edge
`u → v`, whose transferred facts must be included in the facts at `v`. -/
def IsSolution (P : Problem ι α) (s : ι → α) : Prop :=
  ∀ v, P.entry v ≤ s v ∧ ∀ u ∈ P.inputs v, P.transfer u (s u) ≤ s v
-- ANCHOR_END: step

-- ANCHOR: solve
/-- Iterate `step` until nothing changes, for at most `fuel` rounds. -/
def solve [DecidableEq (ι → α)] (P : Problem ι α) : ℕ → (ι → α) → Option (ι → α)
  | 0, _ => none
  | fuel + 1, s => if P.step s = s then some s else P.solve fuel (P.step s)
-- ANCHOR_END: solve

-- ANCHOR: solve_fixpoint
/-- If the solver returns `r`, then `r` is a fixpoint of `step`. -/
theorem solve_fixpoint [DecidableEq (ι → α)] (P : Problem ι α) :
    ∀ (fuel : ℕ) (s r : ι → α), P.solve fuel s = some r → P.step r = r := by
  intro fuel
  induction fuel with
  | zero =>
    -- With no fuel the solver returns `none`, so there is nothing to prove.
    intro s r h
    simp [solve] at h
  | succ fuel ih =>
    intro s r h
    -- Unfold one round: either `step s = s` and `r = s`, or we recurse.
    unfold solve at h
    split at h
    · -- Converged: `h : some s = some r` and the test said `step s = s`.
      rename_i hfix
      cases h
      exact hfix
    · -- Not yet: the recursive call returned `r`; the induction hypothesis
      -- (for one unit of fuel less, starting from `step s`) finishes.
      exact ih (P.step s) r h
-- ANCHOR_END: solve_fixpoint


-- ANCHOR: solution_iff
/-- Being a solution is the same as being a *post-fixpoint*: `step s ≤ s`. -/
theorem isSolution_iff (P : Problem ι α) (s : ι → α) :
    P.IsSolution s ↔ P.step s ≤ s := by
  constructor
  · intro hs v
    obtain ⟨hentry, hedges⟩ := hs v
    apply sup_le hentry
    apply joinAll_le
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact hedges u hu
  · intro hs v
    constructor
    · exact le_trans le_sup_left (hs v)
    · intro u hu
      have hmem : P.transfer u (s u) ∈ (P.inputs v).map fun w => P.transfer w (s w) :=
        List.mem_map.mpr ⟨u, hu, rfl⟩
      exact le_trans (le_joinAll hmem) (le_trans le_sup_right (hs v))
-- ANCHOR_END: solution_iff

-- ANCHOR: fixpoint_solution
/-- A fixpoint of `step` satisfies all the dataflow constraints. -/
theorem fixpoint_isSolution (P : Problem ι α) {r : ι → α} (h : P.step r = r) :
    P.IsSolution r :=
  (P.isSolution_iff r).mpr (le_of_eq h)
-- ANCHOR_END: fixpoint_solution

/-- Joining pointwise-larger facts gives a larger join. -/
theorem joinAll_map_mono {f g : ι → α} (h : ∀ u, f u ≤ g u) :
    ∀ l : List ι, joinAll (l.map f) ≤ joinAll (l.map g)
  | [] => le_refl _
  | u :: l => sup_le_sup (h u) (joinAll_map_mono h l)

-- ANCHOR: step_mono
/-- With monotone transfer functions, `step` is monotone. -/
theorem step_mono (P : Problem ι α) (hmono : ∀ u, Monotone (P.transfer u)) :
    Monotone P.step := by
  intro s t hst v
  apply sup_le_sup (le_refl _)
  exact joinAll_map_mono (fun u => hmono u (hst u)) _
-- ANCHOR_END: step_mono

-- ANCHOR: solve_least
/-- The solver computes the *least* solution: starting below any solution
`t`, every round stays below `t`, so the result does too. -/
theorem solve_least [DecidableEq (ι → α)] (P : Problem ι α)
    (hmono : ∀ u, Monotone (P.transfer u)) {t : ι → α} (ht : P.IsSolution t) :
    ∀ (fuel : ℕ) (s r : ι → α), s ≤ t → P.solve fuel s = some r → r ≤ t := by
  have hpost : P.step t ≤ t := (P.isSolution_iff t).mp ht
  intro fuel
  induction fuel with
  | zero => intro s r _ h; simp [solve] at h
  | succ fuel ih =>
    intro s r hs h
    unfold solve at h
    split at h
    · cases h; exact hs
    · -- `step s ≤ step t ≤ t`: one more round keeps us below `t`.
      exact ih (P.step s) r (le_trans (P.step_mono hmono hs) hpost) h

/-- In particular, starting from `⊥`. -/
theorem solve_bot_least [DecidableEq (ι → α)] (P : Problem ι α)
    (hmono : ∀ u, Monotone (P.transfer u)) {t r : ι → α} (ht : P.IsSolution t)
    {fuel : ℕ} (h : P.solve fuel ⊥ = some r) : r ≤ t :=
  P.solve_least hmono ht fuel ⊥ r bot_le h
-- ANCHOR_END: solve_least

-- ANCHOR: solve_mono_entry
/-- More boundary facts give a larger least solution. (Chapter 29 uses this to
compare lexical and non-lexical regions.) -/
theorem solve_mono_entry [DecidableEq (ι → α)] (P Q : Problem ι α)
    (hinputs : P.inputs = Q.inputs) (htransfer : P.transfer = Q.transfer)
    (hentry : P.entry ≤ Q.entry) (hmono : ∀ u, Monotone (P.transfer u))
    {fp fq : ℕ} {rp rq : ι → α}
    (hp : P.solve fp ⊥ = some rp) (hq : Q.solve fq ⊥ = some rq) : rp ≤ rq := by
  -- `rq` solves `Q`, hence also `P`, whose constraints are weaker.
  have hq_sol : Q.IsSolution rq := Q.fixpoint_isSolution (Q.solve_fixpoint fq ⊥ rq hq)
  have hp_sol : P.IsSolution rq := by
    intro v
    obtain ⟨he, hedges⟩ := hq_sol v
    refine ⟨le_trans (hentry v) he, ?_⟩
    rw [hinputs, htransfer]
    exact hedges
  exact P.solve_bot_least hmono hp_sol hp
-- ANCHOR_END: solve_mono_entry

/-! ### Enough fuel always suffices on a finite lattice -/

-- ANCHOR: solve_isSome
/-- If the `k`-th iterate is already a fixpoint and the fuel exceeds `k`, the
solver returns something. -/
theorem solve_isSome [DecidableEq (ι → α)] (P : Problem ι α) :
    ∀ (fuel k : ℕ) (s : ι → α), P.step^[k + 1] s = P.step^[k] s → k < fuel →
      (P.solve fuel s).isSome := by
  intro fuel
  induction fuel with
  | zero => intro k s _ hk; omega
  | succ fuel ih =>
    intro k s hfix hk
    unfold solve
    split
    · rfl
    · rename_i hne
      cases k with
      | zero => exact absurd hfix hne
      | succ k =>
        -- Iterating `k + 1` times from `s` is iterating `k` times from `step s`.
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hfix
        exact ih k (P.step s) hfix (by omega)

/-- On a finite lattice, monotone transfer functions and `|ι → α| + 1` rounds
of fuel are enough. (The bound is crude: the real one is the number of nodes
times the height of the lattice, plus one.) -/
theorem solve_terminates [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (P : Problem ι α) (hmono : ∀ u, Monotone (P.transfer u)) :
    (P.solve (Fintype.card (ι → α) + 1) ⊥).isSome := by
  set N := Fintype.card (ι → α)
  let it : ℕ → ι → α := fun k => P.step^[k] ⊥
  -- The iterates form an increasing chain ⊥ ≤ step ⊥ ≤ step (step ⊥) ≤ ...
  have hchain : Monotone it := by
    apply monotone_nat_of_le_succ
    intro k
    induction k with
    | zero => exact bot_le
    | succ k ihk =>
      simp only [it, Function.iterate_succ_apply'] at ihk ⊢
      exact P.step_mono hmono ihk
  -- Pigeonhole: N + 1 iterates in a set of size N, so two of them are equal.
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) => it k) (by simp [N])
  -- Between two equal iterates the chain is flat, so the smaller index is a fixpoint.
  have flat : ∀ a b : ℕ, a < b → it a = it b → it (a + 1) = it a := by
    intro a b hab hab'
    apply le_antisymm
    · rw [hab']; exact hchain (by omega)
    · exact hchain (by omega)
  have key : ∃ k, k < N + 1 ∧ it (k + 1) = it k := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact ⟨i, i.isLt, flat i j h heq⟩
    · exact ⟨j, j.isLt, flat j i h heq.symm⟩
  obtain ⟨k, hk, hfix⟩ := key
  exact P.solve_isSome (N + 1) k ⊥ hfix hk
-- ANCHOR_END: solve_isSome

end Problem

end Ch29
