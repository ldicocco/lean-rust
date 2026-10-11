import Book.Ch15.Existential

/-!
# Chapter 15 · Representation independence

Two counter implementations with different state types (`Nat` and
`List Unit`) cannot be told apart by any client that uses only the
interface. We prove it for every client written in a small command language:
a *simulation* (a relation between the two state types that the operations
preserve and that relates states with equal observations) makes the two
implementations produce the same outputs for every program.
-/

namespace Ch15

-- ANCHOR: commands
/-- A client program: a list of commands. -/
inductive Cmd where
  | step
  | read

/-- Run a client program against an implementation, collecting the values it
reads. -/
def exec {σ : Type} (ops : CounterOps σ) : List Cmd → σ → List Nat
  | [], _ => []
  | .step :: cs, s => exec ops cs (ops.step s)
  | .read :: cs, s => ops.get s :: exec ops cs s
-- ANCHOR_END: commands

-- ANCHOR: simulation
/-- A simulation between two implementations: a relation between their
states that holds initially, is preserved by `step`, and relates only states
that `get` cannot tell apart. -/
structure Simulation {σ τ : Type} (A : CounterOps σ) (B : CounterOps τ) where
  R : σ → τ → Prop
  init : R A.init B.init
  step : ∀ s t, R s t → R (A.step s) (B.step t)
  get : ∀ s t, R s t → A.get s = B.get t
-- ANCHOR_END: simulation

-- ANCHOR: exec_sim
/-- Related states produce the same outputs, for every program. -/
theorem exec_sim {σ τ : Type} {A : CounterOps σ} {B : CounterOps τ}
    (sim : Simulation A B) :
    ∀ (cs : List Cmd) (s : σ) (t : τ), sim.R s t → exec A cs s = exec B cs t := by
  intro cs
  induction cs with
  | nil =>
    -- No commands: both runs output the empty list.
    intro s t _
    rfl
  | cons c cs ih =>
    intro s t hR
    cases c with
    | step =>
      -- Both sides take a step; the new states are related again.
      exact ih (A.step s) (B.step t) (sim.step s t hR)
    | read =>
      -- Both sides output a value (equal, by `sim.get`) and continue
      -- from the same, related states.
      show A.get s :: exec A cs s = B.get t :: exec B cs t
      rw [sim.get s t hR, ih s t hR]

/-- Hence the two implementations are indistinguishable from their initial
states. -/
theorem indistinguishable {σ τ : Type} {A : CounterOps σ} {B : CounterOps τ}
    (sim : Simulation A B) (cs : List Cmd) :
    exec A cs A.init = exec B cs B.init :=
  exec_sim sim cs A.init B.init sim.init
-- ANCHOR_END: exec_sim

-- ANCHOR: nat_unary
/-- The simulation between counting with `Nat` and counting with a list of
units: the list's length is the number. -/
def natUnary : Simulation natOps unaryOps where
  R n xs := xs.length = n
  init := rfl
  step n xs h := by
    -- h    : xs.length = n
    -- Goal : R (n + 1) (() :: xs), that is, (() :: xs).length = n + 1
    show xs.length + 1 = n + 1
    rw [h]
  get n xs h := by
    -- Goal : natOps.get n = unaryOps.get xs, that is, n = xs.length
    show n = xs.length
    rw [h]

/-- No client program can tell the two implementations apart. -/
theorem nat_unary (cs : List Cmd) :
    exec natOps cs natOps.init = exec unaryOps cs unaryOps.init :=
  indistinguishable natUnary cs
-- ANCHOR_END: nat_unary

-- ANCHOR: distinguishable
/-- Counting by ten, on the other hand, is told apart by a two-command
program. -/
example : exec natOps [.step, .read] natOps.init ≠
    exec tenOps [.step, .read] tenOps.init := by
  decide
-- ANCHOR_END: distinguishable

end Ch15
