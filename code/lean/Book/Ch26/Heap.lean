import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Notation

/-!
# Chapter 26 · A toy language with a heap

A straight-line imperative language with explicit allocation and
deallocation, in the style of C's `malloc` and `free`. Its small-step
semantics gets *stuck* when a program touches a cell that has been freed.
We show a program that goes wrong (a use after free through an alias), an
executable interpreter that reports why a program is stuck, and two
theorems that connect the interpreter to the step relation.

`Book/Ch26/Regions.lean` builds three static disciplines on top of this
language and proves that the region discipline rules out every stuck state.
-/

namespace Ch26

open Function (update)

/-- Variables are names. -/
abbrev Var := String

-- ANCHOR: syntax
/-- What a variable holds: a number, or the address of a heap cell. -/
inductive Val where
  | num (n : ℕ)
  | addr (l : ℕ)
  deriving DecidableEq, Repr

/-- The commands of the language. A program is a list of commands, run from
left to right. -/
inductive Cmd where
  | alloc (x : Var) (n : ℕ)  -- x := new n     a fresh cell holding n
  | copy (y x : Var)         -- y := x         y now holds what x holds
  | read (y x : Var)         -- y := *x        read the cell x points to
  | write (x : Var) (n : ℕ)  -- *x := n        write the cell x points to
  | free (x : Var)           -- free x         deallocate the cell
  deriving Repr

/-- A program is a list of commands. -/
abbrev Prog := List Cmd
-- ANCHOR_END: syntax

-- ANCHOR: state
/-- The machine state: the variables, the heap and the next fresh address.
A cell that was never allocated, or has been freed, holds `none`. -/
structure State where
  env : Var → Option Val
  heap : ℕ → Option ℕ
  next : ℕ

/-- The empty state: no variables, no cells. -/
def State.init : State where
  env := fun _ => none
  heap := fun _ => none
  next := 0
-- ANCHOR_END: state

-- ANCHOR: step
/-- One step of execution. A configuration is the program still to run
together with the current state. -/
inductive Step : Prog × State → Prog × State → Prop where
  | alloc {x : Var} {n : ℕ} {k : Prog} {s : State} :
      Step (.alloc x n :: k, s)
        (k, { env := update s.env x (some (.addr s.next))
              heap := update s.heap s.next (some n)
              next := s.next + 1 })
  | copy {y x : Var} {v : Val} {k : Prog} {s : State}
      (hx : s.env x = some v) :
      Step (.copy y x :: k, s) (k, { s with env := update s.env y (some v) })
  | read {y x : Var} {l n : ℕ} {k : Prog} {s : State}
      (hx : s.env x = some (.addr l)) (hl : s.heap l = some n) :
      Step (.read y x :: k, s) (k, { s with env := update s.env y (some (.num n)) })
  | write {x : Var} {n l m : ℕ} {k : Prog} {s : State}
      (hx : s.env x = some (.addr l)) (hl : s.heap l = some m) :
      Step (.write x n :: k, s) (k, { s with heap := update s.heap l (some n) })
  | free {x : Var} {l m : ℕ} {k : Prog} {s : State}
      (hx : s.env x = some (.addr l)) (hl : s.heap l = some m) :
      Step (.free x :: k, s) (k, { s with heap := update s.heap l none })
-- ANCHOR_END: step

-- ANCHOR: stuck
/-- Zero or more steps: Mathlib's reflexive-transitive closure of `Step`. -/
abbrev Steps := Relation.ReflTransGen Step

/-- A configuration is stuck when there is still a command to run but no
rule of `Step` applies to it. -/
def Stuck (c : Prog × State) : Prop := c.1 ≠ [] ∧ ¬ ∃ c', Step c c'

/-- A program goes wrong if, started in the empty state, it can reach a stuck
configuration. -/
def GoesWrong (p : Prog) : Prop := ∃ c, Steps (p, State.init) c ∧ Stuck c
-- ANCHOR_END: stuck

-- ANCHOR: programs
/-- Two pointers to one cell, both used to read it, then the cell is freed.
A perfectly safe program. -/
def share : Prog :=
  [.alloc "x" 42, .copy "y" "x", .read "a" "x", .read "b" "y", .free "x"]

/-- The same aliasing, but the cell is freed *before* the alias is read. -/
def uaf : Prog :=
  [.alloc "x" 42, .copy "y" "x", .free "x", .read "z" "y"]

/-- Freeing the same cell twice, once through each pointer. -/
def doubleFree : Prog :=
  [.alloc "x" 1, .copy "y" "x", .free "x", .free "y"]
-- ANCHOR_END: programs

/-! ## An interpreter that explains what went wrong -/

-- ANCHOR: fault
/-- Why a command cannot run. -/
inductive Fault where
  | unassigned (x : Var)            -- `x` has no value yet
  | notAnAddress (x : Var)          -- `x` holds a number, not an address
  | dangling (x : Var) (l : ℕ)    -- `x` points to cell `l`, which is not allocated
  deriving Repr

/-- Follow the pointer in `x`: its address and the current contents of the
cell, or the reason why there is no such cell. -/
def deref (s : State) (x : Var) : Except Fault (ℕ × ℕ) :=
  match s.env x with
  | none => .error (.unassigned x)
  | some (.num _) => .error (.notAnAddress x)
  | some (.addr l) =>
    match s.heap l with
    | none => .error (.dangling x l)
    | some n => .ok (l, n)
-- ANCHOR_END: fault

-- ANCHOR: exec
/-- Run one command. -/
def exec (s : State) : Cmd → Except Fault State
  | .alloc x n => .ok { env := update s.env x (some (.addr s.next))
                        heap := update s.heap s.next (some n)
                        next := s.next + 1 }
  | .copy y x =>
    match s.env x with
    | none => .error (.unassigned x)
    | some v => .ok { s with env := update s.env y (some v) }
  | .read y x =>
    match deref s x with
    | .error e => .error e
    | .ok (_, n) => .ok { s with env := update s.env y (some (.num n)) }
  | .write x n =>
    match deref s x with
    | .error e => .error e
    | .ok (l, _) => .ok { s with heap := update s.heap l (some n) }
  | .free x =>
    match deref s x with
    | .error e => .error e
    | .ok (l, _) => .ok { s with heap := update s.heap l none }

/-- Run a whole program, stopping at the first fault. -/
def run : Prog → State → Except Fault State
  | [], s => .ok s
  | c :: k, s =>
    match exec s c with
    | .error e => .error e
    | .ok s' => run k s'
-- ANCHOR_END: exec

/-- The values of some variables, to look at the result of a run. -/
def observe (xs : List Var) (r : Except Fault State) :
    Except Fault (List (Var × Option Val)) :=
  r.map fun s => xs.map fun x => (x, s.env x)

-- ANCHOR: runs
/-- info: Except.ok [("a", some (Ch26.Val.num 42)), ("b", some (Ch26.Val.num 42))] -/
#guard_msgs in
#eval observe ["a", "b"] (run share State.init)

/-- info: Except.error (Ch26.Fault.dangling "y" 0) -/
#guard_msgs in
#eval observe ["z"] (run uaf State.init)

/-- info: Except.error (Ch26.Fault.dangling "y" 0) -/
#guard_msgs in
#eval observe [] (run doubleFree State.init)
-- ANCHOR_END: runs

/-! ## The interpreter agrees with the step relation -/

-- ANCHOR: deref_ok
/-- `deref` succeeds exactly when `x` holds an address of an allocated cell. -/
theorem deref_ok {s : State} {x : Var} {l n : ℕ} :
    deref s x = .ok (l, n) ↔ s.env x = some (.addr l) ∧ s.heap l = some n := by
  unfold deref
  -- What does `x` hold? Nothing, a number, or an address `l'`.
  rcases hx : s.env x with _ | _ | l'
  · simp
  · simp
  · -- An address `l'`: what is in the cell?
    rcases hl : s.heap l' with _ | m
    · -- A freed cell: `deref` fails, and the right side is false too.
      simp only [hl, reduceCtorEq, Option.some.injEq, Val.addr.injEq, false_iff,
        not_and]
      rintro rfl
      simp [hl]
    · -- An allocated cell holding `m`: both sides say `l' = l` and `m = n`.
      simp only [hl, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq, Val.addr.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, hl⟩
      · rintro ⟨rfl, h⟩
        rw [hl] at h
        exact ⟨rfl, Option.some.inj h⟩
-- ANCHOR_END: deref_ok

/-- If `deref` fails, `x` does not point to an allocated cell. -/
theorem deref_error {s : State} {x : Var} {e : Fault} (h : deref s x = .error e)
    {l n : ℕ} (hx : s.env x = some (.addr l)) (hl : s.heap l = some n) :
    False := by
  have : deref s x = .ok (l, n) := deref_ok.mpr ⟨hx, hl⟩
  rw [h] at this
  cases this

-- ANCHOR: exec_ok
/-- A command that `exec` runs successfully takes one `Step`. -/
theorem exec_ok {s s' : State} {c : Cmd} (k : Prog) (h : exec s c = .ok s') :
    Step (c :: k, s) (k, s') := by
  cases c with
  | alloc x n =>
    -- `exec` returned the new state; the rule `Step.alloc` builds the same one.
    simp only [exec, Except.ok.injEq] at h
    subst h
    exact Step.alloc
  | copy y x =>
    simp only [exec] at h
    split at h
    · cases h
    · rename_i v hx
      simp only [Except.ok.injEq] at h
      subst h
      exact Step.copy hx
  | read y x =>
    simp only [exec] at h
    split at h
    · cases h
    · rename_i l n hd
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨hx, hl⟩ := deref_ok.mp hd
      exact Step.read hx hl
  | write x n =>
    simp only [exec] at h
    split at h
    · cases h
    · rename_i l m hd
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨hx, hl⟩ := deref_ok.mp hd
      exact Step.write hx hl
  | free x =>
    simp only [exec] at h
    split at h
    · cases h
    · rename_i l m hd
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨hx, hl⟩ := deref_ok.mp hd
      exact Step.free hx hl
-- ANCHOR_END: exec_ok

-- ANCHOR: exec_error
/-- A command on which `exec` reports a fault is stuck: no rule applies. -/
theorem exec_error {s : State} {c : Cmd} {e : Fault} (k : Prog)
    (h : exec s c = .error e) : ¬ ∃ c', Step (c :: k, s) c' := by
  rintro ⟨c', hstep⟩
  -- Which rule could have fired? Each one contradicts the fault.
  cases hstep with
  | alloc => simp [exec] at h
  | copy hx => simp [exec, hx] at h
  | read hx hl =>
    simp only [exec] at h
    split at h
    · rename_i e' hd
      exact deref_error hd hx hl
    · cases h
  | write hx hl =>
    simp only [exec] at h
    split at h
    · rename_i e' hd
      exact deref_error hd hx hl
    · cases h
  | free hx hl =>
    simp only [exec] at h
    split at h
    · rename_i e' hd
      exact deref_error hd hx hl
    · cases h
-- ANCHOR_END: exec_error

-- ANCHOR: run_correct
/-- A successful run is a sequence of steps that ends with nothing left to do. -/
theorem run_ok {p : Prog} {s s' : State} (h : run p s = .ok s') :
    Steps (p, s) ([], s') := by
  induction p generalizing s with
  | nil =>
    simp only [run, Except.ok.injEq] at h
    subst h
    exact Relation.ReflTransGen.refl
  | cons c k ih =>
    simp only [run] at h
    split at h
    · cases h
    · rename_i s₁ hc
      exact Relation.ReflTransGen.head (exec_ok k hc) (ih h)

/-- A run that reports a fault has reached a stuck configuration. -/
theorem run_error {p : Prog} {s : State} {e : Fault} (h : run p s = .error e) :
    ∃ c, Steps (p, s) c ∧ Stuck c := by
  induction p generalizing s with
  | nil => simp [run] at h
  | cons c k ih =>
    simp only [run] at h
    split at h
    · -- The first command itself is stuck.
      rename_i e' hc
      exact ⟨(c :: k, s), Relation.ReflTransGen.refl,
        List.cons_ne_nil c k, exec_error k hc⟩
    · -- The first command runs; the fault comes later.
      rename_i s₁ hc
      obtain ⟨c', hsteps, hstuck⟩ := ih h
      exact ⟨c', Relation.ReflTransGen.head (exec_ok k hc) hsteps, hstuck⟩
-- ANCHOR_END: run_correct

-- ANCHOR: goes_wrong
/-- The use after free goes wrong. -/
theorem uaf_goes_wrong : GoesWrong uaf := run_error (e := .dangling "y" 0) rfl

/-- So does the double free. -/
theorem doubleFree_goes_wrong : GoesWrong doubleFree :=
  run_error (e := .dangling "y" 0) rfl

/-- The safe program runs to completion. -/
theorem share_finishes : ∃ s, Steps (share, State.init) ([], s) :=
  ⟨_, run_ok rfl⟩
-- ANCHOR_END: goes_wrong

end Ch26
