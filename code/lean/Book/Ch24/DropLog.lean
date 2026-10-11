/-!
# Chapter 24 · A resource language with a drop log

A tiny straight-line language whose variables own resources. Running a program
produces a *log* of events (`acquire r`, `release r`), the formal counterpart of
the lines that `ch24_drop_order.rs` prints. At the end of the scope, every
variable that still owns a resource is dropped, newest first, as Rust does.

We prove:

* `run_at_most_once`: no resource is ever released twice, for every program;
* `run_exactly_once`: in a program without `forget`, every acquired resource
  is released exactly once;
* `forget_breaks_exactly_once`: with `forget`, "exactly once" fails;
* `check_sound`: programs accepted by a static move checker never fail with a
  use-after-move at run time.
-/

namespace Ch24.DropLog

-- ANCHOR: syntax
/-- Variables are names; resources are numbered in order of acquisition. -/
abbrev Var := String
abbrev Res := Nat

/-- The statements of the language. -/
inductive Stmt where
  | new (x : Var)          -- let x = Resource::new();
  | move (x y : Var)       -- let y = x;
  | drop (x : Var)         -- drop(x);
  | forget (x : Var)       -- mem::forget(x);
  | read (x : Var)         -- x.read();  (uses x without consuming it)
  deriving Repr, DecidableEq

/-- What the log records. -/
inductive Event where
  | acquire (r : Res)
  | release (r : Res)
  deriving DecidableEq
-- ANCHOR_END: syntax

/-- Print events briefly: `acquire r0`, `release r0`. -/
instance : Repr Event where
  reprPrec
    | .acquire r, _ => s!"acquire r{r}"
    | .release r, _ => s!"release r{r}"

-- ANCHOR: state
/-- A slot is a declared variable with its *drop flag*: `some r` if the
variable owns resource `r`, `none` if its value has been moved out. -/
abbrev Slot := Var × Option Res

structure State where
  slots : List Slot      -- every declared variable, newest first
  next  : Res            -- the next fresh resource
  log   : List Event     -- what has happened, oldest first

def State.init : State := ⟨[], 0, []⟩
-- ANCHOR_END: state

-- ANCHOR: take
/-- Take the value out of the newest slot named `x`, clearing its drop flag.
This is the run-time version of "use of moved value". -/
def take (x : Var) : List Slot → Except String (Res × List Slot)
  | [] => .error s!"cannot find value `{x}` in this scope"
  | (y, o) :: rest =>
    if y = x then
      match o with
      | some r => .ok (r, (y, none) :: rest)
      | none => .error s!"use of moved value: `{x}`"
    else
      match take x rest with
      | .ok (r, rest') => .ok (r, (y, o) :: rest')
      | .error e => .error e
-- ANCHOR_END: take

-- ANCHOR: step
/-- One statement. Only `new` and `drop` write to the log. -/
def step (s : State) : Stmt → Except String State
  | .new x =>
    .ok ⟨(x, some s.next) :: s.slots, s.next + 1, s.log ++ [.acquire s.next]⟩
  | .move x y =>
    match take x s.slots with
    | .ok (r, slots) => .ok ⟨(y, some r) :: slots, s.next, s.log⟩
    | .error e => .error e
  | .drop x =>
    match take x s.slots with
    | .ok (r, slots) => .ok ⟨slots, s.next, s.log ++ [.release r]⟩
    | .error e => .error e
  | .forget x =>
    match take x s.slots with
    | .ok (_, slots) => .ok ⟨slots, s.next, s.log⟩
    | .error e => .error e
  | .read x =>
    match take x s.slots with
    | .ok _ => .ok s
    | .error e => .error e
-- ANCHOR_END: step

-- ANCHOR: run
/-- The end of the scope: release every resource that is still owned, newest
slot first (reverse declaration order). Moved-out slots are skipped: that is
what the drop flag is for. -/
def dropAll : List Slot → List Event → List Event
  | [], log => log
  | (_, some r) :: rest, log => dropAll rest (log ++ [.release r])
  | (_, none) :: rest, log => dropAll rest log

def exec (s : State) : List Stmt → Except String State
  | [] => .ok s
  | st :: prog =>
    match step s st with
    | .ok s' => exec s' prog
    | .error e => .error e

/-- Run a program in a fresh scope and return the complete log. -/
def run (prog : List Stmt) : Except String (List Event) :=
  match exec State.init prog with
  | .ok s => .ok (dropAll s.slots s.log)
  | .error e => .error e
-- ANCHOR_END: run

-- ANCHOR: examples
/-- The `moves` function of `ch24_drop_order.rs`, with `send = true`:
`x` is moved into `consume`, which drops it; `y` is dropped at the end. -/
def movesProgram : List Stmt :=
  [.new "x", .new "y", .move "x" "n", .drop "n"]

/-- info: Except.ok [acquire r0, acquire r1, release r0, release r1] -/
#guard_msgs in
#eval run movesProgram

/-- Without the move, both are dropped at the end, newest first. -/
def localsProgram : List Stmt := [.new "a", .new "b", .new "c"]

/--
info: Except.ok [acquire r0, acquire r1, acquire r2, release r2, release r1, release r0]
-/
#guard_msgs in
#eval run localsProgram

/-- info: Except.error "use of moved value: `conn`" -/
#guard_msgs in
#eval run [.new "conn", .drop "conn", .read "conn"]

/-- info: Except.ok [acquire r0] -/
#guard_msgs in
#eval run [.new "conn", .forget "conn"]
-- ANCHOR_END: examples

/-! ## Counting -/

-- ANCHOR: counting
/-- How many slots own resource `r` right now. -/
def held : List Slot → Res → Nat
  | [], _ => 0
  | (_, o) :: rest, r => (if o = some r then 1 else 0) + held rest r

/-- How many times the log says `r` was acquired, and released. -/
def acquired (log : List Event) (r : Res) : Nat := log.count (.acquire r)
def released (log : List Event) (r : Res) : Nat := log.count (.release r)
-- ANCHOR_END: counting

/-! How appending one event changes the counts. -/

@[simp] theorem held_cons (x : Var) (o : Option Res) (rest : List Slot) (r : Res) :
    held ((x, o) :: rest) r = (if o = some r then 1 else 0) + held rest r := rfl

@[simp] theorem acquired_acquire (log : List Event) (r' r : Res) :
    acquired (log ++ [.acquire r']) r = acquired log r + (if r' = r then 1 else 0) := by
  simp [acquired, List.count_append, List.count_singleton]

@[simp] theorem acquired_release (log : List Event) (r' r : Res) :
    acquired (log ++ [.release r']) r = acquired log r := by
  simp [acquired, List.count_append]

@[simp] theorem released_acquire (log : List Event) (r' r : Res) :
    released (log ++ [.acquire r']) r = released log r := by
  simp [released, List.count_append]

@[simp] theorem released_release (log : List Event) (r' r : Res) :
    released (log ++ [.release r']) r = released log r + (if r' = r then 1 else 0) := by
  simp [released, List.count_append, List.count_singleton]

-- ANCHOR: take_held
/-- Taking a value out of the slots removes exactly one owner of `r` (if the
taken resource is `r`) and leaves every other count unchanged. -/
theorem take_held {x : Var} {slots slots' : List Slot} {r : Res}
    (h : take x slots = .ok (r, slots')) (q : Res) :
    held slots q = held slots' q + (if r = q then 1 else 0) := by
  induction slots generalizing slots' with
  | nil =>
    -- `take x []` is an error, so `h` is impossible.
    simp [take] at h
  | cons slot rest ih =>
    obtain ⟨y, o⟩ := slot
    by_cases hyx : y = x
    · -- The newest slot is `x`: it must own a resource, which is taken.
      cases o with
      | none => simp [take, hyx] at h
      | some r₀ =>
        simp only [take, hyx, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [held_cons, Option.some.injEq, reduceCtorEq, ↓reduceIte]
        omega
    · -- Another variable: the value is taken from the rest of the list.
      simp only [take, hyx, ↓reduceIte] at h
      split at h
      · rename_i r₁ rest' htake
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih htake
        simp only [held_cons]
        omega
      · simp at h
-- ANCHOR_END: take_held

/-- The end of the scope adds one release per resource still owned. -/
theorem released_dropAll (slots : List Slot) (log : List Event) (r : Res) :
    released (dropAll slots log) r = released log r + held slots r := by
  induction slots generalizing log with
  | nil => simp [dropAll, held]
  | cons slot rest ih =>
    obtain ⟨y, o⟩ := slot
    cases o with
    | none => simp [dropAll, ih]
    | some r₀ =>
      rw [dropAll, ih, released_release, held_cons]
      simp only [Option.some.injEq]
      omega

/-- The end of the scope acquires nothing. -/
theorem acquired_dropAll (slots : List Slot) (log : List Event) (r : Res) :
    acquired (dropAll slots log) r = acquired log r := by
  induction slots generalizing log with
  | nil => simp [dropAll]
  | cons slot rest ih =>
    obtain ⟨y, o⟩ := slot
    cases o with
    | none => simp [dropAll, ih]
    | some r₀ => rw [dropAll, ih, acquired_release]

/-! ## No resource is released twice -/

-- ANCHOR: inv
/-- The invariant of every reachable state. -/
structure Inv (s : State) : Prop where
  /-- Owners plus releases never exceed acquisitions. -/
  conserve : ∀ r, held s.slots r + released s.log r ≤ acquired s.log r
  /-- Each resource is acquired at most once. -/
  once : ∀ r, acquired s.log r ≤ 1
  /-- Resources from `next` on have not been acquired yet. -/
  fresh : ∀ r, s.next ≤ r → acquired s.log r = 0
-- ANCHOR_END: inv

theorem inv_init : Inv State.init :=
  ⟨by simp [State.init, held, released, acquired],
   by simp [State.init, acquired],
   by simp [State.init, acquired]⟩

-- ANCHOR: step_inv
theorem step_inv {s s' : State} {st : Stmt} (hs : Inv s)
    (h : step s st = .ok s') : Inv s' := by
  obtain ⟨hcons, honce, hfresh⟩ := hs
  cases st with
  | new x =>
    -- A fresh resource `s.next` gets one owner and one acquisition.
    simp only [step, Except.ok.injEq] at h
    subst h
    -- Before the step, `s.next` had no owner and no release.
    have h0 := hfresh s.next (Nat.le_refl _)
    have hc0 := hcons s.next
    refine ⟨fun r => ?_, fun r => ?_, fun r hr => ?_⟩
    · have := hcons r
      by_cases hr : s.next = r
      · subst hr; simp; omega
      · simp [hr]; omega
    · have := honce r
      by_cases hr : s.next = r
      · subst hr; simp; omega
      · simp [hr]; omega
    · -- `r` is at least `s.next + 1`: it is neither `s.next` nor acquired.
      have hlt : s.next < r := hr
      simp [Nat.ne_of_lt hlt, hfresh r (Nat.le_of_lt hlt)]
  | move x y =>
    -- The resource changes owner: every count is unchanged.
    simp only [step] at h
    split at h
    · rename_i r slots htake
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨fun q => ?_, honce, hfresh⟩
      have h1 := take_held htake q
      have h2 := hcons q
      simp only [held_cons, Option.some.injEq]
      omega
    · simp at h
  | drop x =>
    -- One owner fewer, one release more.
    simp only [step] at h
    split at h
    · rename_i r slots htake
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨fun q => ?_, fun q => ?_, fun q hq => ?_⟩
      · have h1 := take_held htake q
        have h2 := hcons q
        simp only [released_release, acquired_release]
        omega
      · simpa using honce q
      · simpa using hfresh q hq
    · simp at h
  | forget x =>
    -- One owner fewer, and nothing in the log.
    simp only [step] at h
    split at h
    · rename_i r slots htake
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨fun q => ?_, honce, hfresh⟩
      have h1 := take_held htake q
      have h2 := hcons q
      dsimp only
      omega
    · simp at h
  | read x =>
    simp only [step] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact ⟨hcons, honce, hfresh⟩
    · simp at h
-- ANCHOR_END: step_inv

theorem exec_inv {s s' : State} {prog : List Stmt} (hs : Inv s)
    (h : exec s prog = .ok s') : Inv s' := by
  induction prog generalizing s with
  | nil =>
    simp only [exec, Except.ok.injEq] at h
    exact h ▸ hs
  | cons st prog ih =>
    simp only [exec] at h
    split at h
    · rename_i s₁ hstep
      exact ih (step_inv hs hstep) h
    · simp at h

-- ANCHOR: at_most_once
/-- **At most once.** For every program, whatever it does, no resource
appears twice as released in the final log. -/
theorem run_at_most_once {prog : List Stmt} {log : List Event}
    (h : run prog = .ok log) (r : Res) : log.count (.release r) ≤ 1 := by
  simp only [run] at h
  split at h
  · rename_i s hexec
    simp only [Except.ok.injEq] at h
    subst h
    have hs := exec_inv inv_init hexec
    have h1 := released_dropAll s.slots s.log r
    have h2 := hs.conserve r
    have h3 := hs.once r
    simp only [released] at h1 h2
    omega
  · simp at h
-- ANCHOR_END: at_most_once

/-! ## Exactly once, without `forget` -/

-- ANCHOR: balanced
/-- A state is *balanced* when owners plus releases equal acquisitions:
nothing has been lost. -/
def Balanced (s : State) : Prop :=
  ∀ r, held s.slots r + released s.log r = acquired s.log r

def NoForget : Stmt → Prop
  | .forget _ => False
  | _ => True
-- ANCHOR_END: balanced

theorem step_balanced {s s' : State} {st : Stmt}
    (hb : Balanced s) (hf : NoForget st) (h : step s st = .ok s') :
    Balanced s' := by
  cases st with
  | new x =>
    simp only [step, Except.ok.injEq] at h
    subst h
    intro r
    have := hb r
    by_cases hr : s.next = r
    · subst hr; simp; omega
    · simp [hr]; omega
  | move x y =>
    simp only [step] at h
    split at h
    · rename_i r slots htake
      simp only [Except.ok.injEq] at h
      subst h
      intro q
      have h1 := take_held htake q
      have h2 := hb q
      simp only [held_cons, Option.some.injEq]
      omega
    · simp at h
  | drop x =>
    simp only [step] at h
    split at h
    · rename_i r slots htake
      simp only [Except.ok.injEq] at h
      subst h
      intro q
      have h1 := take_held htake q
      have h2 := hb q
      simp only [released_release, acquired_release]
      omega
    · simp at h
  | forget x => exact absurd hf id
  | read x =>
    simp only [step] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact hb
    · simp at h

theorem exec_balanced {s s' : State} {prog : List Stmt}
    (hb : Balanced s) (hf : ∀ st ∈ prog, NoForget st)
    (h : exec s prog = .ok s') : Balanced s' := by
  induction prog generalizing s with
  | nil =>
    simp only [exec, Except.ok.injEq] at h
    exact h ▸ hb
  | cons st prog ih =>
    simp only [exec] at h
    split at h
    · rename_i s₁ hstep
      exact ih (step_balanced hb (hf st (by simp)) hstep)
        (fun st' hst' => hf st' (by simp [hst'])) h
    · simp at h

-- ANCHOR: exactly_once
/-- **Exactly once.** Without `forget`, every resource that was acquired is
released exactly once by the end of the scope. -/
theorem run_exactly_once {prog : List Stmt} {log : List Event}
    (hf : ∀ st ∈ prog, NoForget st) (h : run prog = .ok log)
    (r : Res) (hr : Event.acquire r ∈ log) : log.count (.release r) = 1 := by
  simp only [run] at h
  split at h
  · rename_i s hexec
    simp only [Except.ok.injEq] at h
    subst h
    have hs := exec_inv inv_init hexec
    have hb := exec_balanced (fun r => by
      simp [State.init, held, released, acquired]) hf hexec
    -- The final log has the same acquisitions, and one release per owner.
    have h1 := released_dropAll s.slots s.log r
    have h2 := acquired_dropAll s.slots s.log r
    have h3 := hb r
    have h4 := hs.once r
    have h5 : 0 < acquired (dropAll s.slots s.log) r := List.count_pos_iff.mpr hr
    simp only [released, acquired] at h1 h2 h3 h4 h5
    omega
  · simp at h
-- ANCHOR_END: exactly_once

-- ANCHOR: forget_breaks
/-- **`forget` breaks "exactly once".** The statement of `run_exactly_once`
without its hypothesis is false: one program is a counterexample. -/
theorem forget_breaks_exactly_once :
    ¬ ∀ (prog : List Stmt) (log : List Event), run prog = .ok log →
        ∀ r, Event.acquire r ∈ log → log.count (.release r) = 1 := by
  intro claim
  -- the program `let conn = ...; mem::forget(conn);`
  have h := claim [.new "conn", .forget "conn"] [.acquire 0] rfl 0 (by simp)
  -- its log has no `release`: the count is 0, not 1
  simp at h
-- ANCHOR_END: forget_breaks

/-! ## Affine in typing: a static move checker -/

-- ANCHOR: checker
/-- The checker's view of a slot: the name and whether it is initialized. -/
abbrev Flag := Var × Bool

def takeFlag (x : Var) : List Flag → Option (List Flag)
  | [] => none
  | (y, b) :: rest =>
    if y = x then (if b then some ((y, false) :: rest) else none)
    else (takeFlag x rest).map ((y, b) :: ·)

def checkStmt (flags : List Flag) : Stmt → Option (List Flag)
  | .new x => some ((x, true) :: flags)
  | .move x y => (takeFlag x flags).map ((y, true) :: ·)
  | .drop x => takeFlag x flags
  | .forget x => takeFlag x flags
  | .read x => (takeFlag x flags).map (fun _ => flags)

/-- Accept a program if no statement uses a moved (or undeclared) variable. -/
def check (flags : List Flag) : List Stmt → Bool
  | [] => true
  | st :: prog =>
    match checkStmt flags st with
    | some flags' => check flags' prog
    | none => false

/-- info: false -/
#guard_msgs in
#eval check [] [.new "conn", .drop "conn", .read "conn"]
-- ANCHOR_END: checker

/-- What the checker sees of the run-time slots: only the drop flags. -/
def erase (slots : List Slot) : List Flag :=
  slots.map fun (x, o) => (x, o.isSome)

theorem take_of_takeFlag {x : Var} {slots : List Slot} {flags' : List Flag}
    (h : takeFlag x (erase slots) = some flags') :
    ∃ r slots', take x slots = .ok (r, slots') ∧ erase slots' = flags' := by
  induction slots generalizing flags' with
  | nil => simp [erase, takeFlag] at h
  | cons slot rest ih =>
    obtain ⟨y, o⟩ := slot
    by_cases hyx : y = x
    · cases o with
      | none => simp [erase, takeFlag, hyx] at h
      | some r =>
        subst hyx
        simp [erase, takeFlag] at h
        subst h
        exact ⟨r, (y, none) :: rest, by simp [take], by simp [erase]⟩
    · simp only [erase, List.map_cons, takeFlag, hyx, ↓reduceIte,
        Option.map_eq_some_iff] at h
      obtain ⟨fs, hfs, rfl⟩ := h
      obtain ⟨r, rest', htake, herase⟩ := ih hfs
      refine ⟨r, (y, o) :: rest', ?_, ?_⟩
      · simp [take, hyx, htake]
      · simp [erase, ← herase]

theorem step_of_checkStmt {s : State} {st : Stmt} {flags' : List Flag}
    (h : checkStmt (erase s.slots) st = some flags') :
    ∃ s', step s st = .ok s' ∧ erase s'.slots = flags' := by
  cases st with
  | new x =>
    simp only [checkStmt, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, by simp [erase]⟩
  | move x y =>
    simp only [checkStmt, Option.map_eq_some_iff] at h
    obtain ⟨fs, hfs, rfl⟩ := h
    obtain ⟨r, slots', htake, herase⟩ := take_of_takeFlag hfs
    exact ⟨⟨(y, some r) :: slots', s.next, s.log⟩, by simp [step, htake],
      by simp [erase, ← herase]⟩
  | drop x =>
    simp only [checkStmt] at h
    obtain ⟨r, slots', htake, herase⟩ := take_of_takeFlag h
    exact ⟨⟨slots', s.next, s.log ++ [.release r]⟩, by simp [step, htake], herase⟩
  | forget x =>
    simp only [checkStmt] at h
    obtain ⟨r, slots', htake, herase⟩ := take_of_takeFlag h
    exact ⟨⟨slots', s.next, s.log⟩, by simp [step, htake], herase⟩
  | read x =>
    simp only [checkStmt, Option.map_eq_some_iff] at h
    obtain ⟨fs, hfs, rfl⟩ := h
    obtain ⟨r, slots', htake, _⟩ := take_of_takeFlag hfs
    exact ⟨s, by simp [step, htake], rfl⟩

theorem exec_of_check {s : State} {prog : List Stmt}
    (h : check (erase s.slots) prog = true) : ∃ s', exec s prog = .ok s' := by
  induction prog generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons st prog ih =>
    simp only [check] at h
    split at h
    · rename_i flags' hcheck
      obtain ⟨s₁, hstep, herase⟩ := step_of_checkStmt hcheck
      obtain ⟨s', hexec⟩ := ih (s := s₁) (herase ▸ h)
      exact ⟨s', by simp [exec, hstep, hexec]⟩
    · simp at h

-- ANCHOR: check_sound
/-- **Well-checked programs do not go wrong**: if the move checker accepts a
program, running it never reports a use of a moved value. -/
theorem check_sound {prog : List Stmt} (h : check [] prog = true) :
    ∃ log, run prog = .ok log := by
  obtain ⟨s, hs⟩ := exec_of_check (s := State.init) h
  exact ⟨dropAll s.slots s.log, by simp [run, hs]⟩
-- ANCHOR_END: check_sound

end Ch24.DropLog
