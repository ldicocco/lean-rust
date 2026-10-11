/-!
# Chapter 25 · Protocols as inductive relations

The lab instrument of `ch25_typestate.rs` (Idle → Calibrated → Measuring), as
a transition relation `Step` and its closure over traces `Run`. A checker
`accepts` decides `Run`. A family of typed programs `Prog i j`, the
typestate API seen as a data type, produces only accepted traces; a complete
session (`Prog .idle .idle`) ends in the final state, stops every measurement
it starts, and finishes with `powerDown`.
-/

namespace Ch25.Protocol

-- ANCHOR: modes
inductive Mode where
  | idle | calibrated | measuring
  deriving DecidableEq

inductive Action where
  | calibrate | start | sample | stop | powerDown
  deriving DecidableEq
-- ANCHOR_END: modes

instance : Repr Mode where
  reprPrec m _ := match m with
    | .idle => "idle" | .calibrated => "calibrated" | .measuring => "measuring"

instance : Repr Action where
  reprPrec a _ := match a with
    | .calibrate => "calibrate" | .start => "start" | .sample => "sample"
    | .stop => "stop" | .powerDown => "powerDown"

-- ANCHOR: step
/-- `Step m a m'`: in mode `m`, action `a` is allowed and leads to mode `m'`. -/
inductive Step : Mode → Action → Mode → Prop where
  | calibrate : Step .idle .calibrate .calibrated
  | start     : Step .calibrated .start .measuring
  | sample    : Step .measuring .sample .measuring
  | stop      : Step .measuring .stop .calibrated
  | powerDown : Step .calibrated .powerDown .idle

/-- `Run m tr m'`: the trace `tr` is allowed from `m` and ends in `m'`. -/
inductive Run : Mode → List Action → Mode → Prop where
  | nil  {m : Mode} : Run m [] m
  | cons {m₁ m₂ m₃ : Mode} {a : Action} {as : List Action} :
      Step m₁ a m₂ → Run m₂ as m₃ → Run m₁ (a :: as) m₃
-- ANCHOR_END: step

-- ANCHOR: accepts
/-- The transition function: the protocol as a run-time check. -/
def next : Mode → Action → Option Mode
  | .idle, .calibrate => some .calibrated
  | .calibrated, .start => some .measuring
  | .measuring, .sample => some .measuring
  | .measuring, .stop => some .calibrated
  | .calibrated, .powerDown => some .idle
  | _, _ => none

def accepts : Mode → List Action → Option Mode
  | m, [] => some m
  | m, a :: as => (next m a).bind fun m' => accepts m' as

/-- info: some idle -/
#guard_msgs in
#eval accepts .idle [.calibrate, .start, .sample, .sample, .stop, .powerDown]

/-- info: none -/
#guard_msgs in
#eval accepts .idle [.calibrate, .sample]
-- ANCHOR_END: accepts

-- ANCHOR: accepts_iff
theorem next_iff {m m' : Mode} {a : Action} : next m a = some m' ↔ Step m a m' := by
  constructor
  · intro h
    -- 15 combinations of mode and action; `simp [next]` discards the ones
    -- where `next` is `none`, and each remaining one is a constructor.
    cases m <;> cases a <;> simp [next] at h <;> subst h <;> constructor
  · intro h
    cases h <;> rfl

theorem accepts_iff {m m' : Mode} {tr : List Action} :
    accepts m tr = some m' ↔ Run m tr m' := by
  induction tr generalizing m with
  | nil =>
    constructor
    · intro h
      simp only [accepts, Option.some.injEq] at h
      subst h
      exact .nil
    · intro h
      cases h
      rfl
  | cons a as ih =>
    constructor
    · intro h
      simp only [accepts, Option.bind_eq_some_iff] at h
      obtain ⟨m₂, h₁, h₂⟩ := h
      exact .cons (next_iff.mp h₁) (ih.mp h₂)
    · intro h
      cases h with
      | cons hs hr => simp [accepts, next_iff.mpr hs, ih.mpr hr]

/-- A concrete run, proved by computation through `accepts_iff`. -/
example : Run .idle [.calibrate, .start, .sample, .stop, .powerDown] .idle :=
  accepts_iff.mp rfl
-- ANCHOR_END: accepts_iff

-- ANCHOR: balance
/-- 1 in the mode where a measurement is running, 0 elsewhere. -/
def running : Mode → Nat
  | .measuring => 1
  | _ => 0

/-- Along any run, starts and stops balance, up to the measurement that may
be running at the beginning or at the end. -/
theorem run_balance {m m' : Mode} {tr : List Action} (h : Run m tr m') :
    tr.count .start + running m = tr.count .stop + running m' := by
  induction h with
  | nil => simp
  | cons hs hr ih =>
    -- one case per kind of step; `simp_all` unfolds the counts, `omega`
    -- does the arithmetic
    cases hs <;> simp_all [running] <;> omega

/-- A complete session (from idle back to idle) stops every measurement it
starts. -/
theorem complete_balanced {tr : List Action} (h : Run .idle tr .idle) :
    tr.count .start = tr.count .stop := by
  simpa [running] using run_balance h
-- ANCHOR_END: balance

-- ANCHOR: last_action
/-- A nonempty run that ends in `idle` ends with `powerDown`: it is the only
action that leads to `idle`. -/
theorem ends_with_powerDown {m m' : Mode} {tr : List Action} (h : Run m tr m')
    (hm : m' = .idle) (hne : tr ≠ []) : tr.getLast? = some .powerDown := by
  induction h with
  | nil => contradiction
  | cons hs hr ih =>
    rename_i m₁ m₂ m₃ a as
    cases as with
    | nil =>
      -- the step `hs` is the last one, and it leads to `idle`
      cases hr
      subst hm
      cases hs
      rfl
    | cons b bs =>
      -- the last action is the last action of the rest of the run
      have := ih hm (by simp)
      simpa [List.getLast?_cons_cons] using this
-- ANCHOR_END: last_action

-- ANCHOR: prog
/-- Programs that drive the instrument from mode `i` to mode `j`. Each
constructor is one operation of the typestate API: `calibrate` turns a
program that starts calibrated into one that starts idle. -/
inductive Prog : Mode → Mode → Type where
  | done {m : Mode} : Prog m m
  | calibrate {m : Mode} : Prog .calibrated m → Prog .idle m
  | start {m : Mode} : Prog .measuring m → Prog .calibrated m
  | sample {m : Mode} : Prog .measuring m → Prog .measuring m
  | stop {m : Mode} : Prog .calibrated m → Prog .measuring m
  | powerDown {m : Mode} : Prog .idle m → Prog .calibrated m

/-- The actions a program performs, in order. -/
def Prog.trace {i j : Mode} : Prog i j → List Action
  | .done => []
  | .calibrate p => .calibrate :: p.trace
  | .start p => .start :: p.trace
  | .sample p => .sample :: p.trace
  | .stop p => .stop :: p.trace
  | .powerDown p => .powerDown :: p.trace

def shift : Prog .idle .idle :=
  .calibrate <| .start <| .sample <| .sample <| .stop <| .powerDown .done

/-- info: [calibrate, start, sample, sample, stop, powerDown] -/
#guard_msgs in
#eval shift.trace
-- ANCHOR_END: prog

-- ANCHOR: prog_sound
/-- **Typed programs follow the protocol**: the trace of a `Prog i j` is a run
from `i` to `j`. -/
theorem Prog.trace_run {i j : Mode} (p : Prog i j) : Run i p.trace j := by
  induction p with
  | done => exact .nil
  | calibrate p ih => exact .cons .calibrate ih
  | start p ih => exact .cons .start ih
  | sample p ih => exact .cons .sample ih
  | stop p ih => exact .cons .stop ih
  | powerDown p ih => exact .cons .powerDown ih

/-- **Every complete session ends in the final state**, and so the run-time
check accepts its trace with result `idle`, its starts and stops balance, and
(if it does anything) it ends by powering down. -/
theorem session_complete (p : Prog .idle .idle) :
    accepts .idle p.trace = some .idle ∧
    p.trace.count .start = p.trace.count .stop ∧
    (p.trace ≠ [] → p.trace.getLast? = some .powerDown) :=
  ⟨accepts_iff.mpr p.trace_run,
   complete_balanced p.trace_run,
   ends_with_powerDown p.trace_run rfl⟩
-- ANCHOR_END: prog_sound

end Ch25.Protocol
