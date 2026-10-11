import Book.Ch26.Heap

/-!
# Chapter 26 · Three disciplines for the heap language

Three static checks for the language of `Book/Ch26/Heap.lean`:

* a *naive* check that tracks which variables have been freed, and accepts
  the use after free (it is unsound);
* an *affine* check that treats pointers as resources that are moved, not
  copied; it rejects the use after free, and also a perfectly safe program;
* a *region* discipline: every pointer type names the region it points into,
  copies share the region, and `free` kills the region for every alias at once.

For the region discipline we give typing rules, a checker with error messages
(proved equivalent to the rules), and a type-safety theorem: a well-typed
program never reaches a stuck state.
-/

namespace Ch26

open Function (update update_self update_of_ne)

/-! ## Tracking variables is not enough -/

-- ANCHOR: naive
/-- Track *variables*: `free x` marks `x` as dead, and a dead variable may not
be used again. Pointers can be copied freely, like Rust's `&T`. -/
def naiveCheck (dead : List Var) : Prog → Bool
  | [] => true
  | .alloc x _ :: k => naiveCheck (dead.erase x) k
  | .copy y x :: k => !dead.contains x && naiveCheck (dead.erase y) k
  | .read y x :: k => !dead.contains x && naiveCheck (dead.erase y) k
  | .write x _ :: k => !dead.contains x && naiveCheck dead k
  | .free x :: k => !dead.contains x && naiveCheck (x :: dead) k

/-- The naive check accepts the use after free... -/
theorem naive_accepts_uaf : naiveCheck [] uaf = true := rfl

/-- ...so it does not guarantee safety. -/
theorem naive_unsound : ¬ ∀ p, naiveCheck [] p = true → ¬ GoesWrong p :=
  fun h => h uaf naive_accepts_uaf uaf_goes_wrong
-- ANCHOR_END: naive

-- ANCHOR: affine
/-- Treat pointers as affine resources, like Rust's `Box<T>`: `copy y x`
*moves* the pointer from `x` to `y`, so `x` is dead afterwards. -/
def affineCheck (dead : List Var) : Prog → Bool
  | [] => true
  | .alloc x _ :: k => affineCheck (dead.erase x) k
  | .copy y x :: k => !dead.contains x && affineCheck ((x :: dead).erase y) k
  | .read y x :: k => !dead.contains x && affineCheck (dead.erase y) k
  | .write x _ :: k => !dead.contains x && affineCheck dead k
  | .free x :: k => !dead.contains x && affineCheck (x :: dead) k

/-- The affine check rejects the use after free... -/
theorem affine_rejects_uaf : affineCheck [] uaf = false := rfl

/-- ...but it also rejects `share`, which runs safely (`share_finishes`). -/
theorem affine_rejects_share : affineCheck [] share = false := rfl
-- ANCHOR_END: affine

/-! ## Regions -/

-- ANCHOR: region_types
/-- The type of a variable: a number, or a pointer into region `ρ`. -/
inductive Ty where
  | num
  | ref (ρ : ℕ)
  deriving DecidableEq, Repr

/-- The static context: the type of each variable, the set of live regions,
and the next unused region name. -/
structure Ctx where
  ty : Var → Option Ty
  live : ℕ → Bool
  fresh : ℕ

/-- The context of the empty program: no variables, no live regions. -/
def Ctx.init : Ctx where
  ty := fun _ => none
  live := fun _ => false
  fresh := 0
-- ANCHOR_END: region_types

-- ANCHOR: region_rules
/-- `CmdOK Γ c Γ'`: in the context `Γ` the command `c` is well typed and
leaves the context `Γ'`. Every use of a pointer requires its region to be
live; `free` ends the region. -/
inductive CmdOK : Ctx → Cmd → Ctx → Prop where
  | alloc {Γ : Ctx} {x : Var} {n : ℕ} :
      CmdOK Γ (.alloc x n)
        { ty := update Γ.ty x (some (.ref Γ.fresh))
          live := update Γ.live Γ.fresh true
          fresh := Γ.fresh + 1 }
  | copyNum {Γ : Ctx} {y x : Var} (hx : Γ.ty x = some .num) :
      CmdOK Γ (.copy y x) { Γ with ty := update Γ.ty y (some .num) }
  | copyRef {Γ : Ctx} {y x : Var} {ρ : ℕ}
      (hx : Γ.ty x = some (.ref ρ)) (hρ : Γ.live ρ = true) :
      CmdOK Γ (.copy y x) { Γ with ty := update Γ.ty y (some (.ref ρ)) }
  | read {Γ : Ctx} {y x : Var} {ρ : ℕ}
      (hx : Γ.ty x = some (.ref ρ)) (hρ : Γ.live ρ = true) :
      CmdOK Γ (.read y x) { Γ with ty := update Γ.ty y (some .num) }
  | write {Γ : Ctx} {x : Var} {n : ℕ} {ρ : ℕ}
      (hx : Γ.ty x = some (.ref ρ)) (hρ : Γ.live ρ = true) :
      CmdOK Γ (.write x n) Γ
  | free {Γ : Ctx} {x : Var} {ρ : ℕ}
      (hx : Γ.ty x = some (.ref ρ)) (hρ : Γ.live ρ = true) :
      CmdOK Γ (.free x) { Γ with live := update Γ.live ρ false }

/-- A program is well typed when each command is, in the context that the
previous command leaves. -/
inductive ProgOK : Ctx → Prog → Prop where
  | nil {Γ : Ctx} : ProgOK Γ []
  | cons {Γ Γ' : Ctx} {c : Cmd} {k : Prog} :
      CmdOK Γ c Γ' → ProgOK Γ' k → ProgOK Γ (c :: k)
-- ANCHOR_END: region_rules

/-! ## A region checker with error messages -/

-- ANCHOR: region_check
/-- Why a command is rejected. -/
inductive RegionError where
  | unknown (x : Var)               -- `x` has no type yet
  | notAPointer (x : Var)           -- `x` holds a number
  | deadRegion (x : Var) (ρ : ℕ)  -- `x` points into region `ρ`, which has ended
  deriving Repr

/-- The region that the pointer in `x` points into, if that region is live. -/
def liveRegion (Γ : Ctx) (x : Var) : Except RegionError ℕ :=
  match Γ.ty x with
  | none => .error (.unknown x)
  | some .num => .error (.notAPointer x)
  | some (.ref ρ) => if Γ.live ρ then .ok ρ else .error (.deadRegion x ρ)

/-- Check one command, computing the context it leaves. -/
def checkCmd (Γ : Ctx) : Cmd → Except RegionError Ctx
  | .alloc x _ => .ok { ty := update Γ.ty x (some (.ref Γ.fresh))
                        live := update Γ.live Γ.fresh true
                        fresh := Γ.fresh + 1 }
  | .copy y x =>
    match Γ.ty x with
    | some .num => .ok { Γ with ty := update Γ.ty y (some .num) }
    | _ =>
      match liveRegion Γ x with
      | .error e => .error e
      | .ok ρ => .ok { Γ with ty := update Γ.ty y (some (.ref ρ)) }
  | .read y x =>
    match liveRegion Γ x with
    | .error e => .error e
    | .ok _ => .ok { Γ with ty := update Γ.ty y (some .num) }
  | .write x _ =>
    match liveRegion Γ x with
    | .error e => .error e
    | .ok _ => .ok Γ
  | .free x =>
    match liveRegion Γ x with
    | .error e => .error e
    | .ok ρ => .ok { Γ with live := update Γ.live ρ false }

/-- Check a whole program, stopping at the first error. -/
def check (Γ : Ctx) : Prog → Except RegionError Unit
  | [] => .ok ()
  | c :: k =>
    match checkCmd Γ c with
    | .error e => .error e
    | .ok Γ' => check Γ' k
-- ANCHOR_END: region_check

-- ANCHOR: region_check_eval
/-- info: Except.ok () -/
#guard_msgs in
#eval check Ctx.init share

/-- info: Except.error (Ch26.RegionError.deadRegion "y" 0) -/
#guard_msgs in
#eval check Ctx.init uaf

/-- info: Except.error (Ch26.RegionError.deadRegion "y" 0) -/
#guard_msgs in
#eval check Ctx.init doubleFree
-- ANCHOR_END: region_check_eval

/-! ## The checker decides the typing rules -/

theorem liveRegion_ok {Γ : Ctx} {x : Var} {ρ : ℕ} :
    liveRegion Γ x = .ok ρ ↔ Γ.ty x = some (.ref ρ) ∧ Γ.live ρ = true := by
  unfold liveRegion
  rcases hx : Γ.ty x with _ | _ | ρ'
  · simp
  · simp
  · by_cases hl : Γ.live ρ' = true
    · simp only [hl, ite_true, Except.ok.injEq, Option.some.injEq, Ty.ref.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, hl⟩
      · rintro ⟨rfl, -⟩
        rfl
    · simp only [hl, Bool.false_eq_true, ite_false, reduceCtorEq,
        Option.some.injEq, Ty.ref.injEq, false_iff, not_and]
      rintro rfl
      exact hl

theorem checkCmd_ok {Γ Γ' : Ctx} {c : Cmd} :
    checkCmd Γ c = .ok Γ' ↔ CmdOK Γ c Γ' := by
  constructor
  · intro h
    cases c with
    | alloc x n =>
      simp only [checkCmd, Except.ok.injEq] at h
      subst h
      exact CmdOK.alloc
    | copy y x =>
      simp only [checkCmd] at h
      split at h
      · rename_i hx
        simp only [Except.ok.injEq] at h
        subst h
        exact CmdOK.copyNum hx
      · split at h
        · cases h
        · rename_i ρ hr
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨hx, hρ⟩ := liveRegion_ok.mp hr
          exact CmdOK.copyRef hx hρ
    | read y x =>
      simp only [checkCmd] at h
      split at h
      · cases h
      · rename_i ρ hr
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hx, hρ⟩ := liveRegion_ok.mp hr
        exact CmdOK.read hx hρ
    | write x n =>
      simp only [checkCmd] at h
      split at h
      · cases h
      · rename_i ρ hr
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hx, hρ⟩ := liveRegion_ok.mp hr
        exact CmdOK.write hx hρ
    | free x =>
      simp only [checkCmd] at h
      split at h
      · cases h
      · rename_i ρ hr
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hx, hρ⟩ := liveRegion_ok.mp hr
        exact CmdOK.free hx hρ
  · intro h
    cases h with
    | alloc => rfl
    | copyNum hx => simp [checkCmd, hx]
    | copyRef hx hρ =>
      have hr := liveRegion_ok.mpr ⟨hx, hρ⟩
      simp [checkCmd, hx, hr]
    | read hx hρ =>
      have hr := liveRegion_ok.mpr ⟨hx, hρ⟩
      simp [checkCmd, hr]
    | write hx hρ =>
      have hr := liveRegion_ok.mpr ⟨hx, hρ⟩
      simp [checkCmd, hr]
    | free hx hρ =>
      have hr := liveRegion_ok.mpr ⟨hx, hρ⟩
      simp [checkCmd, hr]

-- ANCHOR: check_ok
/-- The checker accepts a program exactly when the typing rules do. -/
theorem check_ok {Γ : Ctx} {p : Prog} : check Γ p = .ok () ↔ ProgOK Γ p := by
  induction p generalizing Γ with
  | nil => exact ⟨fun _ => ProgOK.nil, fun _ => rfl⟩
  | cons c k ih =>
    constructor
    · intro h
      simp only [check] at h
      split at h
      · cases h
      · rename_i Γ' hc
        exact ProgOK.cons (checkCmd_ok.mp hc) (ih.mp h)
    · intro h
      cases h with
      | cons hc hk =>
        simp only [check, checkCmd_ok.mpr hc]
        exact ih.mpr hk

/-- So the typing judgment is decidable, and `decide` can use the checker. -/
instance (Γ : Ctx) (p : Prog) : Decidable (ProgOK Γ p) :=
  match h : check Γ p with
  | .ok () => isTrue (check_ok.mp h)
  | .error _ => isFalse fun hp => by rw [check_ok.mpr hp] at h; cases h

theorem share_typed : ProgOK Ctx.init share := by decide

theorem uaf_rejected : ¬ ProgOK Ctx.init uaf := by decide

theorem doubleFree_rejected : ¬ ProgOK Ctx.init doubleFree := by decide
-- ANCHOR_END: check_ok

/-! ## Safety: well-typed programs never get stuck -/

-- ANCHOR: agree
/-- How a static context describes a run-time state. `owner` says which region
each heap cell belongs to. It is *ghost* information: it exists in the proof,
not in the program or the machine. -/
structure Agree (Γ : Ctx) (s : State) (owner : ℕ → ℕ) : Prop where
  /-- Variables typed `num` hold numbers. -/
  nums : ∀ x, Γ.ty x = some .num → ∃ n, s.env x = some (.num n)
  /-- Variables typed `ref ρ` hold the address of a cell of region `ρ`. -/
  refs : ∀ x ρ, Γ.ty x = some (.ref ρ) →
    ∃ l, s.env x = some (.addr l) ∧ l < s.next ∧ owner l = ρ
  /-- Every cell allocated so far belongs to a region that has been named. -/
  named : ∀ l, l < s.next → owner l < Γ.fresh
  /-- The cells of a live region are allocated. -/
  alive : ∀ l, l < s.next → Γ.live (owner l) = true → s.heap l ≠ none
-- ANCHOR_END: agree

/-- The empty state agrees with the empty context. -/
theorem agree_init : Agree Ctx.init State.init (fun _ => 0) where
  nums _ h := by simp [Ctx.init] at h
  refs _ _ h := by simp [Ctx.init] at h
  named _ h := by simp [State.init] at h
  alive _ h := by simp [State.init] at h

-- ANCHOR: progress
/-- Progress: a well-typed command can run in any state that agrees with
its context. -/
theorem progress {Γ Γ' : Ctx} {c : Cmd} {s : State} {owner : ℕ → ℕ}
    (hc : CmdOK Γ c Γ') (ha : Agree Γ s owner) (k : Prog) :
    ∃ s', Step (c :: k, s) (k, s') := by
  cases hc with
  | alloc => exact ⟨_, Step.alloc⟩
  | copyNum hx =>
    obtain ⟨n, hn⟩ := ha.nums _ hx
    exact ⟨_, Step.copy hn⟩
  | copyRef hx _ =>
    obtain ⟨l, hl, -, -⟩ := ha.refs _ _ hx
    exact ⟨_, Step.copy hl⟩
  | read hx hρ =>
    -- `x` points to a cell `l` of region `ρ`; `ρ` is live, so `l` is allocated.
    obtain ⟨l, hl, hlt, rfl⟩ := ha.refs _ _ hx
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp (ha.alive l hlt hρ)
    exact ⟨_, Step.read hl hn⟩
  | write hx hρ =>
    obtain ⟨l, hl, hlt, rfl⟩ := ha.refs _ _ hx
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (ha.alive l hlt hρ)
    exact ⟨_, Step.write hl hm⟩
  | free hx hρ =>
    obtain ⟨l, hl, hlt, rfl⟩ := ha.refs _ _ hx
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (ha.alive l hlt hρ)
    exact ⟨_, Step.free hl hm⟩
-- ANCHOR_END: progress

-- ANCHOR: preservation_free
/-- The heart of the matter: after `free x`, every alias of `x` is dead in
the context, and every pointer that is still live points to an allocated cell. -/
theorem agree_free {Γ : Ctx} {s : State} {owner : ℕ → ℕ} {x : Var}
    {ρ : ℕ} {l : ℕ} (ha : Agree Γ s owner) (hx : Γ.ty x = some (.ref ρ))
    (hl : s.env x = some (.addr l)) :
    Agree { Γ with live := update Γ.live ρ false }
      { s with heap := update s.heap l none } owner where
  nums := ha.nums
  refs := ha.refs
  named := ha.named
  alive l' hl' hlive := by
    -- The cell `l` that was freed belongs to `ρ`, the region that just ended.
    obtain ⟨l₀, hl₀, -, hown⟩ := ha.refs x ρ hx
    rw [hl, Option.some.injEq, Val.addr.injEq] at hl₀
    subst hl₀
    -- `l'` belongs to a region that is still live, so it is not `ρ`...
    have hne : owner l' ≠ ρ := by
      intro h
      simp [h] at hlive
    -- ...hence `l'` is not the freed cell, and its contents are unchanged.
    have hl'l : l' ≠ l := by
      rintro rfl
      exact hne hown
    simp only [update_of_ne hl'l]
    simp only [update_of_ne hne] at hlive
    exact ha.alive l' hl' hlive
-- ANCHOR_END: preservation_free

/-- After an allocation into `x`, the context and the state still agree, with
the new cell owned by the fresh region. -/
theorem agree_alloc {Γ : Ctx} {s : State} {owner : ℕ → ℕ} {x : Var} {n : ℕ}
    (ha : Agree Γ s owner) :
    Agree { ty := update Γ.ty x (some (.ref Γ.fresh))
            live := update Γ.live Γ.fresh true
            fresh := Γ.fresh + 1 }
      { env := update s.env x (some (.addr s.next))
        heap := update s.heap s.next (some n)
        next := s.next + 1 }
      (update owner s.next Γ.fresh) where
  nums z hz := by
    dsimp only at hz ⊢
    by_cases h : z = x
    · subst h
      simp at hz
    · simp only [update_of_ne h] at hz ⊢
      exact ha.nums z hz
  refs z ρ hz := by
    dsimp only at hz ⊢
    by_cases h : z = x
    · subst h
      simp only [update_self, Option.some.injEq, Ty.ref.injEq] at hz
      subst hz
      exact ⟨s.next, by simp, by omega, by simp⟩
    · simp only [update_of_ne h] at hz ⊢
      obtain ⟨l, hl, hlt, hown⟩ := ha.refs z ρ hz
      have hne : l ≠ s.next := by omega
      exact ⟨l, hl, by omega, by simp [update_of_ne hne, hown]⟩
  named l hl := by
    dsimp only at hl ⊢
    by_cases h : l = s.next
    · subst h
      simp
    · have hlt : l < s.next := by omega
      simp only [update_of_ne h]
      have := ha.named l hlt
      omega
  alive l hl hlive := by
    dsimp only at hl hlive ⊢
    by_cases h : l = s.next
    · subst h
      simp
    · have hlt : l < s.next := by omega
      -- An old cell belongs to an old region, which is not the fresh one.
      have hold : owner l ≠ Γ.fresh := by
        have := ha.named l hlt
        omega
      simp only [update_of_ne h, update_of_ne hold] at hlive ⊢
      exact ha.alive l hlt hlive

/-- Copying a value into `y` gives `y` the type of `x`. -/
theorem agree_copy {Γ : Ctx} {s : State} {owner : ℕ → ℕ} {y : Var} {τ : Ty}
    {v : Val} (ha : Agree Γ s owner)
    (hv : (τ = .num → ∃ n, v = .num n) ∧
      (∀ ρ, τ = .ref ρ → ∃ l, v = .addr l ∧ l < s.next ∧ owner l = ρ)) :
    Agree { Γ with ty := update Γ.ty y (some τ) }
      { s with env := update s.env y (some v) } owner where
  nums z hz := by
    by_cases h : z = y
    · subst h
      simp only [update_self, Option.some.injEq] at hz ⊢
      obtain ⟨n, rfl⟩ := hv.1 hz
      exact ⟨n, rfl⟩
    · simp only [update_of_ne h] at hz ⊢
      exact ha.nums z hz
  refs z ρ hz := by
    by_cases h : z = y
    · subst h
      simp only [update_self, Option.some.injEq] at hz ⊢
      obtain ⟨l, rfl, hlt, hown⟩ := hv.2 ρ hz
      exact ⟨l, rfl, hlt, hown⟩
    · simp only [update_of_ne h] at hz ⊢
      exact ha.refs z ρ hz
  named := ha.named
  alive := ha.alive

/-- Writing changes the contents of a cell, not whether it is allocated. -/
theorem agree_write {Γ : Ctx} {s : State} {owner : ℕ → ℕ} {l n : ℕ}
    (ha : Agree Γ s owner) :
    Agree Γ { s with heap := update s.heap l (some n) } owner where
  nums := ha.nums
  refs := ha.refs
  named := ha.named
  alive l' hl' hlive := by
    by_cases h : l' = l
    · subst h
      simp
    · simp only [update_of_ne h]
      exact ha.alive l' hl' hlive

-- ANCHOR: preservation
/-- Preservation: if a well-typed command takes a step, the new state agrees
with the context the command leaves (for a suitable ghost `owner`). -/
theorem preservation {Γ Γ' : Ctx} {c : Cmd} {k k' : Prog} {s s' : State}
    {owner : ℕ → ℕ} (hc : CmdOK Γ c Γ') (ha : Agree Γ s owner)
    (hs : Step (c :: k, s) (k', s')) : k' = k ∧ ∃ owner', Agree Γ' s' owner' := by
  cases hc with
  | alloc =>
    cases hs
    exact ⟨rfl, _, agree_alloc ha⟩
  | copyNum hx =>
    cases hs with
    | copy hv =>
      obtain ⟨n, hn⟩ := ha.nums _ hx
      rw [hn, Option.some.injEq] at hv
      subst hv
      exact ⟨rfl, owner, agree_copy ha ⟨fun _ => ⟨n, rfl⟩, fun _ h => by cases h⟩⟩
  | copyRef hx _ =>
    cases hs with
    | copy hv =>
      obtain ⟨l, hl, hlt, hown⟩ := ha.refs _ _ hx
      rw [hl, Option.some.injEq] at hv
      subst hv
      refine ⟨rfl, owner, agree_copy ha ⟨(fun h => by cases h), ?_⟩⟩
      intro ρ' h
      cases h
      exact ⟨l, rfl, hlt, hown⟩
  | read hx _ =>
    cases hs with
    | read _ _ =>
      exact ⟨rfl, owner, agree_copy ha ⟨fun _ => ⟨_, rfl⟩, fun _ h => by cases h⟩⟩
  | write hx _ =>
    cases hs with
    | write _ _ => exact ⟨rfl, owner, agree_write ha⟩
  | free hx _ =>
    cases hs with
    | free hl _ => exact ⟨rfl, owner, agree_free ha hx hl⟩
-- ANCHOR_END: preservation

-- ANCHOR: safety
/-- A configuration is well typed when some context describes both the
program still to run and the current state. -/
def Typed (c : Prog × State) : Prop :=
  ∃ Γ owner, ProgOK Γ c.1 ∧ Agree Γ c.2 owner

/-- A well-typed configuration is not stuck. -/
theorem Typed.not_stuck {c : Prog × State} (h : Typed c) : ¬ Stuck c := by
  obtain ⟨p, s⟩ := c
  obtain ⟨Γ, owner, hp, ha⟩ := h
  rintro ⟨hne, hno⟩
  cases hp with
  | nil => exact hne rfl
  | cons hc _ =>
    obtain ⟨s', hs⟩ := progress hc ha _
    exact hno ⟨_, hs⟩

/-- A step from a well-typed configuration leads to a well-typed one. -/
theorem Typed.step {c c' : Prog × State} (h : Typed c) (hs : Step c c') :
    Typed c' := by
  obtain ⟨p, s⟩ := c
  obtain ⟨p', s'⟩ := c'
  obtain ⟨Γ, owner, hp, ha⟩ := h
  cases hp with
  | nil => cases hs
  | cons hc hk =>
    obtain ⟨rfl, owner', ha'⟩ := preservation hc ha hs
    exact ⟨_, owner', hk, ha'⟩

/-- Any number of steps preserve typing. -/
theorem Typed.steps {c c' : Prog × State} (h : Typed c) (hs : Steps c c') :
    Typed c' := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.step hstep

/-- **Region safety.** A program accepted by the region discipline never goes
wrong: no use after free, no double free, no dangling write. -/
theorem regions_safe {p : Prog} (h : ProgOK Ctx.init p) : ¬ GoesWrong p := by
  rintro ⟨c, hs, hstuck⟩
  have ht : Typed (p, State.init) := ⟨Ctx.init, fun _ => 0, h, agree_init⟩
  exact (ht.steps hs).not_stuck hstuck
-- ANCHOR_END: safety

end Ch26
