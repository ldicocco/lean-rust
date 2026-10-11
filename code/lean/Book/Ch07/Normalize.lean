import Book.Ch07.Untyped

/-!
# Chapter 7 · Normalizing λ-terms

A normal-order step function, proved sound and complete with respect to the
`Step` relation; a normalizer with fuel, proved sound; Church arithmetic
checked by computation; and what happens without fuel: the termination checker
rejects the definition, and `partial def` makes it opaque.
-/

namespace Ch07

open Term

-- ANCHOR: step_fn
/-- One step of normal-order reduction: contract the leftmost-outermost redex,
or return `none` if there is no redex. -/
def step : Term → Option Term
  | var _ => none
  | lam t => (step t).map lam
  | app (lam t) s => some (subst 0 s t)
  | app t s =>
    match step t with
    | some t' => some (app t' s)
    | none => (step s).map (app t)
-- ANCHOR_END: step_fn

-- ANCHOR: step_sound
/-- Every step that `step` takes is a `Step`. -/
theorem step_sound {t u : Term} (h : step t = some u) : Step t u := by
  fun_induction step t generalizing u with
  | case1 =>
    -- `step (var k) = none`, so `h : none = some u` is impossible.
    contradiction
  | case2 t ih =>
    -- `h : Option.map lam (step t) = some u`: the body stepped to some `t'`.
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    exact Step.body (ih ht')
  | case3 t s =>
    -- A redex: `h : some (subst 0 s t) = some u`.
    cases h
    exact Step.beta t s
  | case4 t s _ t' ht ih =>
    -- The function part stepped: `ht : step t = some t'`.
    cases h
    exact Step.appL s (ih ht)
  | case5 t s _ _ _ ih =>
    -- The function part is normal and the argument stepped.
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact Step.appR t (ih hs')
-- ANCHOR_END: step_sound

-- ANCHOR: step_app
/-- How `step` unfolds on an application whose function part is not a `λ`. -/
theorem step_app {t s : Term} (ht : ∀ b, t ≠ lam b) :
    step (app t s) =
      match step t with
      | some t' => some (app t' s)
      | none => (step s).map (app t) := by
  rw [step.eq_4]
  exact fun b h => ht b h
-- ANCHOR_END: step_app

-- ANCHOR: step_complete
/-- If any `Step` is possible, `step` finds one: `step` returns `none` only on
normal forms. -/
theorem step_complete {t u : Term} (h : Step t u) : (step t).isSome := by
  induction h with
  | beta t s =>
    -- A redex at the root: the third equation of `step` applies.
    simp [step]
  | @appL t t' s _ ih =>
    -- `t` can step, so `step t` is `some _` (the induction hypothesis).
    cases t with
    | var k => simp [step] at ih
    | lam b => simp [step]
    | app t₁ t₂ =>
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ih
      rw [step_app (by simp), hu]
      rfl
  | @appR t s s' _ ih =>
    -- `s` can step. Either `t` is a `λ` (then the root is a redex), or
    -- `step` tries `t` first and, if `t` is normal, steps `s`.
    cases t with
    | lam b => simp [step]
    | _ =>
      rw [step_app (by simp)]
      split
      · rfl
      · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ih
        simp [hu]
  | body _ ih =>
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ih
    simp [step, hu]

/-- So `step t = none` means that `t` is in normal form. -/
theorem normal_of_step_none {t : Term} (h : step t = none) : Normal t := by
  intro t' hstep
  have := step_complete hstep
  rw [h] at this
  contradiction
-- ANCHOR_END: step_complete

-- ANCHOR: normalize
/-- Normal-order reduction for at most `fuel` steps: `some u` if a normal form
`u` was reached, `none` if the fuel ran out. -/
def normalize : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, t =>
    match step t with
    | none => some t
    | some t' => normalize fuel t'
-- ANCHOR_END: normalize

-- ANCHOR: normalize_sound
/-- What `normalize` returns is a normal form of its input. -/
theorem normalize_sound {fuel : Nat} {t u : Term} (h : normalize fuel t = some u) :
    Steps t u ∧ Normal u := by
  induction fuel generalizing t with
  | zero =>
    -- No fuel: `normalize 0 t = none`, so `h` is impossible.
    simp [normalize] at h
  | succ fuel ih =>
    cases hs : step t with
    | none =>
      -- `t` is already normal and `normalize` returned it.
      simp [normalize, hs] at h
      subst h
      exact ⟨Relation.ReflTransGen.refl, normal_of_step_none hs⟩
    | some t' =>
      -- One step to `t'`, then the induction hypothesis for the rest.
      simp [normalize, hs] at h
      obtain ⟨hsteps, hnormal⟩ := ih h
      exact ⟨Relation.ReflTransGen.head (step_sound hs) hsteps, hnormal⟩
-- ANCHOR_END: normalize_sound

-- ANCHOR: church
/-- `f (f (... (f x)))` with `n` copies of `f`, where `f` is the variable `k`
and `x` is the variable `0`. -/
def iterApp (k : Nat) : Nat → Term
  | 0 => var 0
  | n + 1 => app (var k) (iterApp k n)

/-- The Church numeral `n = λf. λx. f (... (f x))`: `f` is index 1, `x` is 0. -/
def church (n : Nat) : Term := lam (lam (iterApp 1 n))

/-- `succ = λn. λf. λx. f (n f x)` -/
def succ : Term := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- `plus = λm. λn. λf. λx. m f (n f x)` -/
def plus : Term :=
  lam (lam (lam (lam (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))

/-- `times = λm. λn. λf. m (n f)` -/
def times : Term := lam (lam (lam (app (var 2) (app (var 1) (var 0)))))
-- ANCHOR_END: church

-- ANCHOR: church_eval
/-- info: λ. λ. 1 (1 (1 0)) -/
#guard_msgs in
#eval church 3

/-- info: some (λ. λ. 1 (1 (1 (1 (1 0))))) -/
#guard_msgs in
#eval normalize 100 (app (app plus (church 2)) (church 3))

/-- info: none -/
#guard_msgs in
#eval normalize 100 omega
-- ANCHOR_END: church_eval

-- ANCHOR: church_theorems
/-- `2 + 3` reduces to `5`: `normalize` computes the answer, and
`normalize_sound` turns the computation into a proof. -/
theorem two_plus_three : Steps (app (app plus (church 2)) (church 3)) (church 5) :=
  (normalize_sound (fuel := 100) (by decide)).1

theorem two_times_three : Steps (app (app times (church 2)) (church 3)) (church 6) :=
  (normalize_sound (fuel := 100) (by decide)).1
-- ANCHOR_END: church_theorems

-- ANCHOR: succ_lemmas
/-- Church numerals are closed, so shifting does not change them. -/
theorem shift_iterApp (c n : Nat) : shift (c + 2) (iterApp 1 n) = iterApp 1 n := by
  induction n with
  | zero => simp [iterApp, shift]
  | succ n ih => simp [iterApp, shift, ih]

theorem shift_church (c n : Nat) : shift c (church n) = church n := by
  simp [church, shift, shift_iterApp]

/-- Substituting for `f` (index 1) renames it to index 2... -/
theorem subst_iterApp_f (n : Nat) :
    subst 1 (var 2) (iterApp 1 n) = iterApp 2 n := by
  induction n with
  | zero => simp [iterApp, subst]
  | succ n ih => simp [iterApp, subst, ih]

/-- ...and substituting `x` (index 0) for itself lowers index 2 back to 1. -/
theorem subst_iterApp_x (n : Nat) :
    subst 0 (var 0) (iterApp 2 n) = iterApp 1 n := by
  induction n with
  | zero => simp [iterApp, subst]
  | succ n ih => simp [iterApp, subst, ih]
-- ANCHOR_END: succ_lemmas

-- ANCHOR: steps_congr
/-- Reduction sequences can be carried out under a `λ`... -/
theorem steps_body {t t' : Term} (h : Steps t t') : Steps (lam t) (lam t') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Step.body hstep)

/-- ...and inside the argument of an application. -/
theorem steps_appR (t : Term) {s s' : Term} (h : Steps s s') :
    Steps (app t s) (app t s') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Step.appR t hstep)
-- ANCHOR_END: steps_congr

-- ANCHOR: succ_correct
/-- For every `n`, `succ (church n)` reduces to `church (n + 1)`. -/
theorem succ_correct (n : Nat) : Steps (app succ (church n)) (church (n + 1)) := by
  -- Step 1, the outer redex: `succ (church n)` becomes `λ. λ. 1 (church n 1 0)`.
  have h1 : Step (app succ (church n))
      (lam (lam (app (var 1) (app (app (church n) (var 1)) (var 0))))) := by
    have := Step.beta (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))
      (church n)
    simp [subst, shift_church] at this
    exact this
  -- Step 2, inside: `church n 1` becomes `λ. iterApp 2 n`.
  have h2 : Step (app (app (church n) (var 1)) (var 0))
      (app (lam (iterApp 2 n)) (var 0)) := by
    have := Step.appL (var 0) (Step.beta (lam (iterApp 1 n)) (var 1))
    simp [subst, shift, subst_iterApp_f] at this
    exact this
  -- Step 3: `(λ. iterApp 2 n) 0` becomes `iterApp 1 n`.
  have h3 : Step (app (lam (iterApp 2 n)) (var 0)) (iterApp 1 n) := by
    have := Step.beta (iterApp 2 n) (var 0)
    rwa [subst_iterApp_x] at this
  -- Steps 2 and 3 happen under two binders, in the argument of `1`.
  have h23 : Steps (app (app (church n) (var 1)) (var 0)) (iterApp 1 n) :=
    Relation.ReflTransGen.head h2 (Relation.ReflTransGen.single h3)
  -- `church (n + 1)` is, by definition, `λ. λ. 1 (iterApp 1 n)`.
  exact Relation.ReflTransGen.head h1 (steps_body (steps_body (steps_appR _ h23)))
-- ANCHOR_END: succ_correct

-- ANCHOR: no_fuel
/--
error: fail to show termination for
  Ch07.normalizeAll
with errors
failed to infer structural recursion:
Cannot use parameter t:
  failed to eliminate recursive application
    normalizeAll t'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
t t' : Term
⊢ sizeOf t' < sizeOf t
-/
#guard_msgs in
def normalizeAll (t : Term) : Term :=
  match step t with
  | none => t
  | some t' => normalizeAll t'
-- ANCHOR_END: no_fuel

-- ANCHOR: partial
/-- The same function, marked `partial`: Lean accepts it without a termination
proof, compiles it, and lets us run it. -/
partial def normalizeAll' (t : Term) : Term :=
  match step t with
  | none => t
  | some t' => normalizeAll' t'

/-- info: λ. λ. 1 (1 (1 (1 (1 (1 0))))) -/
#guard_msgs in
#eval normalizeAll' (app (app times (church 2)) (church 3))
-- ANCHOR_END: partial

-- ANCHOR: partial_opaque
/--
error: Tactic `rfl` failed: The left-hand side
  normalizeAll' (var 0)
is not definitionally equal to the right-hand side
  var 0

⊢ normalizeAll' (var 0) = var 0
-/
#guard_msgs in
example : normalizeAll' (var 0) = var 0 := by
  rfl
-- ANCHOR_END: partial_opaque

end Ch07
