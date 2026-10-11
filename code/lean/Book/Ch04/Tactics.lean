/-!
# Chapter 4 · Natural deduction in Lean (shallow embedding)

Propositions are Lean types of sort `Prop`, and proofs are terms of those
types. This file shows the rules of natural deduction twice: as the functions
and constructors that Lean's core library provides (`And.intro`, `Or.elim`,
`False.elim`, ...), and as the tactics that apply them (`intro`, `exact`,
`apply`, `constructor`, `cases`, `rcases`, `obtain`, `left`, `right`,
`exfalso`, `contradiction`). It ends with `#print`, which shows the proof term
that a tactic script builds.
-/

namespace Ch04

-- ANCHOR: props
/-- info: True : Prop -/
#guard_msgs in
#check True

/-- info: 2 + 2 = 4 : Prop -/
#guard_msgs in
#check 2 + 2 = 4

/-- info: 2 + 2 = 5 : Prop -/
#guard_msgs in
#check 2 + 2 = 5

/-- info: ∀ (p q : Prop), p ∧ q → q ∧ p : Prop -/
#guard_msgs in
#check ∀ (p q : Prop), p ∧ q → q ∧ p
-- ANCHOR_END: props

-- ANCHOR: rules
/-- info: @And.intro : ∀ {a b : Prop}, a → b → a ∧ b -/
#guard_msgs in
#check @And.intro

/-- info: @And.left : ∀ {a b : Prop}, a ∧ b → a -/
#guard_msgs in
#check @And.left

/-- info: @Or.inl : ∀ {a b : Prop}, a → a ∨ b -/
#guard_msgs in
#check @Or.inl

/-- info: @Or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c -/
#guard_msgs in
#check @Or.elim

/-- info: True.intro : True -/
#guard_msgs in
#check True.intro

/-- info: @False.elim : {C : Sort u_1} → False → C -/
#guard_msgs in
#check @False.elim
-- ANCHOR_END: rules

-- ANCHOR: not
/--
info: @[implicit_reducible] def Not : Prop → Prop :=
fun a => a → False
-/
#guard_msgs in
#print Not
-- ANCHOR_END: not

/-! ## Proofs as terms -/

-- ANCHOR: terms
/-- `∧E₂` and `∧E₁` feed `∧I`: the derivation of `A ∧ B ⊢ B ∧ A`. -/
theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

/-- `→I` is a `fun`, `→E` is application. -/
theorem imp_trans (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  fun hpq hqr hp => hqr (hpq hp)

/-- `∨E`: one branch for each way the disjunction could have been proved. -/
theorem or_swap (p q : Prop) (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-- `⊥E`: from a proof of `False`, anything. -/
theorem explode (p : Prop) (h : False) : p :=
  False.elim h
-- ANCHOR_END: terms

-- ANCHOR: anonymous
/-- The same proofs with Lean's shorthand: `⟨_, _⟩` builds a pair, `.1` and
`.2` project, and `fun ⟨hp, hq⟩ => ...` takes the pair apart. -/
theorem and_swap' (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

theorem and_swap'' (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.2, h.1⟩
-- ANCHOR_END: anonymous

/-! ## Tactics, one rule at a time -/

-- ANCHOR: intro_exact
/-- `intro` is rule →I, read bottom-up: to prove `p → q`, assume `p` (the
assumption gets the name `hp`) and prove `q`. `exact` closes the goal with a
term of exactly the goal's type, here the assumption itself (rule Hyp). -/
theorem identity (p : Prop) : p → p := by
  intro hp      -- goal: p, with hp : p in the context
  exact hp      -- rule Hyp
-- ANCHOR_END: intro_exact

-- ANCHOR: apply
/-- `apply f` is rule →E, read bottom-up: if `f : q → r` and the goal is `r`,
it is enough to prove `q`. -/
theorem imp_trans_tac (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intro hpq hqr hp   -- three uses of →I at once
  apply hqr          -- goal was r; now it is q
  apply hpq          -- goal was q; now it is p
  exact hp
-- ANCHOR_END: apply

-- ANCHOR: constructor
/-- `constructor` applies an introduction rule. For `∧` that is ∧I, and it
leaves one goal per premise. The bullets `·` focus on one goal at a time. -/
theorem and_intro_tac (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp    -- first premise of ∧I
  · exact hq    -- second premise of ∧I
-- ANCHOR_END: constructor

-- ANCHOR: obtain
/-- `obtain ⟨hp, hq⟩ := h` takes a conjunction apart: both eliminations ∧E₁ and
∧E₂ at once. -/
theorem and_swap_tac (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h   -- now hp : p and hq : q
  exact ⟨hq, hp⟩         -- ∧I, written as an anonymous constructor
-- ANCHOR_END: obtain

-- ANCHOR: left_right
/-- `left` and `right` are the two introduction rules ∨I₁ and ∨I₂: they choose
which side of the disjunction we are going to prove. -/
theorem or_intro_tac (p q : Prop) (hq : q) : p ∨ q := by
  right       -- ∨I₂: the goal becomes q
  exact hq
-- ANCHOR_END: left_right

-- ANCHOR: cases
/-- `cases h with` is ∨E: one goal per constructor of `Or`, each with the
assumption that this constructor was used. -/
theorem or_swap_tac (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp =>     -- case 1: h was built by Or.inl, and hp : p
    right
    exact hp
  | inr hq =>     -- case 2: h was built by Or.inr, and hq : q
    left
    exact hq
-- ANCHOR_END: cases

-- ANCHOR: rcases
/-- `rcases` and `rintro` take apart nested conjunctions and disjunctions in
one step: `⟨_, _⟩` splits an `∧`, and `_ | _` splits an `∨` into two goals. -/
theorem and_or_distrib (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  rcases h with ⟨hp, hq | hr⟩
  · left
    exact ⟨hp, hq⟩
  · right
    exact ⟨hp, hr⟩

/-- `rintro` is `intro` followed by `rcases`. -/
theorem and_or_distrib' (p q r : Prop) : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
  rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
  · exact ⟨hp, Or.inl hq⟩
  · exact ⟨hp, Or.inr hr⟩
-- ANCHOR_END: rcases

-- ANCHOR: exfalso
/-- `exfalso` is ⊥E read bottom-up: whatever the goal, replace it by `False`.
Then we prove `False` by →E, applying `hnp : p → False` to `hp : p`. -/
theorem not_or_imp (p q : Prop) : ¬p ∨ q → (p → q) := by
  intro h hp
  rcases h with hnp | hq
  · exfalso       -- goal: False
    exact hnp hp  -- ¬p is p → False, so this is →E
  · exact hq
-- ANCHOR_END: exfalso

-- ANCHOR: contradiction
/-- `contradiction` closes any goal when the context is visibly inconsistent:
it contains `False`, or both `p` and `¬p`. -/
theorem non_contradiction (p q : Prop) (hp : p) (hnp : ¬p) : q := by
  contradiction
-- ANCHOR_END: contradiction

-- ANCHOR: negation
/-- Negation is implication into `False`, so its rules are those of `→`:
`intro` proves a negation, and applying it to a proof eliminates it. -/
theorem contrapositive (p q : Prop) : (p → q) → ¬q → ¬p := by
  intro hpq hnq hp   -- the last intro unfolds ¬p into p → False
  exact hnq (hpq hp)

theorem not_and_not (p : Prop) : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  exact hnp hp
-- ANCHOR_END: negation

-- ANCHOR: curry
/-- Currying: a proof of `p ∧ q → r` and a proof of `p → q → r` can be turned
into each other. `↔` is a structure with two fields, built by `constructor`. -/
theorem curry_iff (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) := by
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · intro h ⟨hp, hq⟩
    exact h hp hq
-- ANCHOR_END: curry

-- ANCHOR: or_map
/-- The walkthrough formula of the chapter, `(A → B) → A ∨ C → B ∨ C`. -/
theorem or_map (p q r : Prop) : (p → q) → p ∨ r → q ∨ r := by
  intro hpq h              -- →I twice
  cases h with             -- ∨E on h : p ∨ r
  | inl hp =>
    left                   -- ∨I1
    exact hpq hp           -- →E
  | inr hr =>
    right                  -- ∨I2
    exact hr
-- ANCHOR_END: or_map

/-! ## The term behind a tactic proof -/

-- ANCHOR: print
/--
info: theorem Ch04.and_swap_tac : ∀ (p q : Prop), p ∧ q → q ∧ p :=
fun p q h => And.casesOn h fun hp hq => ⟨hq, hp⟩
-/
#guard_msgs in
#print and_swap_tac

/--
info: theorem Ch04.imp_trans_tac : ∀ (p q r : Prop), (p → q) → (q → r) → p → r :=
fun p q r hpq hqr hp => hqr (hpq hp)
-/
#guard_msgs in
#print imp_trans_tac
-- ANCHOR_END: print

-- ANCHOR: print_or
/--
info: theorem Ch04.or_swap_tac : ∀ (p q : Prop), p ∨ q → q ∨ p :=
fun p q h => Or.casesOn (motive := fun t => h = t → q ∨ p) h (fun hp h => Or.inr hp) (fun hq h => Or.inl hq) (Eq.refl h)
-/
#guard_msgs in
#print or_swap_tac
-- ANCHOR_END: print_or

-- ANCHOR: wrong
/--
error: Type mismatch
  hp
has type
  p
but is expected to have type
  q
-/
#guard_msgs in
theorem wrong (p q : Prop) : p → q := by
  intro hp
  exact hp
-- ANCHOR_END: wrong

end Ch04
