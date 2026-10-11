import Book.Ch06.Structural

/-!
# Chapter 6 · Counting how often an assumption is used

Derivations as data (`Deriv`, in `Type`), so that we can compute with them.
Hypotheses are referred to by position (`Var`). The three structural rules
become *renamings* of positions, and we prove how each of them changes the
number of times an assumption is used: weakening adds an assumption used zero
times, contraction adds up the uses of two assumptions, exchange swaps them.
-/

namespace Ch06

open Formula

-- ANCHOR: var
/-- `Var Γ A`: a position in the context `Γ` at which the formula `A` sits.
`here` is the first position, `there x` is one step further than `x`. -/
inductive Var : List Formula → Formula → Type where
  | here {Γ A} : Var (A :: Γ) A
  | there {Γ A B} : Var Γ A → Var (B :: Γ) A

/-- The position as a number: `here` is `0`, `there here` is `1`, and so on. -/
def Var.idx {Γ A} : Var Γ A → ℕ
  | .here => 0
  | .there x => x.idx + 1
-- ANCHOR_END: var

-- ANCHOR: deriv
/-- Derivations as data: the same rules as `Proves`, but a derivation is a
tree that we can inspect, and a hypothesis leaf records *which* position of
the context it uses. -/
inductive Deriv : List Formula → Formula → Type where
  | hyp {Γ A} : Var Γ A → Deriv Γ A
  | topI {Γ} : Deriv Γ top
  | botE {Γ C} : Deriv Γ bot → Deriv Γ C
  | conjI {Γ A B} : Deriv Γ A → Deriv Γ B → Deriv Γ (conj A B)
  | conjE₁ {Γ A B} : Deriv Γ (conj A B) → Deriv Γ A
  | conjE₂ {Γ A B} : Deriv Γ (conj A B) → Deriv Γ B
  | disjI₁ {Γ A B} : Deriv Γ A → Deriv Γ (disj A B)
  | disjI₂ {Γ A B} : Deriv Γ B → Deriv Γ (disj A B)
  | disjE {Γ A B C} :
      Deriv Γ (disj A B) → Deriv (A :: Γ) C → Deriv (B :: Γ) C → Deriv Γ C
  | impI {Γ A B} : Deriv (A :: Γ) B → Deriv Γ (imp A B)
  | impE {Γ A B} : Deriv Γ (imp A B) → Deriv Γ A → Deriv Γ B
-- ANCHOR_END: deriv

-- ANCHOR: to_proves
/-- A position holds a member of the context. -/
theorem Var.mem {Γ A} : Var Γ A → A ∈ Γ
  | .here => List.mem_cons_self
  | .there x => List.mem_cons_of_mem _ x.mem

/-- Forgetting the tree: every `Deriv` gives a `Proves`. -/
theorem Deriv.toProves {Γ C} : Deriv Γ C → Proves Γ C
  | .hyp x => .hyp x.mem
  | .topI => .topI
  | .botE d => .botE d.toProves
  | .conjI d e => .conjI d.toProves e.toProves
  | .conjE₁ d => .conjE₁ d.toProves
  | .conjE₂ d => .conjE₂ d.toProves
  | .disjI₁ d => .disjI₁ d.toProves
  | .disjI₂ d => .disjI₂ d.toProves
  | .disjE d e f => .disjE d.toProves e.toProves f.toProves
  | .impI d => .impI d.toProves
  | .impE d e => .impE d.toProves e.toProves
-- ANCHOR_END: to_proves

-- ANCHOR: proves_iff
/-- Every member of a context has a position. -/
theorem Var.of_mem {Γ A} (h : A ∈ Γ) : Nonempty (Var Γ A) := by
  induction h with
  | head => exact ⟨.here⟩
  | tail _ _ ih => exact ih.map .there

/-- `Proves Γ C` says exactly that a derivation tree exists. -/
theorem proves_iff_nonempty {Γ C} : Proves Γ C ↔ Nonempty (Deriv Γ C) := by
  constructor
  · intro h
    induction h with
    | hyp mem => exact (Var.of_mem mem).map .hyp
    | topI => exact ⟨.topI⟩
    | botE _ ih => exact ih.map .botE
    | conjI _ _ ih₁ ih₂ => exact ih₁.elim fun d => ih₂.map (.conjI d)
    | conjE₁ _ ih => exact ih.map .conjE₁
    | conjE₂ _ ih => exact ih.map .conjE₂
    | disjI₁ _ ih => exact ih.map .disjI₁
    | disjI₂ _ ih => exact ih.map .disjI₂
    | disjE _ _ _ ih ihA ihB =>
      exact ih.elim fun d => ihA.elim fun e => ihB.map (.disjE d e)
    | impI _ ih => exact ih.map .impI
    | impE _ _ ih₁ ih₂ => exact ih₁.elim fun d => ih₂.map (.impE d)
  · intro ⟨d⟩
    exact d.toProves
-- ANCHOR_END: proves_iff

-- ANCHOR: renaming
/-- A renaming sends each position of `Γ` to a position of `Δ` that holds the
same formula. -/
abbrev Renaming (Γ Δ : List Formula) : Type := ∀ A, Var Γ A → Var Δ A

/-- Under a binder both contexts grow by the same formula `B`, which is sent
to itself. -/
def Renaming.lift {Γ Δ B} (ρ : Renaming Γ Δ) : Renaming (B :: Γ) (B :: Δ)
  | _, .here => .here
  | _, .there x => .there (ρ _ x)

/-- Renaming a derivation: replace every hypothesis leaf `hyp x` by
`hyp (ρ x)`. The shape of the tree does not change. -/
def Deriv.rename {Γ Δ C} (ρ : Renaming Γ Δ) : Deriv Γ C → Deriv Δ C
  | .hyp x => .hyp (ρ _ x)
  | .topI => .topI
  | .botE d => .botE (d.rename ρ)
  | .conjI d e => .conjI (d.rename ρ) (e.rename ρ)
  | .conjE₁ d => .conjE₁ (d.rename ρ)
  | .conjE₂ d => .conjE₂ (d.rename ρ)
  | .disjI₁ d => .disjI₁ (d.rename ρ)
  | .disjI₂ d => .disjI₂ (d.rename ρ)
  | .disjE d e f => .disjE (d.rename ρ) (e.rename ρ.lift) (f.rename ρ.lift)
  | .impI d => .impI (d.rename ρ.lift)
  | .impE d e => .impE (d.rename ρ) (e.rename ρ)
-- ANCHOR_END: renaming

section Rules

variable {Γ : List Formula} {A B C : Formula}

-- ANCHOR: structural_renamings
/-- Weakening: every old position moves one step to make room for `B`. -/
def Deriv.weaken (d : Deriv Γ C) : Deriv (B :: Γ) C :=
  d.rename (fun _ x => .there x)

/-- Exchange: positions `0` and `1` swap, the others stay. -/
def swapFirstTwo : Renaming (A :: B :: Γ) (B :: A :: Γ)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there x) => .there (.there x)

def Deriv.exchange (d : Deriv (A :: B :: Γ) C) : Deriv (B :: A :: Γ) C :=
  d.rename swapFirstTwo

/-- Contraction: positions `0` and `1` both go to `0`, the others move down. -/
def mergeFirstTwo : Renaming (A :: A :: Γ) (A :: Γ)
  | _, .here => .here
  | _, .there .here => .here
  | _, .there (.there x) => .there x

def Deriv.contract (d : Deriv (A :: A :: Γ) C) : Deriv (A :: Γ) C :=
  d.rename mergeFirstTwo
-- ANCHOR_END: structural_renamings

end Rules

-- ANCHOR: uses
/-- A selection of positions of `Γ`: `true` for the positions we count. -/
abbrev Sel (Γ : List Formula) : Type := ∀ A, Var Γ A → Bool

/-- Under a binder the new position `0` is not selected; the old ones keep
their selection, one step further. -/
def Sel.lift {Γ B} (s : Sel Γ) : Sel (B :: Γ)
  | _, .here => false
  | _, .there x => s _ x

/-- The number of hypothesis leaves of `d` that use a selected position. -/
def Deriv.uses {Γ C} : Deriv Γ C → Sel Γ → ℕ
  | .hyp x, s => if s _ x then 1 else 0
  | .topI, _ => 0
  | .botE d, s => d.uses s
  | .conjI d e, s => d.uses s + e.uses s
  | .conjE₁ d, s => d.uses s
  | .conjE₂ d, s => d.uses s
  | .disjI₁ d, s => d.uses s
  | .disjI₂ d, s => d.uses s
  | .disjE d e f, s => d.uses s + e.uses s.lift + f.uses s.lift
  | .impI d, s => d.uses s.lift
  | .impE d e, s => d.uses s + e.uses s

/-- How many times `d` uses the hypothesis at position `i`. -/
def Deriv.count {Γ C} (d : Deriv Γ C) (i : ℕ) : ℕ :=
  d.uses (fun _ x => x.idx == i)

/-- The usage of every hypothesis, in context order. -/
def Deriv.usage {Γ C} (d : Deriv Γ C) : List ℕ :=
  (List.range Γ.length).map d.count
-- ANCHOR_END: uses

section Examples

-- ANCHOR: usage_examples
def A : Formula := atom "A"
def B : Formula := atom "B"

/-- `A ∧ B ⊢ B ∧ A`, as in `Structural.lean`, now as data. -/
def swapD : Deriv [conj A B] (conj B A) :=
  .conjI (.conjE₂ (.hyp .here)) (.conjE₁ (.hyp .here))

/-- `A, B ⊢ A`. -/
def firstD : Deriv [A, B] A := .hyp .here

/-- `A → B, A ⊢ B` (modus ponens). -/
def mpD : Deriv [imp A B, A] B := .impE (.hyp .here) (.hyp (.there .here))

/-- `A ⊢ A ∧ A`. -/
def dupD : Deriv [A] (conj A A) := .conjI (.hyp .here) (.hyp .here)

/-- info: [2] -/
#guard_msgs in
#eval swapD.usage

/-- info: [1, 0] -/
#guard_msgs in
#eval firstD.usage

/-- info: [1, 1] -/
#guard_msgs in
#eval mpD.usage

/-- info: [2] -/
#guard_msgs in
#eval dupD.usage
-- ANCHOR_END: usage_examples

-- ANCHOR: disciplines
/-- Every hypothesis is used at most once. -/
def Deriv.affine {Γ C} (d : Deriv Γ C) : Bool := d.usage.all (· ≤ 1)
/-- Every hypothesis is used at least once. -/
def Deriv.relevant {Γ C} (d : Deriv Γ C) : Bool := d.usage.all (1 ≤ ·)
/-- Every hypothesis is used exactly once. -/
def Deriv.linear {Γ C} (d : Deriv Γ C) : Bool := d.usage.all (· == 1)

/-- The most specific of the three disciplines that a derivation follows. -/
def Deriv.discipline {Γ C} (d : Deriv Γ C) : String :=
  if d.linear then "linear"
  else if d.affine then "affine"
  else if d.relevant then "relevant"
  else "unrestricted"

/-- info: ["relevant", "affine", "linear", "relevant"] -/
#guard_msgs in
#eval [swapD.discipline, firstD.discipline, mpD.discipline, dupD.discipline]
-- ANCHOR_END: disciplines

-- ANCHOR: usage_structural
/-- `A, A ⊢ A ∧ A`, each copy used once. -/
def twoCopiesD : Deriv [A, A] (conj A A) := .conjI (.hyp .here) (.hyp (.there .here))

/-- info: [1, 1] -/
#guard_msgs in
#eval twoCopiesD.usage

/-- info: [2] -/
#guard_msgs in
#eval twoCopiesD.contract.usage

/-- info: [0, 1, 1] -/
#guard_msgs in
#eval (twoCopiesD.weaken (B := B)).usage

/-- info: [1, 1] -/
#guard_msgs in
#eval mpD.exchange.usage
-- ANCHOR_END: usage_structural

end Examples

section Theorems

variable {Γ Δ : List Formula} {A B C : Formula}

-- ANCHOR: lift_lemmas
/-- Lifting commutes with renaming, with "nothing" and with `||` and `&&`.
Each proof looks at the two kinds of positions, `here` and `there x`. -/
theorem Sel.lift_rename (ρ : Renaming Γ Δ) (s : Sel Δ) :
    (fun X (x : Var (B :: Γ) X) => s.lift X (ρ.lift X x)) =
      Sel.lift (fun X x => s X (ρ X x)) := by
  funext _ x; cases x <;> rfl

theorem Sel.lift_none :
    Sel.lift (B := B) (fun _ _ => false : Sel Γ) = fun _ _ => false := by
  funext _ x; cases x <;> rfl

theorem Sel.lift_or (s t : Sel Γ) :
    Sel.lift (B := B) (fun X x => s X x || t X x) =
      fun X x => s.lift X x || t.lift X x := by
  funext _ x; cases x <;> rfl

theorem Sel.lift_and (s t : Sel Γ) :
    Sel.lift (B := B) (fun X x => s X x && t X x) =
      fun X x => s.lift X x && t.lift X x := by
  funext _ x; cases x <;> rfl
-- ANCHOR_END: lift_lemmas

-- ANCHOR: uses_rename
/-- The key lemma: counting the selected uses in a renamed derivation is the
same as counting, in the original derivation, the positions whose image is
selected. -/
theorem Deriv.uses_rename (d : Deriv Γ C) (ρ : Renaming Γ Δ) (s : Sel Δ) :
    (d.rename ρ).uses s = d.uses (fun X x => s X (ρ X x)) := by
  induction d generalizing Δ with
  | hyp x => rfl
  | topI => rfl
  | botE d ih => exact ih ρ s
  | conjI d e ihd ihe => simp only [rename, uses, ihd, ihe]
  | conjE₁ d ih => exact ih ρ s
  | conjE₂ d ih => exact ih ρ s
  | disjI₁ d ih => exact ih ρ s
  | disjI₂ d ih => exact ih ρ s
  | disjE d e f ihd ihe ihf =>
    simp only [rename, uses, ihd, ihe, ihf, Sel.lift_rename]
  | impI d ih =>
    simp only [rename, uses, ih, Sel.lift_rename]
  | impE d e ihd ihe => simp only [rename, uses, ihd, ihe]
-- ANCHOR_END: uses_rename

-- ANCHOR: uses_lemmas
/-- Selecting nothing counts nothing. -/
theorem Deriv.uses_none (d : Deriv Γ C) : d.uses (fun _ _ => false) = 0 := by
  induction d with
  | hyp x => rfl
  | topI => rfl
  | botE _ ih => exact ih
  | conjI _ _ ihd ihe => simp only [uses, ihd, ihe]
  | conjE₁ _ ih => exact ih
  | conjE₂ _ ih => exact ih
  | disjI₁ _ ih => exact ih
  | disjI₂ _ ih => exact ih
  | disjE _ _ _ ihd ihe ihf => simp only [uses, Sel.lift_none, ihd, ihe, ihf]
  | impI _ ih => simp only [uses, Sel.lift_none, ih]
  | impE _ _ ihd ihe => simp only [uses, ihd, ihe]

/-- Counting the union of two selections plus their intersection is the same
as counting each of them. -/
theorem Deriv.uses_or (d : Deriv Γ C) (s t : Sel Γ) :
    d.uses (fun X x => s X x || t X x) + d.uses (fun X x => s X x && t X x) =
      d.uses s + d.uses t := by
  induction d with
  | hyp x =>
    -- One leaf: check the four combinations of `s x` and `t x`.
    simp only [uses]
    by_cases hs : s _ x <;> by_cases ht : t _ x <;> simp [hs, ht]
  | topI => rfl
  | botE _ ih => exact ih s t
  | conjI _ _ ihd ihe =>
    simp only [uses]
    have := ihd s t
    have := ihe s t
    omega
  | conjE₁ _ ih => exact ih s t
  | conjE₂ _ ih => exact ih s t
  | disjI₁ _ ih => exact ih s t
  | disjI₂ _ ih => exact ih s t
  | disjE _ _ _ ihd ihe ihf =>
    simp only [uses, Sel.lift_or, Sel.lift_and]
    have := ihd s t
    have := ihe s.lift t.lift
    have := ihf s.lift t.lift
    omega
  | impI _ ih =>
    simp only [uses, Sel.lift_or, Sel.lift_and]
    exact ih s.lift t.lift
  | impE _ _ ihd ihe =>
    simp only [uses]
    have := ihd s t
    have := ihe s t
    omega
-- ANCHOR_END: uses_lemmas

-- ANCHOR: count_weaken
/-- Weakening adds a hypothesis that is used zero times... -/
theorem count_weaken (d : Deriv Γ C) : (d.weaken (B := B)).count 0 = 0 := by
  unfold Deriv.count Deriv.weaken
  rw [Deriv.uses_rename]
  -- The selection is now `fun X x => (x.idx + 1 == 0)`: always false.
  have hsel : (fun X (x : Var Γ X) => (Var.idx (Var.there (B := B) x) == 0)) =
      fun _ _ => false := by
    funext _ x; simp [Var.idx]
  rw [hsel, Deriv.uses_none]

/-- ...and leaves the uses of the old hypotheses unchanged. -/
theorem count_weaken_succ (d : Deriv Γ C) (i : ℕ) :
    (d.weaken (B := B)).count (i + 1) = d.count i := by
  unfold Deriv.count Deriv.weaken
  rw [Deriv.uses_rename]
  simp [Var.idx]
-- ANCHOR_END: count_weaken

-- ANCHOR: count_contract
/-- Contraction adds up the uses of the two merged hypotheses. -/
theorem count_contract (d : Deriv (A :: A :: Γ) C) :
    d.contract.count 0 = d.count 0 + d.count 1 := by
  unfold Deriv.contract Deriv.count
  rw [Deriv.uses_rename, ← Deriv.uses_or]
  -- A position goes to 0 exactly when it is 0 or 1 (and it is never both).
  have hor : (fun X (x : Var (A :: A :: Γ) X) => ((mergeFirstTwo X x).idx == 0)) =
      fun _ x => (x.idx == 0 || x.idx == 1) := by
    funext _ x
    rcases x with _ | _ | x <;> simp [mergeFirstTwo, Var.idx]
  have hand : (fun X (x : Var (A :: A :: Γ) X) => (x.idx == 0 && x.idx == 1)) =
      fun _ _ => false := by
    funext _ x
    cases x.idx <;> simp
  rw [hor, hand, Deriv.uses_none, Nat.add_zero]
-- ANCHOR_END: count_contract

-- ANCHOR: count_exchange
/-- Exchange swaps the uses of the first two hypotheses. -/
theorem count_exchange (d : Deriv (A :: B :: Γ) C) :
    d.exchange.count 0 = d.count 1 ∧ d.exchange.count 1 = d.count 0 := by
  unfold Deriv.exchange Deriv.count
  rw [Deriv.uses_rename, Deriv.uses_rename]
  constructor
  · congr 1
    funext _ x
    rcases x with _ | _ | x <;> simp [swapFirstTwo, Var.idx]
  · congr 1
    funext _ x
    rcases x with _ | _ | x <;> simp [swapFirstTwo, Var.idx]
-- ANCHOR_END: count_exchange

end Theorems

end Ch06
