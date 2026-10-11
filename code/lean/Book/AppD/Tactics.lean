import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# Appendix D · The tactics used in this book

One small, compiled example per tactic, grouped by what the tactic does.
-/

namespace AppD

-- ANCHOR: finishing
-- `rfl`: both sides compute to the same value.
example : 2 + 2 = 4 := by rfl

-- `exact e`: the term `e` has exactly the type of the goal.
example (p : Prop) (hp : p) : p := by exact hp

-- `assumption`: some hypothesis has the type of the goal.
example (p q : Prop) (_hq : q) (hp : p) : p := by assumption

-- `trivial`: closes `True`, and goals that `rfl` or `assumption` close.
example : True := by trivial

-- `contradiction`: the hypotheses are contradictory (here, `False` itself).
example (p : Prop) (h : False) : p := by contradiction

-- `absurd h h'`: `h : p` and `h' : ¬p` prove anything.
example (p q : Prop) (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- `decide`: evaluate a decidable proposition.
example : 7 ∣ 91 := by decide

-- `omega`: linear arithmetic over ℕ and ℤ.
example (a b : ℕ) (h : a < b) : a + 1 ≤ b := by omega

-- `ring`: identities in commutative (semi)rings.
example (x y : ℤ) : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring

-- `linarith`: linear inequalities over ordered fields (and ℕ, ℤ).
example (x y : ℚ) (h₁ : x ≤ 2 * y) (h₂ : y < 3) : x < 6 := by linarith

-- `norm_num`: numeric facts.
example : (2 : ℚ) / 3 + 1 / 3 = 1 := by norm_num

-- `positivity`: goals of the form `0 < e` or `0 ≤ e`.
example (x : ℤ) : 0 ≤ x ^ 2 + 1 := by positivity

-- `tauto`: propositional tautologies (classically).
example (p q : Prop) : p ∧ q → q ∨ p := by tauto
-- ANCHOR_END: finishing

-- ANCHOR: introduction
-- `intro`: the →I and ∀I rules; name the hypothesis or variable.
example (p q : Prop) : p → q → p := by
  intro hp _hq
  exact hp

-- `constructor`: apply the (only) constructor: ∧I, ↔I, building a structure.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- `left` / `right`: ∨I, choosing the side.
example (p q : Prop) (hq : q) : p ∨ q := by
  right
  exact hq

-- `exists` / `use`: ∃I, giving the witness.
example : ∃ n : ℕ, n * n = 49 := by
  exists 7

example : ∃ n : ℕ, n + 3 = 7 := by
  use 4

-- `apply f`: backward reasoning; the remaining premises of `f` become goals.
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  apply hqr
  apply hpq
  exact hp

-- `refine`: like `exact`, with `?_` holes that become new goals.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, hq⟩
  exact hp

-- `exfalso`: replace the goal by `False` (⊥E, read backwards).
example (p : Prop) (h : 1 = 0) : p := by
  exfalso
  omega

-- `funext`: two functions are equal if they agree everywhere.
example : (fun n : ℕ => n + 0) = (fun n => n) := by
  funext n
  rfl
-- ANCHOR_END: introduction

-- ANCHOR: elimination
-- `cases`: one goal per constructor of the hypothesis (∨E, ∧E, ∃E, pattern matching).
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- `obtain` / `rcases`: take a hypothesis apart with a pattern, in one step.
example (p q r : Prop) (h : p ∧ (q ∧ r)) : r := by
  obtain ⟨_hp, _hq, hr⟩ := h
  exact hr

example (n : ℕ) (h : ∃ k, n = 2 * k) : n % 2 = 0 := by
  rcases h with ⟨k, rfl⟩
  omega

-- `rintro`: `intro` followed by `rcases`.
example (p q : Prop) : p ∧ q → q := by
  rintro ⟨_, hq⟩
  exact hq

-- `induction`: structural induction; one goal per constructor, with hypotheses.
theorem sum_formula (n : ℕ) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.sum_append, mul_add, ih]
    simp
    ring

-- `by_cases`: split on whether a proposition holds.
example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by
  by_cases h : n % 2 = 0
  · exact Or.inl h
  · right
    omega

-- `split`: one goal per branch of an `if` or `match` in the goal.
example (n : ℕ) : (if n < 5 then n else 5) ≤ 5 := by
  split
  · omega
  · omega

-- `subst`: replace a variable everywhere using an equation `x = e`.
example (a b : ℕ) (h : a = b + 1) : a - 1 = b := by
  subst h
  omega

-- `nomatch`: a hypothesis with no possible constructor proves anything.
example (h : Nat.succ 3 = 0) : False := nomatch h

-- `injection`: constructors are injective.
example (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  injection h
-- ANCHOR_END: elimination

-- ANCHOR: rewriting
-- `rw [h]`: replace the left side of the equation `h` by its right side.
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  rw [h₁, h₂]

-- `rw [← h]`: rewrite right to left.
example (a b : ℕ) (h : a = b) (p : ℕ → Prop) (hb : p b) : p a := by
  rw [h]
  exact hb

-- `simp`: rewrite with the simp lemmas (and the ones given) until nothing changes.
example (xs : List ℕ) : (xs ++ []).length = xs.length := by simp

-- `simp only [...]`: only the given lemmas and definitions (predictable).
def double (n : ℕ) : ℕ := n + n

example (n : ℕ) : double n = 2 * n := by
  simp only [double]
  omega

-- `simp at h`, `simp_all`: simplify hypotheses too.
example (a : ℕ) (h : a + 0 = 3) : a = 3 := by
  simp at h
  exact h

-- `simpa using e`: simplify the goal and `e`, then close the goal with `e`.
example (a : ℕ) (h : 0 + a = 3) : a = 3 := by simpa using h

-- `unfold`: unfold a definition.
example (n : ℕ) : double n = n + n := by
  unfold double
  rfl

-- `calc`: a chain of steps, each with its own proof.
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 :=
  calc a ≤ b := h₁
    _ < c := h₂
    _ < c + 1 := Nat.lt_succ_self c

-- `symm`, `congr`: symmetry of equality; equal arguments give equal results.
example (a b : ℕ) (h : a = b) : b = a := by
  symm
  exact h

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  congr
-- ANCHOR_END: rewriting

-- ANCHOR: structuring
-- `have`: prove an intermediate fact and add it to the context.
example (a b : ℕ) (h : a < b) : a < b + b := by
  have hb : b ≤ b + b := Nat.le_add_right b b
  omega

-- `show`: state the goal (in a form that is equal by computation).
example (n : ℕ) : double n = n + n := by
  show n + n = n + n
  rfl

-- `case`, `next` and `·`: focus on one goal at a time.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  case left => exact hp
  case right => exact hq

-- `all_goals tac` runs `tac` on every goal; `t₁ <;> t₂` runs `t₂` on every
-- goal that `t₁` produces; `first | t₁ | t₂` tries `t₁`, then `t₂`.
example (p : Prop) (hp : p) : p ∧ p ∧ p := by
  refine ⟨?_, ?_, ?_⟩
  all_goals exact hp

example (n : ℕ) : n + 0 = n ∧ 0 + n = n := by
  constructor <;> simp

example (a b : ℕ) (h : a = b) : b = a := by
  first
  | rfl
  | exact h.symm
-- ANCHOR_END: structuring

-- ANCHOR: recursion
-- `termination_by`: the measure that decreases in every recursive call.
def log2 (n : ℕ) : ℕ :=
  if h : n < 2 then 0 else 1 + log2 (n / 2)
termination_by n
decreasing_by omega

/-- info: 10 -/
#guard_msgs in
#eval log2 1024
-- ANCHOR_END: recursion

end AppD
