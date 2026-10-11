import Book.Ch32.Language

/-!
# Chapter 32 · Semantic types: a logical relation

Every type of the language of `Book.Ch32.Language` is interpreted as a
predicate on values (`V`), and a term is *semantically* well typed when it
runs to a value that satisfies the predicate of its type (`SemTyped`). The
fundamental theorem says that the syntactic rules are sound for this
interpretation. Semantic typing is more generous than the syntactic rules: it
accepts the library `satSub`, which uses the unchecked primitive `subRaw` in a
safe way, and rejects `badSub`, which does not. Finally, a verified library can
be linked with any client that type-checks against the library's signature.
-/

namespace Ch32

/-! ## The interpretation of types -/

-- ANCHOR: V
/-- `V τ v`: the value `v` is a good value of type `τ`. -/
def V : Ty → Val → Prop
  | .nat, v => ∃ n, v = .nat n
  | .bool, v => ∃ b, v = .bool b
  | .arr σ τ, v =>
    ∃ ρ body, v = .clo ρ body ∧
      ∀ w, V σ w → ∃ r, Eval (w :: ρ) body r ∧ V τ r
-- ANCHOR_END: V

-- ANCHOR: E
/-- `E τ ρ e`: in the environment `ρ`, the term `e` runs to a good value of
type `τ`. -/
def E (τ : Ty) (ρ : List Val) (e : Expr) : Prop :=
  ∃ v, Eval ρ e v ∧ V τ v
-- ANCHOR_END: E

-- ANCHOR: G
/-- `G Γ ρ`: the environment `ρ` gives every variable of `Γ` a good value of
its type. -/
def G : List Ty → List Val → Prop
  | [], [] => True
  | τ :: Γ, v :: ρ => V τ v ∧ G Γ ρ
  | _, _ => False

/-- Semantic typing, written `Γ ⊨ e : τ` in the text: in every environment that
fits `Γ`, the term `e` runs to a good value of type `τ`. -/
def SemTyped (Γ : List Ty) (e : Expr) (τ : Ty) : Prop :=
  ∀ ρ, G Γ ρ → E τ ρ e
-- ANCHOR_END: G

/-! ## A first example: semantically typed, syntactically not -/

-- ANCHOR: mixed
/-- `if true then 1 else false`. -/
def mixed : Expr := .ite (.bool true) (.nat 1) (.bool false)

/-- No derivation exists: rule `ite` would need both branches at type `nat`. -/
theorem mixed_not_typed : ¬ HasType [] mixed .nat := by
  intro h
  cases h with
  | ite _ _ hf => cases hf

/-- But the term does run to a number. -/
theorem mixed_sem : SemTyped [] mixed .nat := by
  intro ρ _
  exact ⟨.nat 1, .iteTrue .bool .nat, 1, rfl⟩
-- ANCHOR_END: mixed

/-! ## Compatibility lemmas: one per typing rule -/

-- ANCHOR: G_lookup
/-- A good environment has a good value at every position the context types. -/
theorem G_lookup : ∀ {Γ : List Ty} {ρ : List Val} {i : ℕ} {τ : Ty},
    G Γ ρ → Γ[i]? = some τ → ∃ v, ρ[i]? = some v ∧ V τ v
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, hG, _ => by simp [G] at hG
  | _ :: _, v :: _, 0, _, hG, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨v, rfl, hG.1⟩
  | _ :: _, _ :: _, _ + 1, _, hG, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact G_lookup hG.2 h
-- ANCHOR_END: G_lookup

-- ANCHOR: compat_var
theorem compat_var {Γ i τ} (h : Γ[i]? = some τ) : SemTyped Γ (.var i) τ := by
  intro ρ hG
  obtain ⟨v, hv, hV⟩ := G_lookup hG h
  exact ⟨v, .var hv, hV⟩
-- ANCHOR_END: compat_var

-- ANCHOR: compat_consts
theorem compat_nat {Γ n} : SemTyped Γ (.nat n) .nat :=
  fun _ _ => ⟨.nat n, .nat, n, rfl⟩

theorem compat_bool {Γ b} : SemTyped Γ (.bool b) .bool :=
  fun _ _ => ⟨.bool b, .bool, b, rfl⟩
-- ANCHOR_END: compat_consts

-- ANCHOR: compat_add
theorem compat_add {Γ e₁ e₂} (h₁ : SemTyped Γ e₁ .nat)
    (h₂ : SemTyped Γ e₂ .nat) : SemTyped Γ (.add e₁ e₂) .nat := by
  intro ρ hG
  obtain ⟨_, ev₁, n₁, rfl⟩ := h₁ ρ hG
  obtain ⟨_, ev₂, n₂, rfl⟩ := h₂ ρ hG
  exact ⟨.nat (n₁ + n₂), .add ev₁ ev₂, n₁ + n₂, rfl⟩
-- ANCHOR_END: compat_add

theorem compat_le {Γ e₁ e₂} (h₁ : SemTyped Γ e₁ .nat)
    (h₂ : SemTyped Γ e₂ .nat) : SemTyped Γ (.le e₁ e₂) .bool := by
  intro ρ hG
  obtain ⟨_, ev₁, n₁, rfl⟩ := h₁ ρ hG
  obtain ⟨_, ev₂, n₂, rfl⟩ := h₂ ρ hG
  exact ⟨.bool (decide (n₁ ≤ n₂)), .le ev₁ ev₂, _, rfl⟩

-- ANCHOR: compat_ite
theorem compat_ite {Γ c t f τ} (hc : SemTyped Γ c .bool)
    (ht : SemTyped Γ t τ) (hf : SemTyped Γ f τ) :
    SemTyped Γ (.ite c t f) τ := by
  intro ρ hG
  obtain ⟨_, evc, b, rfl⟩ := hc ρ hG
  cases b with
  | true =>
    obtain ⟨v, ev, hv⟩ := ht ρ hG
    exact ⟨v, .iteTrue evc ev, hv⟩
  | false =>
    obtain ⟨v, ev, hv⟩ := hf ρ hG
    exact ⟨v, .iteFalse evc ev, hv⟩
-- ANCHOR_END: compat_ite

-- ANCHOR: compat_lam
theorem compat_lam {Γ body σ τ} (h : SemTyped (σ :: Γ) body τ) :
    SemTyped Γ (.lam body) (.arr σ τ) := by
  intro ρ hG
  refine ⟨.clo ρ body, .lam, ρ, body, rfl, ?_⟩
  intro w hw
  exact h (w :: ρ) ⟨hw, hG⟩
-- ANCHOR_END: compat_lam

-- ANCHOR: compat_app
theorem compat_app {Γ f a σ τ} (hf : SemTyped Γ f (.arr σ τ))
    (ha : SemTyped Γ a σ) : SemTyped Γ (.app f a) τ := by
  intro ρ hG
  obtain ⟨_, evf, ρ', body, rfl, hbody⟩ := hf ρ hG
  obtain ⟨w, eva, hw⟩ := ha ρ hG
  obtain ⟨r, evr, hr⟩ := hbody w hw
  exact ⟨r, .app evf eva evr, hr⟩
-- ANCHOR_END: compat_app

/-! ## The fundamental theorem -/

-- ANCHOR: fundamental
/-- Every syntactically well-typed term is semantically well typed. -/
theorem fundamental {Γ e τ} (h : HasType Γ e τ) : SemTyped Γ e τ := by
  induction h with
  | var h => exact compat_var h
  | nat => exact compat_nat
  | bool => exact compat_bool
  | add _ _ ih₁ ih₂ => exact compat_add ih₁ ih₂
  | le _ _ ih₁ ih₂ => exact compat_le ih₁ ih₂
  | ite _ _ _ ihc iht ihf => exact compat_ite ihc iht ihf
  | lam _ ih => exact compat_lam ih
  | app _ _ ihf iha => exact compat_app ihf iha
-- ANCHOR_END: fundamental

-- ANCHOR: safety
/-- Type safety as a corollary: a closed well-typed term runs to a value of
its type. It never gets stuck (and, in this language, it always finishes). -/
theorem safety {e τ} (h : HasType [] e τ) : ∃ v, Eval [] e v ∧ V τ v :=
  fundamental h [] trivial
-- ANCHOR_END: safety

/-! ## Verifying a library that uses the unchecked primitive -/

-- ANCHOR: satSub_not_typed
/-- `satSub` has no syntactic type at all: its body uses `subRaw`. -/
theorem satSub_not_typed (τ : Ty) : ¬ HasType [] satSub τ := by
  intro h
  cases h with
  | lam h =>
    cases h with
    | lam h =>
      cases h with
      | ite _ ht _ => cases ht
-- ANCHOR_END: satSub_not_typed

-- ANCHOR: eval_le
/-- The comparison `var 0 ≤ var 1` in an environment that starts with two
numbers `y` and `x`. -/
theorem eval_le_vars {y x : ℕ} {ρ : List Val} :
    Eval (.nat y :: .nat x :: ρ) (.le (.var 0) (.var 1)) (.bool (decide (y ≤ x))) :=
  .le (.var rfl) (.var rfl)
-- ANCHOR_END: eval_le

-- ANCHOR: satSub_sem
/-- The proof obligation of the library, discharged once and for all:
`satSub` is a good function from two numbers to a number. -/
theorem satSub_sem : SemTyped [] satSub (.arr .nat (.arr .nat .nat)) := by
  intro ρ _
  -- `satSub` evaluates to a closure; we must show it maps numbers to good
  -- functions from numbers to numbers.
  refine ⟨_, .lam, ρ, _, rfl, ?_⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨_, .lam, _, _, rfl, ?_⟩
  rintro _ ⟨y, rfl⟩
  -- The body `if y ≤ x then subRaw x y else 0` runs in `[y, x] ++ ρ`.
  by_cases hyx : y ≤ x
  · -- The `then` branch: `hyx` is exactly the precondition of `subRaw`.
    have hc := eval_le_vars (ρ := ρ) (y := y) (x := x)
    rw [decide_eq_true hyx] at hc
    exact ⟨.nat (x - y), .iteTrue hc (.subRaw (.var rfl) (.var rfl) hyx), _, rfl⟩
  · -- The `else` branch never calls the primitive.
    have hc := eval_le_vars (ρ := ρ) (y := y) (x := x)
    rw [decide_eq_false hyx] at hc
    exact ⟨.nat 0, .iteFalse hc .nat, 0, rfl⟩
-- ANCHOR_END: satSub_sem

-- ANCHOR: badSub_not_sem
/-- The careless library is not semantically well typed: called with `3` and
`5`, its body is stuck. -/
theorem badSub_not_sem : ¬ SemTyped [] badSub (.arr .nat (.arr .nat .nat)) := by
  intro h
  -- Run `badSub` in the empty environment: it must give a good closure.
  obtain ⟨_, ev, _, _, rfl, hf⟩ := h [] trivial
  cases ev
  -- Apply it to `3`: the result must be a good closure again.
  obtain ⟨_, ev₃, _, _, rfl, hg⟩ := hf (.nat 3) ⟨3, rfl⟩
  cases ev₃
  -- Apply that to `5`: the body `subRaw x y` must run to a value.
  obtain ⟨_, ev₅, _⟩ := hg (.nat 5) ⟨5, rfl⟩
  -- The only rule for `subRaw` needs `5 ≤ 3`.
  cases ev₅ with
  | subRaw ev₁ ev₂ hle =>
    cases ev₁ with
    | var h₁ =>
      cases ev₂ with
      | var h₂ =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Val.nat.injEq] at h₁ h₂
        omega
-- ANCHOR_END: badSub_not_sem

/-! ## Linking a verified library with type-checked clients -/

-- ANCHOR: link
/-- If a library is semantically well typed at `σ`, and a client type-checks
with one variable of type `σ` (the library's signature, nothing more), then
the linked program `(fun lib => client) library` runs to a good value. -/
theorem link {lib c : Expr} {σ τ : Ty}
    (hlib : SemTyped [] lib σ) (hc : HasType [σ] c τ) :
    ∃ v, Eval [] (.app (.lam c) lib) v ∧ V τ v := by
  obtain ⟨w, evw, hw⟩ := hlib [] trivial
  obtain ⟨v, evv, hv⟩ := fundamental hc [w] ⟨hw, trivial⟩
  exact ⟨v, .app .lam evw evv, hv⟩
-- ANCHOR_END: link

-- ANCHOR: client
/-- A client that only knows `sub : nat → nat → nat` (it is `var 0`):
`sub (sub 10 3) 4`. -/
def client : Expr :=
  .app (.app (.var 0) (.app (.app (.var 0) (.nat 10)) (.nat 3))) (.nat 4)

theorem client_typed : HasType [.arr .nat (.arr .nat .nat)] client .nat :=
  .app (.app (.var rfl) (.app (.app (.var rfl) .nat) .nat)) .nat

/-- The linked program is safe, with no further proof about `satSub`. -/
theorem client_safe : ∃ v, Eval [] (.app (.lam client) satSub) v ∧ V .nat v :=
  link satSub_sem client_typed

/-- info: Ch32.Outcome.value (Ch32.Val.nat 3) -/
#guard_msgs in
#eval run 20 [] (.app (.lam client) satSub)
-- ANCHOR_END: client

end Ch32
