/-!
# Chapter 13 · First-order unification

Types with variables, substitutions and their composition (a monoid), the
occurs check and why it is necessary, and a unification algorithm with fuel,
run on the chapter's examples and proved to return unifiers.
-/

namespace Ch13

-- ANCHOR: ty
/-- The types of the chapter's examples: variables, two base types, functions
and lists. -/
inductive Ty where
  | var : Nat → Ty
  | int : Ty
  | bool : Ty
  | arrow : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq

/-- `a ⇒ b` is the function type `Ty.arrow a b`. -/
scoped infixr:25 " ⇒ " => Ty.arrow
-- ANCHOR_END: ty

/-- Prints a type the way the Rust crate does: `?0 → List Int`. -/
def Ty.show : Ty → (prec : Nat := 0) → String
  | .var n, _ => s!"?{n}"
  | .int, _ => "Int"
  | .bool, _ => "Bool"
  | .arrow a b, p =>
    let s := s!"{a.show 1} → {b.show 0}"
    if p > 0 then s!"({s})" else s
  | .list a, p =>
    let s := s!"List {a.show 2}"
    if p > 1 then s!"({s})" else s

instance : Repr Ty where
  reprPrec t _ := .text t.show

-- ANCHOR: subst
/-- A substitution assigns a type to every variable. (The variables it does
not change are mapped to themselves.) -/
def Subst := Nat → Ty

/-- Applying a substitution: replace every variable by its image. -/
def Ty.subst (σ : Subst) : Ty → Ty
  | .var n => σ n
  | .int => .int
  | .bool => .bool
  | .arrow a b => .arrow (a.subst σ) (b.subst σ)
  | .list a => .list (a.subst σ)

/-- The identity substitution changes nothing. -/
def Subst.id : Subst := Ty.var

/-- `τ.comp σ` is "first `σ`, then `τ`": the image of `n` is `σ n` with `τ`
applied to it. -/
def Subst.comp (τ σ : Subst) : Subst := fun n => (σ n).subst τ

/-- The substitution `[x := t]`, which changes only the variable `x`. -/
def Subst.single (x : Nat) (t : Ty) : Subst :=
  fun n => if n = x then t else .var n
-- ANCHOR_END: subst

-- ANCHOR: subst_laws
/-- Applying the identity substitution changes nothing. -/
theorem subst_id (t : Ty) : t.subst Subst.id = t := by
  induction t with
  | var n => rfl
  | int => rfl
  | bool => rfl
  | arrow a b iha ihb => simp [Ty.subst, iha, ihb]
  | list a ih => simp [Ty.subst, ih]

/-- Applying a composition is applying one substitution after the other. -/
theorem subst_comp (τ σ : Subst) (t : Ty) :
    t.subst (τ.comp σ) = (t.subst σ).subst τ := by
  induction t with
  | var n => rfl
  | int => rfl
  | bool => rfl
  | arrow a b iha ihb => simp [Ty.subst, iha, ihb]
  | list a ih => simp [Ty.subst, ih]
-- ANCHOR_END: subst_laws

-- ANCHOR: monoid
/-- Substitutions under composition form a monoid: `id` is a unit on both
sides and composition is associative. -/
theorem Subst.id_comp (σ : Subst) : Subst.id.comp σ = σ := by
  funext n
  exact subst_id (σ n)

theorem Subst.comp_id (σ : Subst) : σ.comp Subst.id = σ := by
  funext n
  rfl

theorem Subst.comp_assoc (ρ τ σ : Subst) :
    (ρ.comp τ).comp σ = ρ.comp (τ.comp σ) := by
  funext n
  exact subst_comp ρ τ (σ n)
-- ANCHOR_END: monoid

-- ANCHOR: occurs
/-- Whether the variable `x` occurs in a type. -/
def Ty.occurs (x : Nat) : Ty → Bool
  | .var n => n == x
  | .int | .bool => false
  | .arrow a b => a.occurs x || b.occurs x
  | .list a => a.occurs x

/-- The size of a type: the number of constructors in it. -/
def Ty.size : Ty → Nat
  | .arrow a b => a.size + b.size + 1
  | .list a => a.size + 1
  | _ => 1
-- ANCHOR_END: occurs

-- ANCHOR: occurs_lemmas
/-- If `x` occurs in `t`, then whatever `σ` puts in place of `x` ends up inside
`t.subst σ`, so it is no bigger. -/
theorem size_le_of_occurs (σ : Subst) (x : Nat) (t : Ty) (h : t.occurs x = true) :
    (σ x).size ≤ (t.subst σ).size := by
  induction t with
  | var n =>
    -- `n == x` is true, so `n = x` and both sides are `(σ x).size`.
    simp [Ty.occurs] at h
    simp [Ty.subst, h]
  | int => simp [Ty.occurs] at h
  | bool => simp [Ty.occurs] at h
  | arrow a b iha ihb =>
    -- `x` occurs in `a` or in `b`; either way `σ x` is inside the image.
    simp only [Ty.occurs, Bool.or_eq_true] at h
    simp only [Ty.subst, Ty.size]
    rcases h with ha | hb
    · have := iha ha; omega
    · have := ihb hb; omega
  | list a ih =>
    simp only [Ty.occurs] at h
    simp only [Ty.subst, Ty.size]
    have := ih h; omega

/-- The occurs check is not a limitation of the algorithm: if `x` occurs in `t`
and `t` is not `x` itself, then *no* substitution makes them equal, because
the right-hand side is always strictly bigger. -/
theorem no_unifier_of_occurs (x : Nat) (t : Ty) (h : t.occurs x = true)
    (hne : t ≠ .var x) (σ : Subst) : (Ty.var x).subst σ ≠ t.subst σ := by
  intro heq
  have hsize := congrArg Ty.size heq
  simp only [Ty.subst] at hsize
  cases t with
  | var n =>
    simp [Ty.occurs] at h
    exact hne (by rw [h])
  | int => simp [Ty.occurs] at h
  | bool => simp [Ty.occurs] at h
  | arrow a b =>
    simp only [Ty.occurs, Bool.or_eq_true] at h
    simp only [Ty.subst, Ty.size] at hsize
    rcases h with ha | hb
    · have := size_le_of_occurs σ x a ha; omega
    · have := size_le_of_occurs σ x b hb; omega
  | list a =>
    simp only [Ty.occurs] at h
    simp only [Ty.subst, Ty.size] at hsize
    have := size_le_of_occurs σ x a h; omega
-- ANCHOR_END: occurs_lemmas

-- ANCHOR: self_application
/-- Typing `fun x -> x x` needs a solution of `?0 = ?0 → ?1`. There is none. -/
theorem self_application_untypable (σ : Subst) :
    (Ty.var 0).subst σ ≠ (.var 0 ⇒ .var 1).subst σ :=
  no_unifier_of_occurs 0 (.var 0 ⇒ .var 1) rfl (by simp) σ
-- ANCHOR_END: self_application

-- ANCHOR: unify
/-- A substitution in triangular form: a list of bindings, applied from left
to right. Later bindings never mention earlier variables. -/
abbrev Bindings := List (Nat × Ty)

def Bindings.toSubst : Bindings → Subst
  | [] => Subst.id
  | (x, t) :: rest => (Bindings.toSubst rest).comp (Subst.single x t)

/-- What unification can answer. -/
inductive Outcome where
  | unifier : Bindings → Outcome
  | clash : Ty → Ty → Outcome
  | occurs : Nat → Ty → Outcome
  | outOfFuel : Outcome

/-- Applies `[x := t]` to both sides of every remaining equation. -/
def substEqs (x : Nat) (t : Ty) (eqs : List (Ty × Ty)) : List (Ty × Ty) :=
  eqs.map fun (a, b) => (a.subst (.single x t), b.subst (.single x t))

/-- The variable case: solve the equation `?x = t`, then unify the remaining
equations with `k`, and add the binding `x := t` in front of their unifier. -/
def solveVar (k : List (Ty × Ty) → Outcome) (x : Nat) (t : Ty)
    (rest : List (Ty × Ty)) : Outcome :=
  if t = .var x then k rest                          -- Delete
  else if t.occurs x then .occurs x t                -- Occurs check
  else match k (substEqs x t rest) with              -- Eliminate
    | .unifier σ => .unifier ((x, t) :: σ)
    | failure => failure

/-- Unification of a list of equations, with `fuel` bounding the number of
steps (each equation processed costs one unit). -/
def unify : (fuel : Nat) → List (Ty × Ty) → Outcome
  | 0, _ => .outOfFuel
  | _ + 1, [] => .unifier []
  | fuel + 1, (a, b) :: rest =>
    match a, b with
    | .var x, t | t, .var x => solveVar (unify fuel) x t rest
    | .int, .int | .bool, .bool => unify fuel rest     -- Delete
    | .arrow a₁ b₁, .arrow a₂ b₂ =>                    -- Decompose
      unify fuel ((a₁, a₂) :: (b₁, b₂) :: rest)
    | .list a₁, .list a₂ => unify fuel ((a₁, a₂) :: rest)
    | a, b => .clash a b                               -- Clash
-- ANCHOR_END: unify

/-- Shows a unifier in solved form: each variable with its final value. -/
def Outcome.show : Outcome → String
  | .unifier σ =>
    let solved := σ.map fun (x, _) => s!"?{x} := {((Ty.var x).subst σ.toSubst).show}"
    "unifier: " ++ ", ".intercalate solved
  | .clash a b => s!"clash: {a.show} is not {b.show}"
  | .occurs x t => s!"occurs check: ?{x} occurs in {t.show}"
  | .outOfFuel => "out of fuel"

instance : Repr Outcome where
  reprPrec o _ := .text o.show

-- ANCHOR: unify_eval
/-- Unifies two types, with plenty of fuel for small examples. -/
def unify₁ (a b : Ty) : Outcome := unify 100 [(a, b)]

section Examples
open Ty

/-- info: unifier: ?0 := Bool, ?1 := Int -/
#guard_msgs in
#eval unify₁ (var 0 ⇒ int) (bool ⇒ var 1)

/-- info: unifier: ?0 := Int, ?1 := Int -/
#guard_msgs in
#eval unify₁ (var 0 ⇒ var 0) (int ⇒ var 1)

/-- info: unifier: ?1 := List Int, ?0 := Int -/
#guard_msgs in
#eval unify₁ (list (var 0) ⇒ var 1) (var 1 ⇒ list int)

/-- info: clash: Int is not Bool -/
#guard_msgs in
#eval unify₁ (int ⇒ var 0) (bool ⇒ var 0)

/-- info: occurs check: ?0 occurs in ?0 → ?1 -/
#guard_msgs in
#eval unify₁ (var 0) (var 0 ⇒ var 1)

end Examples
-- ANCHOR_END: unify_eval

-- ANCHOR: fuel
/-- info: out of fuel -/
#guard_msgs in
#eval unify 3 [(.var 0 ⇒ .int, .bool ⇒ .var 1)]

/-- info: unifier: ?0 := Bool, ?1 := Int -/
#guard_msgs in
#eval unify 4 [(.var 0 ⇒ .int, .bool ⇒ .var 1)]
-- ANCHOR_END: fuel

-- ANCHOR: unifies
/-- `σ` unifies a list of equations when it makes the two sides of each one
equal. -/
def Unifies (σ : Subst) (eqs : List (Ty × Ty)) : Prop :=
  ∀ e ∈ eqs, e.1.subst σ = e.2.subst σ

theorem unifies_nil (σ : Subst) : Unifies σ [] := by
  intro e he
  cases he

theorem unifies_cons {σ : Subst} {a b : Ty} {eqs : List (Ty × Ty)} :
    Unifies σ ((a, b) :: eqs) ↔ a.subst σ = b.subst σ ∧ Unifies σ eqs := by
  simp [Unifies]
-- ANCHOR_END: unifies

-- ANCHOR: sound_helpers
/-- A substitution that does not mention `x` leaves `t` alone. -/
theorem subst_single_of_not_occurs (x : Nat) (s t : Ty) (h : t.occurs x = false) :
    t.subst (.single x s) = t := by
  induction t with
  | var n =>
    simp [Ty.occurs] at h
    simp [Ty.subst, Subst.single, h]
  | int => rfl
  | bool => rfl
  | arrow a b iha ihb =>
    simp only [Ty.occurs, Bool.or_eq_false_iff] at h
    simp [Ty.subst, iha h.1, ihb h.2]
  | list a ih =>
    simp only [Ty.occurs] at h
    simp [Ty.subst, ih h]

/-- Applying the bindings `(x, s) :: σ` is applying `[x := s]`, then `σ`. -/
theorem toSubst_cons (x : Nat) (s : Ty) (σ : Bindings) (t : Ty) :
    t.subst (Bindings.toSubst ((x, s) :: σ)) =
      (t.subst (.single x s)).subst σ.toSubst := by
  rw [Bindings.toSubst, subst_comp]
-- ANCHOR_END: sound_helpers

-- ANCHOR: solve_var_sound
/-- The variable case is sound, provided the recursive call `k` is. -/
theorem solveVar_sound {k : List (Ty × Ty) → Outcome}
    (hk : ∀ eqs σ, k eqs = .unifier σ → Unifies σ.toSubst eqs)
    {x : Nat} {t : Ty} {rest : List (Ty × Ty)} {σ : Bindings}
    (h : solveVar k x t rest = .unifier σ) :
    Unifies σ.toSubst ((.var x, t) :: rest) := by
  unfold solveVar at h
  split at h
  · -- Delete: `t` is the variable `x` itself.
    rename_i ht
    subst ht
    exact unifies_cons.mpr ⟨rfl, hk rest σ h⟩
  · split at h
    · -- The occurs check failed: `h` says `.occurs x t = .unifier σ`.
      cases h
    · -- Eliminate: `x` does not occur in `t`, and `k` solved the rest.
      rename_i hne hocc
      split at h
      · rename_i σ' hσ'
        -- `h` says that `σ` is `(x, t) :: σ'`.
        cases h
        have hrest := hk _ _ hσ'
        have hfix : t.subst (.single x t) = t :=
          subst_single_of_not_occurs x t t (by simpa using hocc)
        refine unifies_cons.mpr ⟨?_, ?_⟩
        · -- The equation `?x = t` itself: both sides become `t.subst σ'`.
          rw [toSubst_cons, toSubst_cons, hfix]
          simp [Ty.subst, Subst.single]
        · -- The other equations: this is what `k` solved.
          intro e he
          rw [toSubst_cons, toSubst_cons]
          exact hrest _ (List.mem_map_of_mem he)
      · -- `k` failed, so `h` contradicts the hypothesis of this branch.
        rename_i hfail
        exact absurd h (hfail σ)
-- ANCHOR_END: solve_var_sound

-- ANCHOR: unify_sound
/-- Swapping the two sides of the first equation does not change what unifies. -/
theorem unifies_swap {σ : Subst} {a b : Ty} {eqs : List (Ty × Ty)}
    (h : Unifies σ ((a, b) :: eqs)) : Unifies σ ((b, a) :: eqs) := by
  rw [unifies_cons] at h ⊢
  exact ⟨h.1.symm, h.2⟩

/-- **Soundness of unification**: when `unify` returns a unifier, it really
unifies every equation it was given. -/
theorem unify_sound : ∀ (fuel : Nat) (eqs : List (Ty × Ty)) (σ : Bindings),
    unify fuel eqs = .unifier σ → Unifies σ.toSubst eqs := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs σ h
    simp [unify] at h
  | succ fuel ih =>
    intro eqs σ h
    match eqs with
    | [] => exact unifies_nil _
    | (a, b) :: rest =>
      -- One case for each pair of constructors: 25 cases. Unfolding one
      -- step of `unify` leaves `h` in one of four shapes.
      cases a <;> cases b <;> simp only [unify] at h
      -- (1) A clash: `h : .clash _ _ = .unifier σ` is impossible.
      all_goals try (cases h; done)
      -- (2) An equation `?x = t` or `t = ?x`: the variable case.
      all_goals try exact solveVar_sound ih h
      all_goals try exact unifies_swap (solveVar_sound ih h)
      -- (3) `Int = Int` and `Bool = Bool`: deleted; `ih` covers the rest.
      all_goals try exact unifies_cons.mpr ⟨rfl, ih _ _ h⟩
      -- (4) Decompose: two arrows, or two lists.
      case arrow.arrow a₁ b₁ a₂ b₂ =>
        have hs := ih _ _ h
        rw [unifies_cons, unifies_cons] at hs
        obtain ⟨ha, hb, hrest⟩ := hs
        exact unifies_cons.mpr ⟨by simp [Ty.subst, ha, hb], hrest⟩
      case list.list a₁ a₂ =>
        have hs := ih _ _ h
        rw [unifies_cons] at hs
        obtain ⟨ha, hrest⟩ := hs
        exact unifies_cons.mpr ⟨by simp [Ty.subst, ha], hrest⟩
-- ANCHOR_END: unify_sound

end Ch13
