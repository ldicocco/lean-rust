import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic.Abel

/-!
# Chapter 21 · A linear sequent calculus

Formulas of intuitionistic multiplicative-additive linear logic, the cut-free
sequent calculus as an inductive relation (with exchange as an explicit rule,
and neither weakening nor contraction), a few derivations, and a complete
proof that `A ⊢ A ⊗ A` is not derivable: every derivable sequent is
*balanced*, for some way of resolving its choices, the bag of atoms on the
left equals the bag of atoms on the right.
-/

namespace Ch21

-- ANCHOR: formula
/-- Formulas of intuitionistic linear logic (multiplicative-additive). -/
inductive Formula where
  /-- An atomic resource. -/
  | atom (name : String)
  /-- `1`, the unit of `⊗`: nothing at all. -/
  | one
  /-- `⊤`, the unit of `&`: accepts anything, offers nothing. -/
  | top
  /-- `0`, the unit of `⊕`: an impossible situation. -/
  | zero
  /-- `A ⊗ B`: both, at the same time. -/
  | tensor (A B : Formula)
  /-- `A & B`: either, and the consumer chooses. -/
  | «with» (A B : Formula)
  /-- `A ⊕ B`: either, and the producer chooses. -/
  | plus (A B : Formula)
  /-- `A ⊸ B`: consume an `A`, produce a `B`. -/
  | lolli (A B : Formula)
  deriving DecidableEq, Repr

@[inherit_doc] scoped infixr:40 " ⊗ " => Formula.tensor
@[inherit_doc] scoped infixr:35 " & " => Formula.with
@[inherit_doc] scoped infixr:30 " ⊕ " => Formula.plus
@[inherit_doc] scoped infixr:25 " ⊸ " => Formula.lolli
-- ANCHOR_END: formula

open Formula

-- ANCHOR: sequent_calculus
/-- `LProves Γ C`: the sequent `Γ ⊢ C` is derivable in linear logic. Left
rules act on the first formula of the context; `exch` moves formulas. -/
inductive LProves : List Formula → Formula → Prop where
  | ax (A : Formula) : LProves [A] A
  | exch {Γ Δ C} : Γ.Perm Δ → LProves Γ C → LProves Δ C
  | oneR : LProves [] one
  | oneL {Γ C} : LProves Γ C → LProves (one :: Γ) C
  | topR {Γ} : LProves Γ top
  | zeroL {Γ C} : LProves (zero :: Γ) C
  | tensorR {Γ Δ A B} : LProves Γ A → LProves Δ B → LProves (Γ ++ Δ) (A ⊗ B)
  | tensorL {Γ A B C} : LProves (A :: B :: Γ) C → LProves ((A ⊗ B) :: Γ) C
  | withR {Γ A B} : LProves Γ A → LProves Γ B → LProves Γ (A & B)
  | withL₁ {Γ A B C} : LProves (A :: Γ) C → LProves ((A & B) :: Γ) C
  | withL₂ {Γ A B C} : LProves (B :: Γ) C → LProves ((A & B) :: Γ) C
  | plusR₁ {Γ A B} : LProves Γ A → LProves Γ (A ⊕ B)
  | plusR₂ {Γ A B} : LProves Γ B → LProves Γ (A ⊕ B)
  | plusL {Γ A B C} :
      LProves (A :: Γ) C → LProves (B :: Γ) C → LProves ((A ⊕ B) :: Γ) C
  | lolliR {Γ A B} : LProves (A :: Γ) B → LProves Γ (A ⊸ B)
  | lolliL {Γ Δ A B C} :
      LProves Γ A → LProves (B :: Δ) C → LProves ((A ⊸ B) :: (Γ ++ Δ)) C

@[inherit_doc] scoped notation:20 Γ " ⊢ " C:21 => LProves Γ C
-- ANCHOR_END: sequent_calculus

section Derivations

variable (A B C : Formula)

-- ANCHOR: derivations
/-- A choice: from `A & B` take `A`. -/
example : [A & B] ⊢ A := .withL₁ (.ax A)

/-- Sharing: both sides of `A & A` are built from the same `A`. -/
example : [A] ⊢ A & A := .withR (.ax A) (.ax A)

/-- Exchange: `⊗R` produces the context `[B] ++ [A]`, and `exch` reorders it. -/
example : [A ⊗ B] ⊢ B ⊗ A :=
  .tensorL (.exch (List.Perm.swap A B []) (.tensorR (.ax B) (.ax A)))

/-- Modus ponens: `⊸L` splits `[A]` off for the argument. -/
example : [A ⊸ B, A] ⊢ B := .lolliL (Γ := [A]) (Δ := []) (.ax A) (.ax B)

/-- Currying: `A ⊸ B ⊸ C ⊢ A ⊗ B ⊸ C`. -/
example : [A ⊸ B ⊸ C] ⊢ A ⊗ B ⊸ C := by
  apply LProves.lolliR
  -- [A ⊗ B, A ⊸ B ⊸ C] ⊢ C
  apply LProves.tensorL
  -- [A, B, A ⊸ B ⊸ C] ⊢ C: bring the implication to the front
  apply LProves.exch (List.perm_middle (l₁ := [A, B]) (l₂ := [])).symm
  -- [A ⊸ B ⊸ C, A, B] ⊢ C: the argument A, then B ⊸ C with B
  exact .lolliL (Γ := [A]) (Δ := [B]) (.ax A)
    (.lolliL (Γ := [B]) (Δ := []) (.ax B) (.ax C))
-- ANCHOR_END: derivations

end Derivations

-- ANCHOR: bag
/-- A bag of resources: how many copies of each atom. Counts may be negative,
which records a debt: `A ⊸ B` provides one `B` and owes one `A`. -/
abbrev Bag : Type := String → ℤ

/-- The bag that holds exactly one copy of the atom `a`. -/
def single (a : String) : Bag := fun x => if x = a then 1 else 0
-- ANCHOR_END: bag

-- ANCHOR: provides
/-- `Provides F n`: one way of resolving the choices inside `F` yields the
bag `n`. The additives offer several ways; `⊤` and `0` fit any bag. -/
def Provides : Formula → Bag → Prop
  | atom a, n => n = single a
  | one, n => n = 0
  | top, _ => True
  | zero, _ => True
  | A ⊗ B, n => ∃ a b, Provides A a ∧ Provides B b ∧ n = a + b
  | A & B, n => Provides A n ∨ Provides B n
  | plus A B, n => Provides A n ∨ Provides B n
  | A ⊸ B, n => ∃ a b, Provides A a ∧ Provides B b ∧ n = b - a

/-- A whole context provides the sum of what its formulas provide. -/
def ProvidesAll : List Formula → Bag → Prop
  | [], n => n = 0
  | A :: Γ, n => ∃ a g, Provides A a ∧ ProvidesAll Γ g ∧ n = a + g

/-- A sequent is balanced when the context and the goal can provide the same
bag of atoms. -/
def Balanced (Γ : List Formula) (C : Formula) : Prop :=
  ∃ n, ProvidesAll Γ n ∧ Provides C n
-- ANCHOR_END: provides

-- ANCHOR: helper_lemmas
/-- Every formula provides some bag. -/
theorem provides_exists : ∀ F : Formula, ∃ n, Provides F n
  | atom a => ⟨single a, rfl⟩
  | one => ⟨0, rfl⟩
  | top => ⟨0, trivial⟩
  | zero => ⟨0, trivial⟩
  | A ⊗ B =>
    let ⟨a, ha⟩ := provides_exists A
    let ⟨b, hb⟩ := provides_exists B
    ⟨a + b, a, b, ha, hb, rfl⟩
  | A & _ =>
    let ⟨a, ha⟩ := provides_exists A
    ⟨a, .inl ha⟩
  | plus A _ =>
    let ⟨a, ha⟩ := provides_exists A
    ⟨a, .inl ha⟩
  | A ⊸ B =>
    let ⟨a, ha⟩ := provides_exists A
    let ⟨b, hb⟩ := provides_exists B
    ⟨b - a, a, b, ha, hb, rfl⟩

/-- Every context provides some bag. -/
theorem providesAll_exists : ∀ Γ : List Formula, ∃ n, ProvidesAll Γ n
  | [] => ⟨0, rfl⟩
  | A :: Γ =>
    let ⟨a, ha⟩ := provides_exists A
    let ⟨g, hg⟩ := providesAll_exists Γ
    ⟨a + g, a, g, ha, hg, rfl⟩

/-- Concatenated contexts provide the sum of the bags. -/
theorem providesAll_append {Γ Δ : List Formula} {g d : Bag}
    (hΓ : ProvidesAll Γ g) (hΔ : ProvidesAll Δ d) : ProvidesAll (Γ ++ Δ) (g + d) := by
  induction Γ generalizing g with
  | nil =>
    -- hΓ : g = 0
    simp only [ProvidesAll] at hΓ
    simpa [hΓ] using hΔ
  | cons A Γ ih =>
    obtain ⟨a, g', ha, hg', rfl⟩ := hΓ
    exact ⟨a, g' + d, ha, ih hg', by abel⟩

/-- Reordering a context does not change what it provides. -/
theorem providesAll_perm {Γ Δ : List Formula} (p : Γ.Perm Δ) :
    ∀ {n : Bag}, ProvidesAll Γ n → ProvidesAll Δ n := by
  induction p with
  | nil => exact id
  | cons A _ ih =>
    rintro n ⟨a, g, ha, hg, rfl⟩
    exact ⟨a, g, ha, ih hg, rfl⟩
  | swap A B Γ =>
    rintro n ⟨b, r, hb, ⟨a, g, ha, hg, rfl⟩, rfl⟩
    exact ⟨a, b + g, ha, ⟨b, g, hb, hg, rfl⟩, by abel⟩
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
-- ANCHOR_END: helper_lemmas

-- ANCHOR: invariant
/-- **The invariant.** Every derivable sequent is balanced. -/
theorem balanced_of_proves {Γ : List Formula} {C : Formula}
    (h : Γ ⊢ C) : Balanced Γ C := by
  induction h with
  | ax A =>
    -- [A] ⊢ A: both sides provide whatever A provides.
    obtain ⟨a, ha⟩ := provides_exists A
    exact ⟨a, ⟨a, 0, ha, rfl, by abel⟩, ha⟩
  | exch p _ ih =>
    obtain ⟨n, hΓ, hC⟩ := ih
    exact ⟨n, providesAll_perm p hΓ, hC⟩
  | oneR => exact ⟨0, rfl, rfl⟩
  | oneL _ ih =>
    obtain ⟨n, hΓ, hC⟩ := ih
    exact ⟨n, ⟨0, n, rfl, hΓ, by abel⟩, hC⟩
  | @topR Γ =>
    -- ⊤ accepts whatever the context provides.
    obtain ⟨g, hg⟩ := providesAll_exists Γ
    exact ⟨g, hg, trivial⟩
  | @zeroL Γ C =>
    -- 0 makes up the difference between the goal and the rest.
    obtain ⟨c, hc⟩ := provides_exists C
    obtain ⟨g, hg⟩ := providesAll_exists Γ
    exact ⟨c, ⟨c - g, g, trivial, hg, by abel⟩, hc⟩
  | tensorR _ _ ih₁ ih₂ =>
    -- The two halves of the context pay for the two halves of A ⊗ B.
    obtain ⟨n₁, hΓ, hA⟩ := ih₁
    obtain ⟨n₂, hΔ, hB⟩ := ih₂
    exact ⟨n₁ + n₂, providesAll_append hΓ hΔ, n₁, n₂, hA, hB, rfl⟩
  | tensorL _ ih =>
    obtain ⟨n, ⟨a, r, ha, ⟨b, g, hb, hg, rfl⟩, rfl⟩, hC⟩ := ih
    exact ⟨a + (b + g), ⟨a + b, g, ⟨a, b, ha, hb, rfl⟩, hg, by abel⟩, hC⟩
  | withR _ _ ih₁ _ =>
    -- One premise is enough: A & B can provide what A provides.
    obtain ⟨n, hΓ, hA⟩ := ih₁
    exact ⟨n, hΓ, .inl hA⟩
  | withL₁ _ ih =>
    obtain ⟨n, ⟨a, g, ha, hg, rfl⟩, hC⟩ := ih
    exact ⟨a + g, ⟨a, g, .inl ha, hg, rfl⟩, hC⟩
  | withL₂ _ ih =>
    obtain ⟨n, ⟨b, g, hb, hg, rfl⟩, hC⟩ := ih
    exact ⟨b + g, ⟨b, g, .inr hb, hg, rfl⟩, hC⟩
  | plusR₁ _ ih =>
    obtain ⟨n, hΓ, hA⟩ := ih
    exact ⟨n, hΓ, .inl hA⟩
  | plusR₂ _ ih =>
    obtain ⟨n, hΓ, hB⟩ := ih
    exact ⟨n, hΓ, .inr hB⟩
  | plusL _ _ ih₁ _ =>
    obtain ⟨n, ⟨a, g, ha, hg, rfl⟩, hC⟩ := ih₁
    exact ⟨a + g, ⟨a, g, .inl ha, hg, rfl⟩, hC⟩
  | lolliR _ ih =>
    -- From A, Γ ⊢ B: Γ provides g and B provides a + g, so A ⊸ B provides g.
    obtain ⟨n, ⟨a, g, ha, hg, rfl⟩, hB⟩ := ih
    exact ⟨g, hg, a, a + g, ha, hB, by abel⟩
  | lolliL _ _ ih₁ ih₂ =>
    -- Γ pays for the argument A; the result B joins Δ.
    obtain ⟨m, hΓ, hA⟩ := ih₁
    obtain ⟨n, ⟨b, d, hb, hd, rfl⟩, hC⟩ := ih₂
    exact ⟨b + d, ⟨b - m, m + d, ⟨m, b, hA, hb, rfl⟩,
      providesAll_append hΓ hd, by abel⟩, hC⟩
-- ANCHOR_END: invariant

-- ANCHOR: no_contraction
/-- **No contraction.** `A ⊢ A ⊗ A` has no derivation in linear logic. -/
theorem not_proves_dup (a : String) : ¬ ([atom a] ⊢ atom a ⊗ atom a) := by
  intro h
  obtain ⟨n, ⟨x, g, hx, hg, hn⟩, ⟨y, z, hy, hz, hyz⟩⟩ := balanced_of_proves h
  -- hx : x = single a,  hg : g = 0,  hy : y = single a,  hz : z = single a
  subst hx hg hy hz
  -- hn : n = single a + 0,  hyz : n = single a + single a
  -- Count the copies of `a` on both sides: 1 + 0 = 1 + 1 is false.
  have count := congrFun (hn.symm.trans hyz) a
  simp [single] at count
-- ANCHOR_END: no_contraction

-- ANCHOR: no_weakening
/-- **No weakening.** `A ⊗ B ⊢ A` has no derivation when `A` and `B` are
different atoms: the `B` on the left has nowhere to go. -/
theorem not_proves_fst {a b : String} (hab : a ≠ b) :
    ¬ ([atom a ⊗ atom b] ⊢ atom a) := by
  intro h
  obtain ⟨n, ⟨t, g, ⟨x, y, hx, hy, ht⟩, hg, hn⟩, hC⟩ := balanced_of_proves h
  subst hx hy ht hg hC
  -- hn : single a = single a + single b + 0. Count the copies of `b`.
  have count := congrFun hn b
  simp [single, hab.symm] at count
-- ANCHOR_END: no_weakening

-- ANCHOR: coffee
/-- The vending machine: a coin buys a coffee... -/
example : [atom "coin", atom "coin" ⊸ (atom "coffee" & atom "tea")] ⊢ atom "coffee" :=
  .exch (List.Perm.swap _ _ [])
    (.lolliL (Γ := [atom "coin"]) (Δ := []) (.ax _) (.withL₁ (.ax _)))

/-- ...or a tea, but not both. -/
theorem one_coin_one_drink :
    ¬ ([atom "coin", atom "coin" ⊸ (atom "coffee" & atom "tea")] ⊢
        atom "coffee" ⊗ atom "tea") := by
  intro h
  obtain ⟨n, ⟨c, r, hc, ⟨m, g, ⟨k, d, hk, hd, hm⟩, hg, hr⟩, hn⟩,
    ⟨x, y, hx, hy, hxy⟩⟩ := balanced_of_proves h
  subst hc hk hm hg hr hx hy
  -- The machine's offer was resolved one way or the other.
  rcases hd with rfl | rfl
  · -- Chose coffee: there is no tea on the left. Count teas.
    have count := congrFun (hn.symm.trans hxy) "tea"
    simp [single] at count
  · -- Chose tea: count coffees.
    have count := congrFun (hn.symm.trans hxy) "coffee"
    simp [single] at count
-- ANCHOR_END: coffee

end Ch21
