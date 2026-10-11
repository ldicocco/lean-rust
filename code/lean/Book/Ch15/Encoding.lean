import Book.Ch15.Existential

/-!
# Chapter 15 · Existentials encoded with universals

∃α. τ α ≅ ∀ρ. (∀α. τ α → ρ) → ρ. A package becomes a function that hands its
contents to any client. Packing and unpacking in this encoding, the
computation rule (by `rfl`), the counter packages of `Existential.lean` in
this form, the round trip from dependent pairs (which holds by `rfl`), and the
universe in which the encoding lives. In `Prop` the same encoding is a
logical equivalence, provable in both directions.
-/

namespace Ch15

universe u

-- ANCHOR: hidden
/-- ∃α. τ α, encoded: for every result type `ρ`, given a client that works
for every `α`, produce a `ρ`. The result types range over `Type u`. -/
def Hidden (τ : Type → Type) : Type (u + 1) :=
  (ρ : Type u) → ((α : Type) → τ α → ρ) → ρ

/-- Pack: remember `α` and `x`; when a client arrives, run it on them. -/
def Hidden.pack {τ : Type → Type} (α : Type) (x : τ α) : Hidden.{u} τ :=
  fun _ k => k α x

/-- Unpack: hand the client to the package. -/
def Hidden.unpack {τ : Type → Type} {ρ : Type u} (p : Hidden.{u} τ)
    (k : (α : Type) → τ α → ρ) : ρ :=
  p ρ k

/-- The computation rule holds by definition. -/
theorem Hidden.unpack_pack {τ : Type → Type} {ρ : Type u} (α : Type) (x : τ α)
    (k : (α : Type) → τ α → ρ) :
    (Hidden.pack α x).unpack k = k α x := rfl
-- ANCHOR_END: hidden

-- ANCHOR: hidden_universe
/-- info: Hidden CounterOps : Type 1 -/
#guard_msgs in
#check Hidden.{0} CounterOps

/-- info: Hidden CounterOps : Type 2 -/
#guard_msgs in
#check Hidden.{1} CounterOps
-- ANCHOR_END: hidden_universe

-- ANCHOR: with_counter
/-- The Rust function `with_counter`, in Lean: the package is chosen at run
time, and each branch packs a different state type. -/
def withCounter (fast : Bool) : Hidden.{0} CounterOps :=
  if fast then Hidden.pack Nat tenOps
  else Hidden.pack (List Unit) unaryOps

/-- A client: three steps, then read. It must work for every state type. -/
def stepThree (σ : Type) (ops : CounterOps σ) : Nat :=
  ops.get (ops.step (ops.step (ops.step ops.init)))

/-- info: (30, 3) -/
#guard_msgs in
#eval ((withCounter true).unpack stepThree, (withCounter false).unpack stepThree)
-- ANCHOR_END: with_counter

-- ANCHOR: round_trip
/-- From a dependent pair to the encoding. The result types must range over
`Type 1`, because the pair type itself lives in `Type 1`. -/
def toHidden {τ : Type → Type} : ((α : Type) × τ α) → Hidden.{1} τ
  | ⟨α, x⟩ => Hidden.pack α x

/-- Back: use the pair type itself as the result type `ρ`. -/
def fromHidden {τ : Type → Type} (p : Hidden.{1} τ) : (α : Type) × τ α :=
  p.unpack (fun α x => ⟨α, x⟩)

/-- One round trip is the identity, by computation. -/
theorem fromHidden_toHidden {τ : Type → Type} (s : (α : Type) × τ α) :
    fromHidden (toHidden s) = s := by
  -- Split the pair into its type and its value; then both sides compute
  -- to the same pair.
  cases s
  rfl
-- ANCHOR_END: round_trip

-- ANCHOR: prop_encoding
/-- In `Prop`, the encoding is an equivalence, and both directions are
provable: a proof of `∃ x, P x` is exactly something that can serve every
client `∀ x, P x → Q`. -/
theorem exists_iff_forall {α : Type} (P : α → Prop) :
    (∃ x, P x) ↔ ∀ Q : Prop, (∀ x, P x → Q) → Q := by
  constructor
  · -- Unpack the witness and hand it to the client `k`.
    intro ⟨x, hx⟩ Q k
    exact k x hx
  · -- Choose the client that packs its argument again.
    intro h
    exact h (∃ x, P x) (fun x hx => ⟨x, hx⟩)

/-- info: 'Ch15.exists_iff_forall' does not depend on any axioms -/
#guard_msgs in
#print axioms exists_iff_forall
-- ANCHOR_END: prop_encoding

end Ch15
