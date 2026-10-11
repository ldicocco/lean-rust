/-!
# Chapter 3 · Arith in Lean

The toy language Arith: its syntax as inductive types, the typing judgment
`Γ ⊢ e : τ` as an inductive predicate, derivations as proof terms (by hand and
with tactics), a type checker and an evaluator written as Lean functions.
The theorems about the checker are in `Book/Ch03/Soundness.lean`.
-/

namespace Ch03

-- ANCHOR: ty
/-- The types of Arith: `τ ::= Nat | Bool`. -/
inductive Ty where
  | nat
  | bool
  deriving Repr, DecidableEq
-- ANCHOR_END: ty

-- ANCHOR: expr
/-- The expressions of Arith, one constructor per alternative of the grammar.
`if` and `let` are Lean keywords, so the constructors are called `ite` and
`letE`. -/
inductive Expr where
  | num  (n : Nat)
  | bool (b : Bool)
  | var  (x : String)
  | add  (e₁ e₂ : Expr)
  | eq   (e₁ e₂ : Expr)
  | ite  (c e₁ e₂ : Expr)
  | letE (x : String) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq
-- ANCHOR_END: expr

-- ANCHOR: sample
/-- `let x = 3 in if x == 3 then x + 1 else 0`, as a tree. -/
def sample : Expr :=
  .letE "x" (.num 3)
    (.ite (.eq (.var "x") (.num 3))
      (.add (.var "x") (.num 1))
      (.num 0))
-- ANCHOR_END: sample

-- ANCHOR: render
/-- How tightly an expression binds (larger binds tighter). -/
def Expr.prec : Expr → Nat
  | .letE .. | .ite .. => 0
  | .eq .. => 1
  | .add .. => 2
  | .num _ | .bool _ | .var _ => 3

/-- Print an expression in concrete syntax, with parentheses only where they
are needed: the same algorithm as the `Display` impl of the Rust crate. -/
def Expr.render (e : Expr) (min : Nat := 0) : String :=
  let text := match e with
    | .num n => toString n
    | .bool b => toString b
    | .var x => x
    | .add a b => s!"{a.render 2} + {b.render 3}"
    | .eq a b => s!"{a.render 2} == {b.render 2}"
    | .ite c a b => s!"if {c.render} then {a.render} else {b.render}"
    | .letE x a b => s!"let {x} = {a.render} in {b.render}"
  if e.prec < min then s!"({text})" else text

instance : ToString Expr := ⟨fun e => e.render⟩
-- ANCHOR_END: render

-- ANCHOR: render_eval
/-- info: "let x = 3 in if x == 3 then x + 1 else 0" -/
#guard_msgs in
#eval toString sample
-- ANCHOR_END: render_eval

-- ANCHOR: ctx
/-- A typing context `Γ = x₁ : τ₁, ..., xₙ : τₙ`, newest binding first. -/
abbrev Ctx := List (String × Ty)
-- ANCHOR_END: ctx

-- ANCHOR: lookup
/-- info: some (Ch03.Ty.bool) -/
#guard_msgs in
#eval ([("x", .bool), ("x", .nat)] : Ctx).lookup "x"
-- ANCHOR_END: lookup

-- ANCHOR: has_type
/-- The typing judgment `Γ ⊢ e : τ`. Each constructor is one inference rule:
its arguments are the premises, its type is the conclusion. -/
inductive HasType : Ctx → Expr → Ty → Prop where
  | num : HasType Γ (.num n) .nat
  | bool : HasType Γ (.bool b) .bool
  | var : Γ.lookup x = some τ →
      HasType Γ (.var x) τ
  | add : HasType Γ e₁ .nat → HasType Γ e₂ .nat →
      HasType Γ (.add e₁ e₂) .nat
  | eq : HasType Γ e₁ τ → HasType Γ e₂ τ →
      HasType Γ (.eq e₁ e₂) .bool
  | ite : HasType Γ c .bool → HasType Γ e₁ τ → HasType Γ e₂ τ →
      HasType Γ (.ite c e₁ e₂) τ
  | letE : HasType Γ e₁ τ₁ → HasType ((x, τ₁) :: Γ) e₂ τ₂ →
      HasType Γ (.letE x e₁ e₂) τ₂
-- ANCHOR_END: has_type

-- ANCHOR: has_type_check
/--
info: @HasType.letE : ∀ {Γ : Ctx} {e₁ : Expr} {τ₁ : Ty} {x : String} {e₂ : Expr} {τ₂ : Ty},
  HasType Γ e₁ τ₁ → HasType ((x, τ₁) :: Γ) e₂ τ₂ → HasType Γ (Expr.letE x e₁ e₂) τ₂
-/
#guard_msgs in
#check @HasType.letE
-- ANCHOR_END: has_type_check

-- ANCHOR: deriv_add
/-- `⊢ 1 + 2 : Nat`: rule T-Add with two instances of T-Num above it. -/
example : HasType [] (.add (.num 1) (.num 2)) .nat :=
  HasType.add HasType.num HasType.num
-- ANCHOR_END: deriv_add

-- ANCHOR: deriv_sample
/-- The derivation of `⊢ sample : Nat`, written out as a term. The shape of
the term is the shape of the derivation tree. -/
theorem sample_typed : HasType [] sample .nat :=
  HasType.letE HasType.num
    (HasType.ite
      (HasType.eq (HasType.var rfl) HasType.num)
      (HasType.add (HasType.var rfl) HasType.num)
      HasType.num)
-- ANCHOR_END: deriv_sample

-- ANCHOR: deriv_tactics
/-- The same derivation, built backwards from the goal with tactics. -/
example : HasType [] sample .nat := by
  unfold sample
  apply HasType.letE
  · -- Goal: HasType [] (Expr.num 3) ?τ₁
    exact HasType.num
  · -- Goal: HasType [("x", Ty.nat)] (Expr.ite ...) Ty.nat
    apply HasType.ite
    · exact HasType.eq (HasType.var rfl) HasType.num
    · exact HasType.add (HasType.var rfl) HasType.num
    · exact HasType.num

/-- And with a loop: `constructor` applies whichever rule fits the goal. -/
example : HasType [] sample .nat := by
  repeat constructor
-- ANCHOR_END: deriv_tactics

-- ANCHOR: check
/-- The type checker: synthesize the type of `e` in `Γ`, or fail with `none`.
For each kind of expression only one rule can apply, so the checker never
guesses. -/
def check (Γ : Ctx) : Expr → Option Ty
  | .num _ => some .nat
  | .bool _ => some .bool
  | .var x => Γ.lookup x
  | .add e₁ e₂ =>
    match check Γ e₁, check Γ e₂ with
    | some .nat, some .nat => some .nat
    | _, _ => none
  | .eq e₁ e₂ =>
    match check Γ e₁, check Γ e₂ with
    | some τ₁, some τ₂ => if τ₁ = τ₂ then some .bool else none
    | _, _ => none
  | .ite c e₁ e₂ =>
    match check Γ c, check Γ e₁, check Γ e₂ with
    | some .bool, some τ₁, some τ₂ => if τ₁ = τ₂ then some τ₁ else none
    | _, _, _ => none
  | .letE x e₁ e₂ =>
    match check Γ e₁ with
    | some τ₁ => check ((x, τ₁) :: Γ) e₂
    | none => none
-- ANCHOR_END: check

-- ANCHOR: check_eval
/-- info: some (Ch03.Ty.nat) -/
#guard_msgs in
#eval check [] sample

/-- info: none -/
#guard_msgs in
#eval check [] (.add (.num 1) (.bool true))

/-- info: some (Ch03.Ty.bool) -/
#guard_msgs in
#eval check [("b", .bool)] (.ite (.var "b") (.var "b") (.eq (.num 1) (.num 2)))
-- ANCHOR_END: check_eval

-- ANCHOR: value
/-- The values of Arith. -/
inductive Value where
  | num (n : Nat)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- The type of a value. -/
def Value.ty : Value → Ty
  | .num _ => .nat
  | .bool _ => .bool

/-- An environment: the values of the variables in scope, newest first. -/
abbrev Env := List (String × Value)
-- ANCHOR_END: value

-- ANCHOR: eval
/-- The evaluator: `some v` if `e` evaluates to `v`, `none` if the run gets
stuck. It never looks at types. -/
def eval (ρ : Env) : Expr → Option Value
  | .num n => some (.num n)
  | .bool b => some (.bool b)
  | .var x => ρ.lookup x
  | .add e₁ e₂ =>
    match eval ρ e₁, eval ρ e₂ with
    | some (.num n), some (.num m) => some (.num (n + m))
    | _, _ => none
  | .eq e₁ e₂ =>
    match eval ρ e₁, eval ρ e₂ with
    | some (.num n), some (.num m) => some (.bool (n == m))
    | some (.bool p), some (.bool q) => some (.bool (p == q))
    | _, _ => none
  | .ite c e₁ e₂ =>
    match eval ρ c with
    | some (.bool true) => eval ρ e₁
    | some (.bool false) => eval ρ e₂
    | _ => none
  | .letE x e₁ e₂ =>
    match eval ρ e₁ with
    | some v => eval ((x, v) :: ρ) e₂
    | none => none
-- ANCHOR_END: eval

-- ANCHOR: eval_eval
/-- info: some (Ch03.Value.num 4) -/
#guard_msgs in
#eval eval [] sample

/-- info: none -/
#guard_msgs in
#eval eval [] (.add (.num 1) (.bool true))

/-- info: some (Ch03.Value.num 1) -/
#guard_msgs in
#eval eval [] (.ite (.bool true) (.num 1) (.bool false))
-- ANCHOR_END: eval_eval

end Ch03
