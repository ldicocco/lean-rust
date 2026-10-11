/-!
# Chapter 22 · The syntax of the affine λ-calculus

Types and terms of `λ^aff`, with de Bruijn indices for variables (as in
Chapters 7 and 9), and the function `uses` that counts how many times a term
uses a variable. The typing rules are in `Typing.lean`.
-/

namespace Ch22

-- ANCHOR: ty
/-- The types of `λ^aff`. -/
inductive Ty where
  /-- An opaque base type, named like a Rust type: `String`, `File`, ... -/
  | base : String → Ty
  /-- The unit type `𝟏`, Rust's `()`. -/
  | unit : Ty
  /-- Linear (affine) functions `τ ⊸ σ`, Rust's `FnOnce(τ) -> σ`. -/
  | lolli : Ty → Ty → Ty
  /-- The multiplicative pair `τ ⊗ σ`, Rust's `(τ, σ)`. -/
  | tensor : Ty → Ty → Ty
  /-- The additive pair `τ & σ` ("with"): a choice of one of the two. -/
  | amp : Ty → Ty → Ty
  /-- The sum `τ ⊕ σ`, a Rust `enum` with two variants. -/
  | plus : Ty → Ty → Ty
  deriving DecidableEq
-- ANCHOR_END: ty

-- ANCHOR: notation
@[inherit_doc] scoped infixr:25 " ⊸ " => Ty.lolli
@[inherit_doc] scoped infixl:35 " ⊗ " => Ty.tensor
@[inherit_doc] scoped infixl:35 " & " => Ty.amp
@[inherit_doc] scoped infixl:30 " ⊕ " => Ty.plus
-- ANCHOR_END: notation

/-- Print a type the way the book writes it. The flag says whether a compound
type must be put in parentheses (it must when it is a component of another). -/
def Ty.showP (paren : Bool) : Ty → String
  | .base n => n
  | .unit => "𝟏"
  | .lolli a b => wrap (showP true a ++ " ⊸ " ++ showP true b)
  | .tensor a b => wrap (showP true a ++ " ⊗ " ++ showP true b)
  | .amp a b => wrap (showP true a ++ " & " ++ showP true b)
  | .plus a b => wrap (showP true a ++ " ⊕ " ++ showP true b)
where
  wrap (s : String) : String := if paren then "(" ++ s ++ ")" else s

/-- Compound types get parentheses when they are an argument (as in
`some (File ⊸ 𝟏)`). -/
instance : Repr Ty where
  reprPrec t prec := match t with
    | .base _ | .unit => t.showP false
    | _ => if prec ≥ 1024 then "(" ++ t.showP false ++ ")" else t.showP false

-- ANCHOR: term
/-- The terms of `λ^aff`. Variables are de Bruijn indices: `var 0` is the
nearest enclosing binder. The comments give the named notation of the text. -/
inductive Term where
  | var : Nat → Term                    -- x
  | lam : Ty → Term → Term              -- λx:τ. e          (binds x)
  | app : Term → Term → Term            -- e₁ e₂
  | unit : Term                         -- ()
  | pair : Term → Term → Term           -- (e₁, e₂)          ⊗ introduction
  | letPair : Term → Term → Term        -- let (x, y) = e₁ in e₂  (binds x, y)
  | wpair : Term → Term → Term          -- ⟨e₁, e₂⟩          & introduction
  | fst : Term → Term                   -- fst e
  | snd : Term → Term                   -- snd e
  | inl : Ty → Term → Term              -- inl e  (the Ty is the right summand)
  | inr : Ty → Term → Term              -- inr e  (the Ty is the left summand)
  | case : Term → Term → Term → Term    -- case e of inl x ⇒ e₁ | inr y ⇒ e₂
  | letIn : Term → Term → Term          -- let x = e₁ in e₂  (binds x)
  deriving DecidableEq, Repr
-- ANCHOR_END: term

-- ANCHOR: uses
/-- `uses i e` counts the occurrences of the free variable with index `i` in
`e`. Under a binder the index of the same variable goes up by one (by two under
`letPair`, which binds two variables). The two alternatives of an additive pair
and the two branches of a `case` are counted with `max`, not `+`: only one of
them will ever run. -/
def uses (i : Nat) : Term → Nat
  | .var j => if i = j then 1 else 0
  | .lam _ e => uses (i + 1) e
  | .app e₁ e₂ => uses i e₁ + uses i e₂
  | .unit => 0
  | .pair e₁ e₂ => uses i e₁ + uses i e₂
  | .letPair e₁ e₂ => uses i e₁ + uses (i + 2) e₂
  | .wpair e₁ e₂ => max (uses i e₁) (uses i e₂)
  | .fst e => uses i e
  | .snd e => uses i e
  | .inl _ e => uses i e
  | .inr _ e => uses i e
  | .case e e₁ e₂ => uses i e + max (uses (i + 1) e₁) (uses (i + 1) e₂)
  | .letIn e₁ e₂ => uses i e₁ + uses (i + 1) e₂
-- ANCHOR_END: uses

-- ANCHOR: examples
/-- Two base types for the examples. -/
def Str : Ty := .base "String"
def File : Ty := .base "File"

/-- `λp. let (x, y) = p in (y, x)`. Inside the `let`, `y` is `var 0`, `x` is
`var 1` and `p` would be `var 2`. -/
def swap (τ σ : Ty) : Term :=
  .lam (τ ⊗ σ) (.letPair (.var 0) (.pair (.var 0) (.var 1)))

/-- `λx. λy. x`: the second argument is discarded. -/
def discard (τ σ : Ty) : Term :=
  .lam τ (.lam σ (.var 1))

/-- `λx. (x, x)`: the argument is used twice. -/
def dup (τ : Ty) : Term :=
  .lam τ (.pair (.var 0) (.var 0))
-- ANCHOR_END: examples

-- ANCHOR: uses_eval
-- The body of `swap` uses `p` once: the `let` consumes it.
/-- info: 1 -/
#guard_msgs in
#eval uses 0 (.letPair (.var 0) (.pair (.var 0) (.var 1)))

-- Under one binder, the free variable 0 is written `var 1`.
/-- info: 1 -/
#guard_msgs in
#eval uses 0 (.lam Str (.var 1))

-- The body of `dup` uses its variable twice.
/-- info: 2 -/
#guard_msgs in
#eval uses 0 (.pair (.var 0) (.var 0))

-- An additive pair counts the larger of its two components.
/-- info: 1 -/
#guard_msgs in
#eval uses 0 (.wpair (.var 0) (.var 0))
-- ANCHOR_END: uses_eval

-- ANCHOR: show_ty
/-- info: (String ⊗ File) ⊸ (File ⊗ String) -/
#guard_msgs in
#eval (Str ⊗ File) ⊸ (File ⊗ Str)
-- ANCHOR_END: show_ty

end Ch22
