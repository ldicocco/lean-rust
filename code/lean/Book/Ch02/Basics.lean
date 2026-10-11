/-!
# Chapter 2 · Lean basics for Rust programmers

Functions, numbers, structures, inductive types, pattern matching, `Option`,
`Except`, `List` and `Array`, namespaces and dot notation. This file imports
nothing: everything in it is part of Lean's core library.
-/

namespace Ch02

-- ANCHOR: double
/-- Rust: `fn double(n: u64) -> u64 { 2 * n }` -/
def double (n : Nat) : Nat := 2 * n
-- ANCHOR_END: double

-- ANCHOR: double_eval
/-- info: 42 -/
#guard_msgs in
#eval double 21
-- ANCHOR_END: double_eval

-- ANCHOR: area
/-- Two parameters. Rust: `fn area(width: u64, height: u64) -> u64`. -/
def area (width height : Nat) : Nat := width * height

/-- info: 12 -/
#guard_msgs in
#eval area 3 4
-- ANCHOR_END: area

-- ANCHOR: area_check
/-- info: Ch02.area (width height : Nat) : Nat -/
#guard_msgs in
#check area

/-- info: area : Nat → Nat → Nat -/
#guard_msgs in
#check (area)

/-- info: area 3 : Nat → Nat -/
#guard_msgs in
#check area 3

/-- info: [30, 40, 50] -/
#guard_msgs in
#eval [3, 4, 5].map (area 10)
-- ANCHOR_END: area_check

-- ANCHOR: lambdas
/-- info: [1, 4, 9] -/
#guard_msgs in
#eval [1, 2, 3].map (fun n => n * n)

/-- info: [11, 12, 13] -/
#guard_msgs in
#eval [1, 2, 3].map (· + 10)
-- ANCHOR_END: lambdas

-- ANCHOR: describe
/-- `let`, `if` and string interpolation. Everything is an expression, and
there is no `return`: the body's value is the result. -/
def describe (n : Nat) : String :=
  let parity := if n % 2 == 0 then "even" else "odd"
  s!"{n} is {parity}"

/-- info: "7 is odd" -/
#guard_msgs in
#eval describe 7
-- ANCHOR_END: describe

-- ANCHOR: numbers
/-- info: 0 -/
#guard_msgs in
#eval (3 : Nat) - 5          -- Nat subtraction stops at zero

/-- info: -2 -/
#guard_msgs in
#eval (3 : Int) - 5

/-- info: 0 -/
#guard_msgs in
#eval (255 : UInt8) + 1      -- fixed-width types wrap around

/-- info: 1267650600228229401496703205376 -/
#guard_msgs in
#eval 2 ^ 100                -- Nat has no upper bound
-- ANCHOR_END: numbers

-- ANCHOR: first_or
/-- A generic function. `{α : Type}` is an *implicit* argument: Lean infers it
from the other arguments, as Rust infers `T` in
`fn first_or<T>(xs: Vec<T>, default: T) -> T`. -/
def firstOr {α : Type} (xs : List α) (default : α) : α :=
  match xs with
  | [] => default
  | x :: _ => x

/-- info: 3 -/
#guard_msgs in
#eval firstOr [3, 4] 0

/-- info: "none" -/
#guard_msgs in
#eval firstOr [] "none"
-- ANCHOR_END: first_or

-- ANCHOR: first_or_explicit
/-- info: @firstOr : {α : Type} → List α → α → α -/
#guard_msgs in
#check @firstOr

/-- info: 7 -/
#guard_msgs in
#eval @firstOr Nat [] 7      -- like Rust's turbofish: first_or::<u64>
-- ANCHOR_END: first_or_explicit

-- ANCHOR: auto_bound
/-- `α` is not declared anywhere: Lean adds `{α}` as an implicit argument. -/
def identity (x : α) : α := x

/-- info: @identity : {α : Sort u_1} → α → α -/
#guard_msgs in
#check @identity
-- ANCHOR_END: auto_bound

-- ANCHOR: auto_bound_typo
/--
error: failed to synthesize instance of type class
  HMul Nat Nta Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def triple (n : Nta) : Nat := 3 * n     -- a typo: `Nta` instead of `Nat`
-- ANCHOR_END: auto_bound_typo

-- ANCHOR: fib
/-- A definition by pattern matching: one equation per case. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- info: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34] -/
#guard_msgs in
#eval (List.range 10).map fib
-- ANCHOR_END: fib

-- ANCHOR: point
/-- Rust: `struct Point { x: i64, y: i64 }` with `#[derive(Debug, PartialEq)]`. -/
structure Point where
  x : Int
  y : Int
  deriving Repr, BEq

def origin : Point := { x := 0, y := 0 }

def p : Point := ⟨3, 4⟩
-- ANCHOR_END: point

-- ANCHOR: point_eval
/-- info: 3 -/
#guard_msgs in
#eval p.x

/-- info: { x := 3, y := 10 } -/
#guard_msgs in
#eval { p with y := 10 }      -- Rust: Point { y: 10, ..p }

/-- info: { x := 3, y := 4 } -/
#guard_msgs in
#eval p                       -- p itself is unchanged

/-- info: Ch02.Point.mk (x y : Int) : Point -/
#guard_msgs in
#check Point.mk
-- ANCHOR_END: point_eval

-- ANCHOR: command
/-- Rust: `enum Command { Ping, Get(String), Set(String, u64), Delete(String) }`. -/
inductive Command where
  | ping
  | get (key : String)
  | set (key : String) (value : Nat)
  | delete (key : String)
  deriving Repr, BEq

/-- `match` with one arm per constructor. -/
def Command.describe (c : Command) : String :=
  match c with
  | .ping => "ping"
  | .get key => s!"read {key}"
  | .set key value => s!"write {value} to {key}"
  | .delete key => s!"remove {key}"

/-- info: "write 3 to retries" -/
#guard_msgs in
#eval (Command.set "retries" 3).describe
-- ANCHOR_END: command

-- ANCHOR: missing_case
/--
error: Missing cases:
ping
-/
#guard_msgs in
def Command.isWrite : Command → Bool
  | .set _ _ => true
  | .delete _ => true
  | .get _ => false
-- ANCHOR_END: missing_case

-- ANCHOR: tree
/-- A binary search tree. Rust needs `Box<Tree>` for the recursive fields;
Lean does not, because every value of an inductive type is already a pointer
to an immutable heap object. -/
inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)
  deriving Repr

def Tree.insert (t : Tree) (k : Nat) : Tree :=
  match t with
  | .leaf => .node .leaf k .leaf
  | .node l x r =>
    if k < x then .node (l.insert k) x r
    else if x < k then .node l x (r.insert k)
    else t

def Tree.toList : Tree → List Nat
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

/-- info: [1, 3, 4, 5, 9] -/
#guard_msgs in
#eval ([5, 3, 9, 1, 4, 3].foldl Tree.insert .leaf).toList
-- ANCHOR_END: tree

-- ANCHOR: option
/-- Rust: `fn safe_div(a: u64, b: u64) -> Option<u64>`. -/
def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

/-- info: some 5 -/
#guard_msgs in
#eval safeDiv 10 2

/-- info: none -/
#guard_msgs in
#eval safeDiv 10 0

/-- info: 0 -/
#guard_msgs in
#eval (safeDiv 10 0).getD 0        -- Rust: .unwrap_or(0)

/-- info: some 6 -/
#guard_msgs in
#eval (safeDiv 10 2).map (· + 1)   -- Rust: .map(|n| n + 1)
-- ANCHOR_END: option

-- ANCHOR: except
/-- The errors of a small parser. -/
inductive ParseError where
  | empty
  | notADigit (c : Char)
  deriving Repr

/-- `Except ε α` is Rust's `Result<α, ε>`: note that the error type comes
first. The constructors are `.ok` and `.error`. -/
def parseDigit (c : Char) : Except ParseError Nat :=
  if c.isDigit then .ok (c.toNat - '0'.toNat) else .error (.notADigit c)

/-- info: Except.ok 7 -/
#guard_msgs in
#eval parseDigit '7'

/-- info: Except.error (Ch02.ParseError.notADigit 'x') -/
#guard_msgs in
#eval parseDigit 'x'
-- ANCHOR_END: except

-- ANCHOR: except_match
/-- Combining two fallible steps with `match`, the long way. (Section "Effects"
shows the short way, with `do` and `←`, Lean's version of Rust's `?`.) -/
def parseTwoDigits (a b : Char) : Except ParseError Nat :=
  match parseDigit a with
  | .error e => .error e
  | .ok d₁ =>
    match parseDigit b with
    | .error e => .error e
    | .ok d₂ => .ok (10 * d₁ + d₂)

/-- info: Except.ok 42 -/
#guard_msgs in
#eval parseTwoDigits '4' '2'
-- ANCHOR_END: except_match

-- ANCHOR: list
def primes : List Nat := [2, 3, 5, 7]

/-- info: [1, 2, 3, 5, 7] -/
#guard_msgs in
#eval 1 :: primes              -- a new list whose tail *is* primes

/-- info: [2, 3, 5, 7] -/
#guard_msgs in
#eval primes                   -- primes itself is unchanged

/-- info: [6, 10, 14] -/
#guard_msgs in
#eval primes.map (· * 2) |>.filter (· > 5)

/-- info: 17 -/
#guard_msgs in
#eval primes.foldl (· + ·) 0

/-- info: (some 5, some 3, none) -/
#guard_msgs in
#eval (primes.find? (· > 4), primes[1]?, primes[10]?)
-- ANCHOR_END: list

-- ANCHOR: array
def readings : Array Nat := #[12, 15, 11]

/-- info: #[12, 15, 11, 14] -/
#guard_msgs in
#eval readings.push 14

/-- info: #[12, 99, 11] -/
#guard_msgs in
#eval readings.set! 1 99

/-- info: (3, 15) -/
#guard_msgs in
#eval (readings.size, readings[1]!)
-- ANCHOR_END: array

-- ANCHOR: namespace
namespace Point

/-- Inside `namespace Point`, this defines `Point.add`. -/
def add (a b : Point) : Point := ⟨a.x + b.x, a.y + b.y⟩

/-- The Manhattan length. `Int.natAbs` is the absolute value, as a `Nat`. -/
def manhattan (a : Point) : Nat := a.x.natAbs + a.y.natAbs

end Point

/-- info: { x := 6, y := 8 } -/
#guard_msgs in
#eval p.add p                  -- dot notation: Point.add p p

/-- info: 7 -/
#guard_msgs in
#eval p.manhattan
-- ANCHOR_END: namespace

end Ch02
