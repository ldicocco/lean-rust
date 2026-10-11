import Std.Data.HashMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Appendix B · Lean 4 for Rust programmers: cheat sheet

Small, compiled examples of the Lean constructs a Rust programmer reaches for
first, each next to its Rust counterpart in the appendix.
-/

namespace AppB

-- ANCHOR: functions
-- fn square(x: u64) -> u64 { x * x }
def square (x : ℕ) : ℕ := x * x

-- Generic, with the type parameter implicit (inferred at call sites):
-- fn twice<T>(f: impl Fn(T) -> T, x: T) -> T { f(f(x)) }
def twice {α : Type} (f : α → α) (x : α) : α := f (f x)

-- A closure: |n| n + 1
#guard twice (fun n => n + 1) 5 = 7

-- Pattern matching in the definition itself (like a `match` on the argument):
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- ANCHOR_END: functions

-- ANCHOR: structures
-- struct Point { x: f64, y: f64 }  +  #[derive(Debug, Clone, PartialEq)]
structure Point where
  x : Float
  y : Float
  deriving Repr, BEq

-- impl Point { fn norm2(&self) -> f64 { ... } }   (methods live in the namespace)
def Point.norm2 (p : Point) : Float := p.x * p.x + p.y * p.y

def origin : Point := { x := 0, y := 0 }
def p : Point := ⟨3, 4⟩            -- anonymous constructor
def q : Point := { p with y := 0 } -- struct update syntax: Point { y: 0.0, ..p }

/-- info: 25.000000 -/
#guard_msgs in
#eval p.norm2                      -- dot notation: Point.norm2 p
-- ANCHOR_END: structures

-- ANCHOR: inductives
-- enum Shape { Circle(f64), Rect { w: f64, h: f64 } }
inductive Shape where
  | circle (r : Float)
  | rect (w h : Float)
  deriving Repr

def Shape.area : Shape → Float
  | .circle r => 3.14159 * r * r
  | .rect w h => w * h

-- A recursive enum needs no Box: enum Tree { Leaf, Node(Box<Tree>, u64, Box<Tree>) }
inductive Tree where
  | leaf
  | node (left : Tree) (value : ℕ) (right : Tree)

def Tree.sum : Tree → ℕ
  | .leaf => 0
  | .node l v r => l.sum + v + r.sum
-- ANCHOR_END: inductives

-- ANCHOR: options
-- Option<T> and Result<T, E>
def safeDiv (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

def parsePort (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => if n < 65536 then .ok n else .error s!"{n} is not a port"
  | none => .error s!"not a number: {s}"

/-- info: Except.ok 8080 -/
#guard_msgs in
#eval parsePort "8080"

-- The `?` operator is `←` inside `do`:
def addPorts (a b : String) : Except String ℕ := do
  let x ← parsePort a
  let y ← parsePort b
  return x + y
-- ANCHOR_END: options

-- ANCHOR: collections
-- Vec<u64> ~ Array ℕ (a contiguous array, updated in place when unshared)
def squares : Array ℕ := (Array.range 5).map square

/-- info: #[0, 1, 4, 9, 16] -/
#guard_msgs in
#eval squares

-- Linked lists are the default sequence in proofs: [1, 2, 3] : List ℕ
/-- info: [2, 4, 6] -/
#guard_msgs in
#eval [1, 2, 3].map (· * 2)

/-- info: 6 -/
#guard_msgs in
#eval [1, 2, 3].foldl (· + ·) 0

-- HashMap<String, u64>
def stock : Std.HashMap String ℕ :=
  (∅ : Std.HashMap String ℕ) |>.insert "bolts" 40 |>.insert "nuts" 75

/-- info: some 75 -/
#guard_msgs in
#eval stock.get? "nuts"
-- ANCHOR_END: collections

-- ANCHOR: classes
-- trait Describe { fn describe(&self) -> String; }
class Describe (α : Type) where
  describe : α → String

-- impl Describe for Point { ... }
instance : Describe Point where
  describe p := s!"({p.x}, {p.y})"

-- fn show_all<T: Describe>(xs: &[T]) -> Vec<String>
def showAll {α : Type} [Describe α] (xs : List α) : List String :=
  xs.map Describe.describe
-- ANCHOR_END: classes

-- ANCHOR: imperative
-- Imperative-looking code in `do` blocks: `let mut`, `for`, early `return`.
def firstNegativeIndex (xs : Array ℤ) : Option ℕ := Id.run do
  for h : i in [0:xs.size] do
    if xs[i] < 0 then return some i
  return none

def sumTo (n : ℕ) : ℕ := Id.run do
  let mut total := 0
  for i in [0:n+1] do
    total := total + i
  return total

/-- info: 5050 -/
#guard_msgs in
#eval sumTo 100

-- fn main() { println!("..."); }
def main : IO Unit := do
  let name := "Lean"
  IO.println s!"Hello from {name}"
-- ANCHOR_END: imperative

-- ANCHOR: proofs
-- A theorem is a definition whose type is a proposition.
theorem square_eq (n : ℕ) : square n = n * n := rfl

example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

example (x y : ℤ) (h₁ : x < y) (h₂ : 0 < x) : 0 < x + y := by linarith

theorem fib_pos (n : ℕ) (h : 0 < n) : 0 < fib n := by
  induction n using fib.induct with
  | case1 => omega
  | case2 => decide
  | case3 n ih₁ ih₂ =>
    simp only [fib]
    omega
-- ANCHOR_END: proofs

end AppB
