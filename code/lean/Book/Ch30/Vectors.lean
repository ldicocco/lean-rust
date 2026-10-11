import Mathlib.Data.Nat.Notation

/-!
# Chapter 30 · Vectors: Π-types, Σ-types and indexed families

A type computed from a value, dependent functions (Π) and dependent pairs (Σ)
over `Bool`, a length-indexed vector type built from scratch (`Vec α n`) with a
total `head` and a length-preserving `zip`, `Fin n` and total indexing, Lean's
own `Vector α n` and indexing with proof obligations, dependent pairs that hide
the length (`Σ n, Vec α n`), and subtypes.
-/

namespace Ch30

-- ANCHOR: family
/-- A type that depends on a value: a function from `Bool` to `Type`. -/
def Answer : Bool → Type
  | true => ℕ
  | false => String

/-- A dependent function: the *type* of the result depends on the *value* of
the argument. Its type is the Π-type `(b : Bool) → Answer b`. -/
def answer : (b : Bool) → Answer b
  | true => (42 : ℕ)
  | false => "no number today"
-- ANCHOR_END: family

-- ANCHOR: family_eval
/-- info: 42 -/
#guard_msgs in
#eval (answer true : ℕ)

/-- info: "no number today" -/
#guard_msgs in
#eval (answer false : String)
-- ANCHOR_END: family_eval

-- ANCHOR: sigma_bool
/-- A dependent pair: a tag `b`, and a value whose type depends on the tag.
This is exactly what a Rust `enum` with two variants stores. -/
def mixed : List ((b : Bool) × Answer b) :=
  [⟨true, (7 : ℕ)⟩, ⟨false, "seven"⟩, ⟨true, (8 : ℕ)⟩]

/-- To use a component we look at the tag first, as a `match` on an enum does. -/
def describe : (b : Bool) × Answer b → String
  | ⟨true, n⟩ => "number " ++ Nat.repr n
  | ⟨false, s⟩ => String.append "text " s

/-- info: ["number 7", "text seven", "number 8"] -/
#guard_msgs in
#eval mixed.map describe
-- ANCHOR_END: sigma_bool

-- ANCHOR: vec
/-- Lists that know their length. `α` is a *parameter* (the same in every
constructor); the natural number after the colon is an *index* (each
constructor chooses it). -/
inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)
-- ANCHOR_END: vec

namespace Vec

variable {α β : Type}

-- ANCHOR: replicate
/-- `n` copies of `x`: a Π-type, because the length of the result is the
argument `n`. -/
def replicate : (n : ℕ) → α → Vec α n
  | 0, _ => nil
  | n + 1, x => cons x (replicate n x)

def toList {n : ℕ} : Vec α n → List α
  | nil => []
  | cons x xs => x :: toList xs

/-- From a list to a vector whose length is the length of *that* list. -/
def ofList : (xs : List α) → Vec α xs.length
  | [] => nil
  | x :: xs => cons x (ofList xs)
-- ANCHOR_END: replicate

-- ANCHOR: replicate_check
/-- info: Ch30.Vec.replicate {α : Type} (n : ℕ) : α → Vec α n -/
#guard_msgs in
#check replicate

/-- info: Ch30.Vec.ofList {α : Type} (xs : List α) : Vec α xs.length -/
#guard_msgs in
#check ofList

/-- info: [7, 7, 7] -/
#guard_msgs in
#eval (replicate 3 7).toList
-- ANCHOR_END: replicate_check

-- ANCHOR: head
/-- The first element. The argument has length `n + 1`, so the `nil` case
cannot occur, and Lean does not ask for it. -/
def head {n : ℕ} : Vec α (n + 1) → α
  | cons x _ => x

def tail {n : ℕ} : Vec α (n + 1) → Vec α n
  | cons _ xs => xs
-- ANCHOR_END: head

-- ANCHOR: samples
def three : Vec ℕ 3 := ofList [10, 20, 30]
def two : Vec Char 2 := ofList ['a', 'b']
-- ANCHOR_END: samples

-- ANCHOR: head_eval
/-- info: 10 -/
#guard_msgs in
#eval three.head

/-- info: [20, 30] -/
#guard_msgs in
#eval three.tail.toList
-- ANCHOR_END: head_eval

-- ANCHOR: head_nil
/--
error: Application type mismatch: The argument
  nil
has type
  Vec ℕ 0
but is expected to have type
  Vec ℕ (?m.2 + 1)
in the application
  nil.head
-/
#guard_msgs in
example : ℕ := head (nil : Vec ℕ 0)
-- ANCHOR_END: head_nil

-- ANCHOR: zip
/-- Both arguments have the same length `n`. Mismatched cases such as
`nil, cons ..` are impossible, so they are not written. -/
def zip {n : ℕ} : Vec α n → Vec β n → Vec (α × β) n
  | nil, nil => nil
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)

def map {n : ℕ} (f : α → β) : Vec α n → Vec β n
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
-- ANCHOR_END: zip

-- ANCHOR: zip_eval
/-- info: [(10, 'x'), (20, 'y'), (30, 'z')] -/
#guard_msgs in
#eval (three.zip (ofList ['x', 'y', 'z'])).toList
-- ANCHOR_END: zip_eval

-- ANCHOR: zip_mismatch
/--
error: Application type mismatch: The argument
  two
has type
  Vec Char 2
but is expected to have type
  Vec ?m.5 3
in the application
  three.zip two
-/
#guard_msgs in
example := three.zip two
-- ANCHOR_END: zip_mismatch

-- ANCHOR: get
/-- Total indexing: an index of type `Fin n` is a number together with a proof
that it is less than `n`. There is no `nil` case: `Fin 0` is empty. -/
def get {n : ℕ} : Vec α n → Fin n → α
  | cons x _, ⟨0, _⟩ => x
  | cons _ xs, ⟨i + 1, h⟩ => xs.get ⟨i, by omega⟩
-- ANCHOR_END: get

-- ANCHOR: get_eval
/-- info: 30 -/
#guard_msgs in
#eval three.get 2

/-- info: 30 -/
#guard_msgs in
#eval three.get ⟨2, by decide⟩
-- ANCHOR_END: get_eval

-- ANCHOR: get_out_of_range
/--
error: Tactic `decide` proved that the proposition
  5 < 3
is false
-/
#guard_msgs in
example : ℕ := three.get ⟨5, by decide⟩
-- ANCHOR_END: get_out_of_range

-- ANCHOR: fin_wrap
-- A numeral of type `Fin 3` is reduced modulo 3: `5` means `2`.
/-- info: (2, 30) -/
#guard_msgs in
#eval ((5 : Fin 3), three.get 5)
-- ANCHOR_END: fin_wrap

-- ANCHOR: append
/-- Concatenation. The length of the result is `m + n`, not `n + m`: the
section on equality in this chapter explains why the order matters. -/
def append {n m : ℕ} : Vec α n → Vec α m → Vec α (m + n)
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)
-- ANCHOR_END: append

-- ANCHOR: append_eval
/-- info: three.append three : Vec ℕ (3 + 3) -/
#guard_msgs in
#check three.append three
-- ANCHOR_END: append_eval

-- ANCHOR: theorems
/-- The index tells the truth: the list underneath has length `n`. -/
theorem length_toList {n : ℕ} (v : Vec α n) : v.toList.length = n := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [toList, ih]

theorem toList_ofList (xs : List α) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ofList, toList, ih]

theorem toList_append {n m : ℕ} (xs : Vec α n) (ys : Vec α m) :
    (xs.append ys).toList = xs.toList ++ ys.toList := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, toList, ih]
-- ANCHOR_END: theorems

-- ANCHOR: filter
/-- Keeping the elements that satisfy `p`: the length of the result depends on
the *contents* of the vector, not just on its length, so the result is a
dependent pair: some length `m`, and a vector of that length. -/
def filter (p : α → Bool) {n : ℕ} : Vec α n → (m : ℕ) × Vec α m
  | nil => ⟨0, nil⟩
  | cons x xs =>
    let ⟨m, ys⟩ := filter p xs
    if p x then ⟨m + 1, cons x ys⟩ else ⟨m, ys⟩
-- ANCHOR_END: filter

-- ANCHOR: filter_eval
/-- info: 2 -/
#guard_msgs in
#eval (three.filter (· > 15)).1

/-- info: [20, 30] -/
#guard_msgs in
#eval (three.filter (· > 15)).2.toList
-- ANCHOR_END: filter_eval

-- ANCHOR: filter_le
/-- What the Σ-type forgot, a theorem can recover: filtering never makes a
vector longer. -/
theorem filter_length_le (p : α → Bool) {n : ℕ} (v : Vec α n) :
    (v.filter p).1 ≤ n := by
  induction v with
  | nil => simp [filter]
  | cons x xs ih =>
    simp only [filter]
    split <;> simp <;> omega
-- ANCHOR_END: filter_le

end Vec

-- ANCHOR: some_vec
/-- A vector of *some* length: the Σ-type `Σ n, Vec α n`. Forgetting the length
gives back an ordinary list. -/
abbrev SomeVec (α : Type) := (n : ℕ) × Vec α n

def SomeVec.ofList {α : Type} (xs : List α) : SomeVec α := ⟨xs.length, Vec.ofList xs⟩
-- ANCHOR_END: some_vec

-- ANCHOR: lean_vector
/--
info: structure Vector.{u} (α : Type u) (n : ℕ) : Type u
number of parameters: 2
fields:
  Vector.toArray : Array α
  Vector.size_toArray : self.toArray.size = n
constructor:
  Vector.mk.{u} {α : Type u} {n : ℕ} (toArray : Array α) (size_toArray : toArray.size = n) : Vector α n
-/
#guard_msgs in
#print Vector
-- ANCHOR_END: lean_vector

-- ANCHOR: lean_vector_ops
/-- info: #v[1, 2, 3] ++ #v[4, 5] : Vector ℕ (3 + 2) -/
#guard_msgs in
#check #v[1, 2, 3] ++ #v[4, 5]

/-- info: #[1, 2, 3, 4, 5] -/
#guard_msgs in
#eval (#v[1, 2, 3] ++ #v[4, 5]).toArray

/-- info: @Vector.push : {α : Type u_1} → {n : ℕ} → Vector α n → α → Vector α (n + 1) -/
#guard_msgs in
#check @Vector.push
-- ANCHOR_END: lean_vector_ops

-- ANCHOR: indexing
/-- An index of type `Fin n` is always valid. -/
def atFin {n : ℕ} (v : Vector ℕ n) (i : Fin n) : ℕ := v[i]

/-- A proof in the context is found automatically. -/
def atProof {n : ℕ} (v : Vector ℕ n) (i : ℕ) (h : i < n) : ℕ := v[i]

/-- A proof can be given explicitly with `'`: here it needs a small argument. -/
def atNext {n : ℕ} (v : Vector ℕ n) (i : ℕ) (h : i + 1 < n) : ℕ := v[i]'(by omega)

/-- A run-time test produces the proof: in the `then` branch, `h : i < n`. -/
def atOr {n : ℕ} (v : Vector ℕ n) (i : ℕ) (default : ℕ) : ℕ :=
  if h : i < n then v[i] else default

/-- Rust's two options are also available: `v[i]?` and `v[i]!`. -/
def atOpt {n : ℕ} (v : Vector ℕ n) (i : ℕ) : Option ℕ := v[i]?
-- ANCHOR_END: indexing

-- ANCHOR: indexing_eval
/-- info: (30, 20, 99, none) -/
#guard_msgs in
#eval (atFin #v[10, 20, 30] 2, atNext #v[10, 20, 30] 1 (by decide),
  atOr #v[10, 20, 30] 7 99, atOpt #v[10, 20, 30] 7)
-- ANCHOR_END: indexing_eval

-- ANCHOR: indexing_fail
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
n : ℕ
v : Vector ℕ n
i : ℕ
⊢ i < n
-/
#guard_msgs in
def atUnchecked {n : ℕ} (v : Vector ℕ n) (i : ℕ) : ℕ := v[i]
-- ANCHOR_END: indexing_fail

-- ANCHOR: subtype
/-- A subtype: natural numbers together with a proof that they are at most
100. A dependent pair whose second component is a proof. -/
abbrev Percent := { n : ℕ // n ≤ 100 }

/-- Halving stays in range, and Lean demands a proof of it: `p.property` is the
proof stored inside `p` (`p.val ≤ 100`), and `omega` derives the new bound. -/
def half (p : Percent) : Percent :=
  ⟨p.val / 2, by have h := p.property; omega⟩

/-- `Fin n` is the same idea, packaged as a structure. -/
example : Fin 3 := ⟨2, by decide⟩
-- ANCHOR_END: subtype

-- ANCHOR: subtype_eval
/-- info: 21 -/
#guard_msgs in
#eval (half ⟨42, by decide⟩).val
-- ANCHOR_END: subtype_eval

end Ch30
