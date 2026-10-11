# Dependent Types

In Chapter 1 you met a Lean function that Rust cannot write. It returned the
first element of an array, and it took two arguments: the array `xs`, and a
proof `h : 0 < xs.size` that the array is not empty. The type of the second
argument mentions the *value* of the first. We called this a dependent type,
noted that it is the feature that sets Lean apart from Rust, and promised a
chapter about it. This is that chapter.

Dependent types have been in the background ever since: Chapter 8's
intrinsically typed terms, Chapter 10's `Sigma` and `Subtype`, Chapter 25's vault
indexed by its balance. Now we look at them directly: what it means for a type
to depend on a term, which type formers this requires, what changes about
equality, and how much of it a Rust programmer can have today.

The payoff is large. When types may mention values, a type can state a precise
property, such as "a vector of exactly three elements", "an index smaller than
the length" or "a proof that these two numbers are equal", and the type checker
checks it. The price is that type checking sometimes has to compute, and that
some equations which are obviously true need a proof before the type checker
accepts them. Chapter 31 then uses dependent types for their most ambitious
purpose: writing a program's full specification as its type.

**In this chapter you will learn:**

- what a type family is, and the two type formers that dependent types add:
  Π-types (dependent functions) and Σ-types (dependent pairs), with their rules;
- the difference between the parameters and the indices of an inductive family,
  and how a length-indexed vector makes `head` total and `zip` length-preserving;
- how Lean's `Vector`, `Fin` and the notations `xs[i]`, `xs[i]'h`, `xs[i]?` and
  `xs[i]!` turn bounds checks into proof obligations;
- equality as a type, rewriting with `rw` and `▸`, the difference between
  definitional and propositional equality, and why it shapes the way you write
  indices;
- the λ-cube, and where Rust, Haskell and Lean sit in it;
- how far Rust gets: const generics, Peano numerals at the type level, Σ-types
  as slices and trait objects, newtypes as refinement types, and what is still
  unstable;
- how to build dimension-checked matrices in Lean, prove their laws, and connect
  them to Mathlib's `Matrix`.

## Types that mention terms

Every type constructor you use daily in Rust takes types as arguments:
`Vec<T>`, `Option<T>`, `Result<T, E>`, `HashMap<K, V>`. There is one familiar
exception. In `[u8; 4]` the `4` is a number, and `[u8; 4]` and `[u8; 5]` are
different types: a function that expects one rejects the other. A *value*
appears inside a type.

Type theory says that such a type **depends** on a term. Here are three types
that we would like to have, each depending on a value:

- `Vec α n`, the lists of elements of type `α` of length exactly `n`;
- `Fin n`, the natural numbers smaller than `n`;
- `a = b`, the proofs that `a` and `b` are equal.

### Type families

To talk about types like these we need functions that return types. In Lean
this needs no special machinery: `Type` is itself a type (it lives in
`Type 1`, as Chapter 12 explained), so a function can return a type just as it
returns a number. A function whose result is a type is called a **type family**.
The Lean code for this section is in `code/lean/Book/Ch30/Vectors.lean`:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:family}}
```

`Answer` is a family indexed by `Bool`: `Answer true` is `ℕ` and `Answer false`
is `String`. The function `answer` is the interesting part. Its result type,
`Answer b`, depends on the argument `b`. To check the first clause, Lean must
check that `42` has type `Answer true`; it computes `Answer true` by running the
definition of `Answer`, gets `ℕ`, and the check succeeds. Notice what just
happened: to type-check a program, the type checker *ran* a program. That is the
first and most important consequence of letting types mention terms.

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:family_eval}}
```

(The ascriptions `(answer true : ℕ)` tell `#eval` how to print the result;
Lean accepts them because `Answer true` computes to `ℕ`.) Rust has no
counterpart to `answer`: the return type of a Rust function is fixed by its
signature, and generic code can choose a type based on another *type* (through
an associated type) but never based on a value.

### Π-types: dependent functions

The type of `answer` is written `(b : Bool) → Answer b` in Lean, and
$\Pi b{:}\mathsf{Bool}.\,\mathsf{Answer}\,b$ in type theory. It is a
**Π-type**, or dependent function type: the type of functions whose result type
depends on the argument. Three rules describe it. The first says when a Π-type
is a well-formed type at all:

$$
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma,\, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \Pi x{:}A.\,B : \mathsf{Type}}\;\textsf{Pi-Form}
$$

The second premise is where dependency enters: $B$ is checked in a context that
contains $x$, so $B$ may mention $x$. In other words, $B$ is a type family over
$A$. The introduction and elimination rules are the familiar rules for λ and
application from Chapter 8, with one change:

$$
\dfrac{\Gamma,\, x : A \vdash b : B}{\Gamma \vdash \lambda x.\, b : \Pi x{:}A.\,B}\;\textsf{Pi-Intro}
\qquad\qquad
\dfrac{\Gamma \vdash f : \Pi x{:}A.\,B \qquad \Gamma \vdash a : A}{\Gamma \vdash f\,a : B[a/x]}\;\textsf{Pi-Elim}
$$

The change is in the conclusion of Pi-Elim. The type of $f\,a$ is $B[a/x]$: the
family $B$ with the actual argument $a$ substituted for $x$. Applying `answer`
to `true` gives a value of type `Answer true`; applying it to `false` gives one
of type `Answer false`. The substitution in the *type* is the whole point.

When $B$ does not mention $x$, the substitution does nothing, and the rules
become exactly those of the ordinary function type $A \to B$ from Chapter 8:
$A \to B$ is the special case of $\Pi x{:}A.\,B$ in which the result type does
not depend on the argument. In Lean, `A → B`, `(x : A) → B` and `∀ x : A, B` are
all spellings of Π-types. Chapter 10 used the last one: under Curry–Howard, Π is
the universal quantifier. Chapter 12's polymorphic `{α : Type} → α → α` is a
Π-type whose argument is a type.

Why the letter Π, for *product*? Think of a dependent function over a finite
type as a table with one entry per argument. A function of type
`(b : Bool) → Answer b` is completely described by two values, `f true : ℕ` and
`f false : String`; so such functions correspond one to one with pairs in
`ℕ × String`. In general, $\Pi x{:}A.\,B$ is the product of the types $B[a/x]$
over all $a$ in $A$, the way $\prod$ is a product of numbers.

### Σ-types: dependent pairs

The second type former is the **Σ-type**, or dependent pair type. An element of
$\Sigma x{:}A.\,B$ is a pair $(a, b)$ in which the *type* of $b$ depends on the
*value* of $a$:

$$
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma,\, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \Sigma x{:}A.\,B : \mathsf{Type}}\;\textsf{Sigma-Form}
\qquad\qquad
\dfrac{\Gamma \vdash a : A \qquad \Gamma \vdash b : B[a/x]}{\Gamma \vdash (a, b) : \Sigma x{:}A.\,B}\;\textsf{Sigma-Intro}
$$

$$
\dfrac{\Gamma \vdash p : \Sigma x{:}A.\,B}{\Gamma \vdash \pi_1\,p : A}\;\textsf{Sigma-Fst}
\qquad\qquad
\dfrac{\Gamma \vdash p : \Sigma x{:}A.\,B}{\Gamma \vdash \pi_2\,p : B[\pi_1\,p/x]}\;\textsf{Sigma-Snd}
$$

Rule Sigma-Intro says that to build a pair, the second component must have the
type that the family assigns to the *first component*. Rule Sigma-Snd says that
the type of the second projection mentions the first projection. When $B$ does
not mention $x$, the rules collapse to those of the ordinary product $A \times B$.
Lean writes the Σ-type `(x : A) × B` or `Σ x, B`, builds pairs with the
anonymous constructor `⟨a, b⟩`, and projects with `.1` and `.2`.

Why Σ, for *sum*? Take the family `Answer` again. A pair `⟨b, v⟩` with
`v : Answer b` is either `⟨true, n⟩` with `n : ℕ` or `⟨false, s⟩` with
`s : String`. That is a tagged union of `ℕ` and `String`:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:sigma_bool}}
```

This is precisely what a Rust `enum` is. The discriminant is the first
component, the payload is the second, and the type of the payload depends on the
discriminant. A `match` on an enum is Σ-elimination: inspect the tag, and only
then do you know the type of what it carries, as `describe` does here. So Rust
does have Σ-types, built into the language, as long as the first component
ranges over a finite set of variants that you list in advance. What it lacks is
a Σ over an arbitrary type, such as "some natural number `n`, and a vector of
length `n`". We will meet Rust's partial substitutes for that later in the
chapter.

Under Curry–Howard, Σ is the existential quantifier: a proof of
$\exists x.\,P(x)$ is a witness together with a proof that the witness has the
property. Chapter 10 explained the subtlety that Lean keeps two versions apart:
`Sigma`, which lives in `Type` and whose first component you can project out and
compute with, and `Exists`, which lives in `Prop` and whose witness cannot be
extracted into data. A third relative, the subtype `{ x : A // P x }`, is a Σ
whose second component is a proof. It will be everywhere in this chapter and the
next.

| | Π-type | Σ-type |
|---|---|---|
| Lean | `(x : A) → B x` | `(x : A) × B x` |
| non-dependent case | `A → B` | `A × B` |
| over `Bool` | a pair | a tagged union |
| logic | $\forall x.\,P(x)$ | $\exists x.\,P(x)$ |
| closest in Rust | `fn f<const N: usize>` | `enum`, slices, `dyn Trait` |

## Indexed families

Type families defined by a function, like `Answer`, are handy, but the families
that matter most are defined *inductively*, constructor by constructor. The
standard example is the vector of a given length.

### Parameters and indices

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:vec}}
```

`Vec α` is a function from `ℕ` to `Type`, one type for each length. The
declaration distinguishes two kinds of arguments:

- `α`, written *before* the colon, is a **parameter**: the same in the result
  type of every constructor. Rust's generic parameters are parameters in this
  sense: every variant of `Option<T>` produces an `Option<T>` for the same `T`.
- The `ℕ` *after* the colon is an **index**: each constructor chooses its value.
  `nil` produces index `0`, and `cons` turns index `n` into `n + 1`. Rust has no
  indices (Haskell has them through an extension called GADTs).

You have seen indexed families before: `Nat.le` in Chapter 10 and `Term Γ τ` in
Chapter 8. The braces in `cons {n : ℕ}` make `n` an implicit argument
(Chapter 2), inferred from the type of the tail.

### Functions whose types depend on their arguments

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:replicate}}
```

`replicate` has a Π-type: the length of the result is the argument `n`. Each
clause is checked against the type with the pattern substituted for `n`: the
first must produce a `Vec α 0`, the second a `Vec α (n + 1)`. The type of
`ofList` mentions the argument `xs` itself.

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:replicate_check}}
```

### A total `head` and a length-preserving `zip`

Here is the function that gives indexed families their reputation:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:head}}
```

There is no case for `nil`, and Lean does not complain. The argument has type
`Vec α (n + 1)`. If it were `nil`, its type would be `Vec α 0`, so the index
`0` would have to equal `n + 1`. Those are built from different constructors of
`ℕ` (`Nat.zero` and `Nat.succ`), so no `n` can make them equal, and Lean removes
the case. This is **dependent pattern matching**: matching on a value also
refines the indices in its type, and cases whose indices cannot fit are
discarded. The function is total, and the compiled code contains no check and no
panic.

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:samples}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:head_eval}}
```

The definitions of `three` and `two` deserve a second look. `ofList [10, 20, 30]`
has type `Vec ℕ [10, 20, 30].length`, and we declared the type `Vec ℕ 3`. Lean
accepts this because `[10, 20, 30].length` computes to `3`: the type checker
evaluates again.

Applying `head` to an empty vector is a type error:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:head_nil}}
```

The argument `nil` has type `Vec ℕ 0`, and `head` expected a
`Vec ℕ (?m.2 + 1)`, where `?m.2` is a metavariable (Chapter 13) standing for the
implicit `n`. Unification found no `n` with `n + 1 = 0`. (Lean prints `head nil`
as `nil.head`.) In Rust, `v[0]` on an empty vector panics and `v.first()`
returns an `Option`; here the question never arises at run time, because a
program that could ask it does not type-check.

`zip` is the second classic:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:zip}}
```

Both arguments have the same index `n`. If the first is `nil`, then `n` is `0`,
so the second must be `nil` too; if the first is a `cons`, the second must be a
`cons`. The mixed cases are impossible, and again Lean removes them. Rust's
`Iterator::zip` silently stops at the shorter input; this `zip` cannot be
called with inputs of different lengths:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:zip_eval}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:zip_mismatch}}
```

### `Fin`: numbers that know their bound

Indexing needs a type of valid positions. Lean's core library defines it as a
structure with two fields, a number and a proof:

```lean,ignore
structure Fin (n : ℕ) where
  val  : ℕ
  isLt : val < n
```

A value of type `Fin n` is a natural number together with evidence that it is
smaller than `n`. `Fin 3` has exactly three elements, and `Fin 0` has none,
because no proof of `i < 0` exists. Indexing a vector with a `Fin` is total:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:get}}
```

In the second clause the vector is `cons _ xs` with `xs : Vec α m`, and the
index is `⟨i + 1, h⟩` with `h : i + 1 < m + 1`. The recursive call needs a
`Fin m`, so we build `⟨i, _⟩` and prove `i < m` with `omega` (Chapter 2), which
decides linear arithmetic and finds the proof from `h`. There is no clause for
`nil`, because `Fin 0` is empty.

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:get_eval}}
```

In `three.get 2` the numeral `2` is read as an element of `Fin 3`. The second
line builds the index explicitly, with `decide` proving `2 < 3`. An index that is
out of range cannot be built:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:get_out_of_range}}
```

Numerals, however, are a trap:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:fin_wrap}}
```

> [!WARNING]
> A numeral of type `Fin n` is reduced modulo `n`, so `(5 : Fin 3)` is `2`, and
> `three.get 5` happily returns the element at position 2. The type guarantees
> that the index is in range, not that it is the index you meant. Build indices
> that come from outside with `⟨i, proof⟩`, which fails loudly when the proof
> does not exist.

### Concatenation and the order of indices

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:append}}
```

The result of appending a vector of length `n` and one of length `m` has length
`m + n`. You would probably have written `n + m`, and the reason we did not is
one of the most instructive facts about dependent types; the section on
equality below explains it. Lean does not simplify the index in the type it
displays:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:append_eval}}
```

`Vec ℕ (3 + 3)` is nevertheless the same type as `Vec ℕ 6`, because `3 + 3`
computes to `6`: you can declare a constant of type `Vec ℕ 6` and give it
`three.append three` as its value.

An indexed type tells the truth about its index, and we can prove it:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:theorems}}
```

`length_toList` is proved by induction on the vector. In the `nil` case both
sides compute to `0`, and `rfl` closes the goal. In the `cons x xs` case the goal
is `(cons x xs).toList.length = n + 1` and `ih : xs.toList.length = n`;
`simp [toList, ih]` unfolds `toList` one step, uses the library fact that
`(a :: l).length = l.length + 1`, rewrites with `ih`, and closes `n + 1 = n + 1`.
Induction on an indexed family replaces the index in each case (by `0`, or by
`n + 1`) automatically. The other two proofs follow the same pattern.

### Σ again: when the length depends on the contents

Some operations produce a vector whose length cannot be computed from the
lengths of the inputs. Keeping only the elements that satisfy a predicate is the
standard example: the length of the result depends on the *elements*. Its type
is a Σ-type, "some length `m`, and a vector of that length":

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:filter}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:filter_eval}}
```

A Σ-type hides the index, but a theorem can recover what we know about it:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:filter_le}}
```

In the `cons` case, `simp only [filter]` unfolds one step, leaving the first
projection of an `if p x then … else …`. `split` makes one goal per branch, and
`<;>` runs the next tactic on every goal: `simp` computes the projection, and
`omega` finishes with `ih : (filter p xs).1 ≤ n`.

Hiding the length altogether gives back ordinary lists:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:some_vec}}
```

`SomeVec α` and `List α` carry the same information. A list *is* a Σ-type: a
length, and that many elements. We will see the same fact in Rust, where a slice
reference stores its length next to the pointer.

## Lean's vectors and indexing with proofs

Our `Vec` is a linked list with a length in its type. Lean's core library has a
vector type of its own, built differently:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:lean_vector}}
```

A `Vector α n` is an `Array α` (Lean's contiguous array, the counterpart of
Rust's `Vec`) bundled with a proof that its size is `n`. Proofs are erased when
Lean compiles a program (Chapter 10), so a `Vector` costs exactly what an
`Array` costs. The operations have the types you would expect:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:lean_vector_ops}}
```

Indexing is where the design pays off. Lean's indexing notation `v[i]` asks for
a proof that `i` is in range and tries to find it on its own; when it cannot,
you have alternatives:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:indexing}}
```

Indexing runs a small tactic, `get_elem_tactic`, which looks for the fact in
the context and tries some simple arithmetic; that is how `atProof` works. In
`atNext` the fact `i < n` only *follows* from the hypothesis, so `v[i]'proof`
supplies it explicitly. In `atOr` the proof comes from a run-time test: the
*dependent if* `if h : i < n then … else …` names the condition, and in the
`then` branch `h : i < n` is a hypothesis. This is the bridge between a dynamic
check and a static guarantee.

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:indexing_eval}}
```

Without any of these, Lean refuses, with the message you first saw in
Chapter 1:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:indexing_fail}}
```

The message ends with the goal it could not prove, `⊢ i < n`. Here are the
options side by side with Rust's:

| Lean | Rust | when `i` is out of range |
|---|---|---|
| `v[i]`, proof found | (none) | cannot happen |
| `v[i]'h` | (none) | cannot happen |
| `v[i]?` | `v.get(i)` | `none` |
| `v[i]!` | `v[i]` | panic |
| `if h : i < n then v[i] else d` | `if i < v.len() { v[i] } else { d }` | `d` |

The last row looks the same in both languages, but it is not. In Lean, the test
produces a proof that the indexing consumes. In Rust, the test produces a
`bool` that the type system forgets, and `v[i]` checks the bound again (the
optimizer often removes the second check, but as an optimization, not a
guarantee).

Subtypes are the general form of "a value with a proof attached". A percentage
is a natural number with a proof that it is at most 100:

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:subtype}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Vectors.lean:subtype_eval}}
```

To return a `Percent`, `half` must prove that the new value is at most 100,
using the evidence carried by its input. We will compare this with Rust's way of
guaranteeing the same invariant later in the chapter.

## Equality as a type

The third of our dependent types was `a = b`. In a dependently typed language
equality is no longer just a boolean test: it decides which programs
type-check.

### Equality from scratch

Equality is an inductive family with a single constructor. Here it is from
scratch, in `code/lean/Book/Ch30/Equality.lean`:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:same}}
```

`Same a b` is a proposition indexed by two values. The only constructor,
`refl a`, builds a proof of `Same a a`, where both indices are the same. So a
proof of `Same a b` can exist only when `a` and `b` are the same value. That
single constructor is enough to derive everything we expect from equality:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:same_laws}}
```

Every proof starts with `cases h`. Since `h` can only have been built by
`refl`, whose indices are equal, Lean unifies `b` with `a` and replaces `b` by
`a` in the goal: dependent pattern matching once more, as in `head`. The theorem
`subst` is the essence of equality: any property of `a` is a property of
anything equal to `a`. This principle, **transport**, is the elimination rule of
the equality type. Lean's own equality is defined in exactly the same way:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:print_eq}}
```

(`Sort u_1` makes `Eq` universe-polymorphic, Chapter 12. `#print` reports two
parameters, `α` and the left side `a`: since `a` is uniform in the constructor,
Lean promotes it from an index to a parameter.)

### Definitional and propositional equality

**Definitional equality** is what the type checker sees by itself. Two terms
are definitionally equal if they compute to the same result: by unfolding
definitions, by β-reduction (substituting arguments into function bodies), and by
running pattern matching on constructors. The tactic `rfl` (and the term `rfl`)
proves `a = b` exactly when `a` and `b` are definitionally equal:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:defeq}}
```

**Propositional equality** is the type `a = b` itself: anything you can *prove*.
Every definitional equality is a propositional one (by `rfl`), but not the other
way around. Here is the standard example:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:zero_add_rfl}}
```

`n + 0 = n` was accepted by `rfl`, but `0 + n = n` is not. The statement is
true, of course; it is just not true *by computation*. To see why, look at how
addition on natural numbers is defined in Lean's core library (simplified from
the file `Init/Prelude.lean` of the toolchain):

```lean,ignore
protected def Nat.add : Nat → Nat → Nat
  | n, .zero   => n
  | n, .succ m => .succ (Nat.add n m)
```

Addition is defined by recursion on its *second* argument. `n + 0` matches the
first equation, whatever `n` is, and computes to `n`: definitional. `0 + n`, for
a variable `n`, matches neither equation, because the second argument is not
known to be `zero` or `succ m`; the computation is stuck, and `rfl` has nothing
to compare. To prove `0 + n = n` we need induction:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:zero_add_proof}}
```

In the `succ` case the goal `0 + (k + 1) = k + 1` *can* compute one step,
because the second argument is now a successor; `show` restates it in the
computed form `(0 + k) + 1 = k + 1`, which Lean accepts because the two are
definitionally equal. Then `rw [ih]` **rewrites**: it replaces the left side of
`ih : 0 + k = k` by its right side, and closes the resulting `k + 1 = k + 1` by
trying `rfl`. (`rw [← h]` rewrites from right to left.) The lesson:
definitional equality is fixed by how your functions recurse; propositional
equality is everything you can prove.

### Why the order of indices matters

With dependent types the distinction decides which programs type-check,
because the type checker compares *types* by definitional equality. Here is
`append` with the index `n + m`, the way you would first write it:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:append_nm_fail}}
```

Both clauses fail. In the first, `ys : Vec α m` must have type
`Vec α (0 + m)`, and `0 + m` is not definitionally `m`. In the second, the clause
produces length `n + m + 1` but must produce `n + 1 + m`, which does not compute
for a variable `m`. (The dagger in `n✝` marks a name you cannot refer to, here
the implicit length of the tail.) The `append` of `Vectors.lean` used `m + n`,
and with that order both clauses check by computation: `m + 0` is `m`, and
`m + (n + 1)` is `(m + n) + 1`. The index follows the recursion. That is the
first fix, and the one to prefer.

The second fix is to keep the type you want and *transport* the value along a
proof of the equation. If `h : a = b` and `v : Vec α a`, then `h ▸ v` is the
same vector, seen at type `Vec α b`:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:append_cast}}
```

`Nat.add_comm m n : m + n = n + m` is a library theorem, proved by induction.
The triangle `▸` is our `subst`, used on data; Lean works out what to rewrite
from the expected type. Transport changes the type and nothing else:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:cast_lemmas}}
```

In `toList_cast`, `subst h` replaces `m` by `n` everywhere; then `h ▸ v` is a
transport along `n = n`, which computes to `v`, and `rfl` finishes. In
`toList_append'`, `rw` unfolds `append'`, removes the transport with
`toList_cast`, and applies `toList_append`. Transport works, but every theorem
about `append'` must see through the `▸`. Experienced users of dependent types
choose indices so that the equations they need hold by computation.

### Decidable equality

The last ingredient connects equality with running programs. Chapter 5
introduced `Decidable`: a proposition is decidable when there is an algorithm
that answers it, and the answer carries evidence either way:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:decidable}}
```

A `Decidable p` is `isTrue` with a proof of `p` or `isFalse` with a proof of
`¬p`; `decide` runs the algorithm, and `deriving DecidableEq` generates one, as
`#[derive(PartialEq)]` does in Rust. The difference is the evidence: Rust's `==`
returns a `bool`, and nothing remembers what it was a test of. A dependent `if`
turns the evidence into something the types can use:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:to_vec}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:to_vec_eval}}
```

`toVec?` takes a vector whose length `k` is known only at run time (a Σ-type)
and tests `k = n`. In the `then` branch the test has produced a proof
`h : k = n`, and `h ▸ v` transports the vector to type `Vec α n`. This is the
general pattern for crossing from data that arrives at run time (Σ) to code that
demands static guarantees (Π): decide, then transport.

Not every proposition is decidable. Equality of functions `ℕ → ℕ` is not: no
algorithm can compare two functions on infinitely many inputs. Quantifiers over
infinite types are not decidable either, though bounded ones are:

```lean
{{#include ../../code/lean/Book/Ch30/Equality.lean:undecidable}}
```

## The λ-cube

In the early 1990s Henk Barendregt organized a family of typed λ-calculi as
the corners of a cube, which gives us a map for placing Rust and Lean. Start
from the simply typed λ-calculus of Chapter 8, where terms depend on terms.
There are three independent ways to add a dependency:

- **terms depending on types**: polymorphism, a term that takes a type as an
  argument, as in `fn id<T>(x: T) -> T` (System F, Chapter 12);
- **types depending on types**: type operators, as in `Vec<T>` viewed as a
  function from types to types (Chapter 17);
- **types depending on terms**: dependent types, the subject of this chapter.

Each subset of the three gives a system, and the eight systems form the cube:

![The λ-cube. Each arrow adds one kind of dependency; λ→ is the simply typed λ-calculus, λ2 is System F, λω is System Fω, λP adds dependent types, and λC, the Calculus of Constructions, has all three. Red marks what Rust has (dashed: only fragments).](../images/ch30-lambda-cube.svg)

The corner λ→ is Chapter 8. Moving back gives λ2, System F (Chapter 12).
Moving up gives $\lambda\underline{\omega}$ (read "weak lambda omega"), with
type operators but no polymorphism, and λω, System Fω, with both: the system in which you can
quantify over type constructors, which is what a `Functor` class needs
(Chapter 17). Moving right adds dependent types: λP is the system known as LF,
used as a logical framework for encoding logics. The far corner, λC, has all
three dependencies: it is the **Calculus of Constructions** of Thierry Coquand
and Gérard Huet (1988), in which terms and types live in one language and any
of them may depend on any other.

Here is where Rust, Lean and Haskell sit, with the caveats that a picture this
simple requires:

| Language | Polymorphism | Type operators | Dependent types |
|---|---|---|---|
| Rust | rank-1 generics; rank-2 only via traits and `for<'a>` | generic types, but no abstraction over them; GATs as a workaround | const generics only |
| Haskell (GHC) | higher-rank types (extension) | higher-kinded types, `Functor` | approximated: GADTs, type families, type-level data |
| Lean | full (Π over types) | full (functions into `Type`) | full: λC and more |

GHC's core language is an extension of System Fω, and its dependent-type
features simulate Π-types by keeping a type-level copy of the values involved.
Lean is beyond the cube altogether: its type theory adds to the Calculus of
Constructions inductive types (every `inductive` in this book), a hierarchy of
universes and an impredicative `Prop` (Chapter 12), and quotient types. This
family of systems is usually called the Calculus of Inductive Constructions;
Rocq (formerly Coq) is based on it too.

One more distinction matters in practice. Without dependent types, type
checking never runs programs: Rust's types can be checked and erased without
evaluating anything but constant expressions. From λP on, deciding whether two
types are equal means computing with terms, as with `Answer true` and
`Vec ℕ (3 + 3)`. That is why a dependently typed language insists on
termination (Chapter 2, and Chapter 31 in detail): if the type checker runs your
programs, a non-terminating program would make type checking loop forever.

## Rust's approximations

Rust has no Π-types over arbitrary values, but it has partial substitutes, and
they are how working Rust code gets some of this chapter's guarantees.

### Const generics

A **const generic** parameter, `const N: usize` in angle brackets, is a
value-level parameter of a type or function. Arrays `[T; N]` are the built-in
example. The code is in `code/rust/examples/ch30_const_generics.rs`:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:dot}}
```

Calling `dot` with two arrays of length 3 instantiates `N = 3`:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:main_dot}}
```

```text
{{#include ../../code/rust/output/ch30_const_generics.txt:1:1}}
```

Arrays of lengths 3 and 4 would be a type error. This is a restricted Π-type:
in effect,
$\mathtt{dot} : \Pi N{:}\mathtt{usize}.\,[\mathtt{i64}; N] \to [\mathtt{i64}; N] \to \mathtt{i64}$.
A matrix type with dimensions in its type follows the same idea:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:matrix}}
```

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:mul}}
```

The `Mul` implementation exists for a left operand `Matrix<R, C>` and a right
operand `Matrix<C, K>` with the *same* `C`. The identity only exists for square
shapes, because its `impl` block is for `Matrix<N, N>`:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:identity}}
```

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:main_matrix}}
```

```text
{{#include ../../code/rust/output/ch30_const_generics.txt:2:5}}
```

The annotations `Matrix<2, 2>` and `Matrix<3, 3>` are checked, not trusted.
Multiplying a 2 × 3 matrix by another 2 × 3 matrix fails with one of the few
Rust type errors that talk about numbers
(`code/rust/compile_fail/ch30_matrix_mismatch.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_matrix_mismatch.rs:mismatch}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_matrix_mismatch.stderr}}
```

The only candidate implementation requires the right operand to be
`Matrix<3, _>`, and `3` is not `2`: E0308, a mismatch between two *values*
inside two types.

### What const generics cannot do

On stable Rust 1.99 a const parameter may only have an integer type, `bool` or
`char`, and inside a type it may only appear on its own, never inside an
expression. So the result type of vertical stacking, with `R1 + R2` rows, cannot
be written (`code/rust/compile_fail/ch30_const_arithmetic.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_const_arithmetic.rs:vstack}}
```

```rust
{{#include ../../code/rust/compile_fail/ch30_const_arithmetic.rs:dependent_param}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_const_arithmetic.stderr}}
```

The first two errors (which have no error code) reject `R1 + R2` inside a
type. The third, E0770, rejects a const parameter whose *type* depends on another
parameter: `DIMS` would be an array of `N` extents, a genuinely dependent kind.
The fourth rejects arrays as the type of a const parameter at all. Lifting these
restrictions is the goal of unstable features, notably `generic_const_exprs`
and `adt_const_params`; they are available only on nightly compilers and still
being designed, so check their current status before relying on them.

On stable Rust, the usual workaround is to let the caller name the result size
and check the arithmetic separately:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:vstack}}
```

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:main_vstack}}
```

```text
{{#include ../../code/rust/output/ch30_const_generics.txt:6:6}}
```

An inline `const { … }` block is evaluated at compile time for each set of
concrete parameters: had the caller asked for a `Matrix<5, 3>`, the build would
stop with error E0080. There is a subtlety, which we checked with rustc 1.99:
the check happens only when the function is *instantiated*, during code
generation, so `cargo check` does not report it and `cargo build` does. The same
technique gives a `first` that rejects empty arrays:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:first}}
```

Compare Lean's `head`, and the `vstack` at the end of this chapter: Lean checks
the arithmetic in the type, for all sizes at once, when the definition is
written. Rust checks each instantiation, after type checking; the generic
function itself is never verified.

### From run-time data to static shapes

Data from a file or a network has a length known only at run time. Rust bridges
the gap the way Lean's `toVec?` did, with a checked conversion:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:try_from}}
```

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:main_parse}}
```

```text
{{#include ../../code/rust/output/ch30_const_generics.txt:8:10}}
```

The difference from Lean is that `N` must be fixed at compile time: the caller
decides that it wants three numbers, and the data either has three or is
rejected. In Lean, as the walkthrough at the end of the chapter shows, the
length itself can come from the data.

### Peano numerals at the type level

Before const generics, Rust programmers encoded numbers as *types*, and the
technique still helps where const generics cannot do arithmetic. Zero is a type
`Z`, and the successor of `N` is `S<N>`
(`code/rust/examples/ch30_type_level_nat.rs`):

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:peano}}
```

`PhantomData<N>` is a zero-sized marker from the standard library that lets a
struct mention a type parameter without storing a value of it, so `S<S<Z>>` is
an empty struct whose *type* encodes the number 2. The trait `Nat` reflects a
type-level number back to a value, computed by recursion on the type.

Addition is a trait with an associated type, defined by two `impl` blocks that
mirror the two equations of addition by recursion on the first argument:

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:plus}}
```

To find `<S<S<Z>> as Plus<M>>::Sum`, the trait solver uses the second `impl`,
which asks for `<S<Z> as Plus<M>>::Sum`, and so on down to `Z`. This is
computation by search, as in a logic programming language such as Prolog: the
`impl` blocks are rules, and the solver chains them.

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:main_arith}}
```

```text
{{#include ../../code/rust/output/ch30_type_level_nat.txt:1:2}}
```

With numbers in types, we can build Rust's version of `Vec α n`:

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:vect}}
```

`Vect<T, N>` stores an ordinary `Vec<T>`; `N` exists only at compile time.
Each signature transcribes a dependent type from the Lean section: `push` goes
from `N` to `S<N>`, `zip` demands the same `N` twice, `append` returns
`<N as Plus<M>>::Sum`, and `head` and `tail` live in an `impl` block for
`Vect<T, S<N>>` only.

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:main_vect}}
```

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:main_append}}
```

```text
{{#include ../../code/rust/output/ch30_type_level_nat.txt:3:7}}
```

The two classic mistakes are type errors. The head of an empty vector is a
method that does not exist (`ch30_head_of_empty.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_head_of_empty.rs:head_of_empty}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_head_of_empty.stderr}}
```

Zipping vectors of lengths 2 and 1 is a mismatch between `S<S<Z>>` and `S<Z>`
(`ch30_zip_lengths.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_zip_lengths.rs:zip_lengths}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_zip_lengths.stderr}}
```

### The limit: the trait solver does not do induction

Our `Plus` recurses on its *first* argument, the mirror image of Lean's `Nat.add`.
So in Rust `Z + m = m` holds by computation (the first `impl` says so), while
`n + Z = n` does not. Try to append an empty vector to a vector of unknown
length and keep the type (`ch30_plus_zero.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_plus_zero.rs:append_nil}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_plus_zero.stderr}}
```

This is the Rust twin of the failed `rfl` in the equality section. For each
concrete `N` the solver would compute `<N as Plus<Z>>::Sum` and find `N`; for a
*generic* `N` it cannot, because proving `n + 0 = n` for all `n` takes
induction, and the trait solver only unfolds `impl` blocks. Rust has no proof
terms either, so there is no `▸`. The compiler's suggestion is revealing: add
the bound `N: Plus<Z, Sum = N>`, that is, *assume* the equation, and let every
caller discharge it with a concrete `N`. Trait bounds are Rust's only proof
obligations, and the solver is its only prover.

### Σ-types in Rust: hiding the index

Vectors of different lengths have different types, so to store them together
we must forget the length: we need
$\Sigma n.\,\mathtt{Vect}\langle T, n\rangle$. A trait object provides it:

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:sigma}}
```

```rust
{{#include ../../code/rust/examples/ch30_type_level_nat.rs:main_sigma}}
```

```text
{{#include ../../code/rust/output/ch30_type_level_nat.txt:8:10}}
```

The trait object is an existential package (Chapter 15): it hides
`Vect<u8, N>`, and with it `N`, but its vtable still computes `len` from the
hidden type. Rust also has a built-in Σ-type over lengths that you use every
day: the slice. Coercing `&[i64; 3]` to `&[i64]` moves the length from the type
into the value, next to the pointer:

```rust
{{#include ../../code/rust/examples/ch30_const_generics.rs:main_sigma}}
```

```text
{{#include ../../code/rust/output/ch30_const_generics.txt:11:11}}
```

The slice reference is twice as large because it *is* a pair: a length $n$ and
a pointer to $n$ elements. `Vec<T>` is the owning version of the same Σ-type,
and converting back to an array with `try_from` is the check-and-transport
pattern of `toVec?`.

### "Parse, don't validate": newtypes as refinement types

A **refinement type** is a type together with a predicate, such as "integers
between 0 and 100"; Lean's subtypes are refinement types with proofs. Rust gets
part of the benefit from a newtype with a private field
(`code/rust/examples/ch30_refinements.rs`):

```rust
{{#include ../../code/rust/examples/ch30_refinements.rs:percent}}
```

Outside the module `percent` the field is invisible, so every `Percent` comes
from `Percent::new`, which checks the bound. Forging one is a privacy error
(`ch30_private_constructor.rs`):

```rust
{{#include ../../code/rust/compile_fail/ch30_private_constructor.rs:forge}}
```

```text
{{#include ../../code/rust/compile_fail/ch30_private_constructor.stderr}}
```

(The compiler's suggestion, making the field public, would dissolve the
invariant.) Shapes can encode invariants too: a vector that stores its first
element separately cannot be empty, so its `first` and `max` need neither
`Option` nor a panic:

```rust
{{#include ../../code/rust/examples/ch30_refinements.rs:non_empty}}
```

The slogan "parse, don't validate", popularized by Alexis King, describes how to
use such types. *Validating* means checking data and getting a `bool`, which is
soon forgotten. *Parsing* means checking it once, at the boundary of the
program, and returning a value of a more precise type that records the result:

```rust
{{#include ../../code/rust/examples/ch30_refinements.rs:validate_vs_parse}}
```

```text
{{#include ../../code/rust/output/ch30_refinements.txt}}
```

`best` needs no checks, because its argument's type rules out both empty input
and out-of-range scores: the same move as `toVec?`, which turned a test into a
more precise type.

The difference is who checks the invariant *inside* the abstraction.
`Percent::half` builds `Percent(self.0 / 2)` directly, and nothing verifies that
the result is in range; if someone changed it to `self.0 * 2`, the program would
still compile. In Lean, `half` had to prove `p.val / 2 ≤ 100`, and the doubling
version would be rejected. Rust's newtype is a refinement type whose proofs are
trusted, behind an encapsulation boundary; Lean's subtype is one whose proofs
are checked.

## Matrices with dimensions in their types

Back to Lean, for the matrices that Rust could multiply but not stack
(`code/lean/Book/Ch30/Matrix.lean`). An `m × n` matrix of integers gives an entry
for every row index in `Fin m` and column index in `Fin n`:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:mat}}
```

The structure gives the type a name of its own, which keeps error messages
readable. `@[ext]` generates an *extensionality* lemma (matrices with equal
entries are equal), which lets the `ext` tactic reduce an equation between
matrices to one between entries.

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:ops}}
```

As in Rust, the inner dimensions of `mul` are one variable `n`. `∑ j, …` is
Mathlib's notation for a sum over all elements of a finite type, here all
`j : Fin n`. `vstack`, the operation Rust could not type, has `m + n` rows; its
body uses `Fin.append`, which combines functions on `Fin m` and `Fin n` into one
on `Fin (m + n)`. To compute and prove with these operations, we state how each
entry is computed, as **simp lemmas**:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:entry_lemmas}}
```

Each lemma holds by definition (`rfl`); its value is the `@[simp]` attribute,
which adds it to the equations that `simp` uses on its own, left to right.
Chapter 31 says more about simp lemmas.

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:samples}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:samples_eval}}
```

Mathlib's notation `![…]` gives a function on `Fin n` by its values. The
results agree with the Rust program, and a mismatch is rejected as in Rust:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:mismatch}}
```

Rust's example *tested* the identity and transpose laws on one pair of
matrices. In Lean we prove them for all matrices of all sizes:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:laws}}
```

- `transpose_transpose` holds by definition: transposing twice swaps the indices
  back, and `rfl` sees it.
- `transpose_mul` starts with `ext k i`, which reduces the equation between
  matrices to one between their entries at row `k` and column `i`. The entry
  lemmas compute both sides, and rewriting with the commutativity of integer
  multiplication, `Int.mul_comm`, makes the two sums identical.
- `mul_one` is a single `simp`: after the entry lemmas, the goal is a sum of
  `M.entry i k * (if k = j then 1 else 0)` over all `k`, and Mathlib's simp set
  knows that such a sum picks out the term `k = j`.
- `mul_assoc` is the real work. `Finset.sum_mul` and `Finset.mul_sum`
  distribute the products into the sums, so both sides become double sums;
  `Finset.sum_comm` swaps the order of summation on the left; `Int.mul_assoc`
  re-brackets the products. Each step is a Mathlib lemma, applied by name.

Stacking distributes over multiplication, and the proof shows how to reason
about an index in `Fin (m + n)`:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:vstack_mul}}
```

`cases i using Fin.addCases` splits a row index of the stacked matrix into two
cases: a row `i` of the top block (the index `Fin.castAdd`, numerically `i`) and
a row `i` of the bottom block (the index `Fin.natAdd`, numerically `m + i`).
In each case Mathlib's simp lemmas about `Fin.append` select the right block, and
the entry lemmas finish.

### In Mathlib

Mathlib defines `Matrix m n α := m → n → α`. The difference from our `Mat` is
that the indices `m` and `n` are arbitrary *types* (finite ones, for
multiplication), not numbers: `Matrix (Fin 2) (Fin 3) ℤ` is our `Mat 2 3`. The
notation `!![…]` separates rows with semicolons:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:mathlib}}
```

Our multiplication is Mathlib's, entry by entry, and that lets us borrow
Mathlib's theorems:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:to_matrix}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:transfer}}
```

`apply toMatrix_injective` reduces the goal to an equation between Mathlib
matrices, `rw` pushes `toMatrix` inside the products, and Mathlib's
`Matrix.mul_assoc` closes the goal: a pattern you will use often with
libraries.

Indexing by types instead of numbers has a beautiful consequence for stacking.
Mathlib's version of `vstack` is `Matrix.fromRows`, and its result is indexed by
the *sum type* of the two row types:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:from_rows}}
```

A row of the stack is either a row of the top block (`Sum.inl i`) or a row of the
bottom block (`Sum.inr i`), and no arithmetic appears in the type at all: the
`m + n` of our `vstack` has become `m₁ ⊕ m₂`, and the case split that
`Fin.addCases` performed is now an ordinary `match` on a sum. Mathlib's lemma
`Matrix.fromRows_mul` is the analogue of our `vstack_mul`. This is the algebra of
types from Chapter 11 at work: $|m_1 \oplus m_2| = |m_1| + |m_2|$, so the sum type
is the type-level version of addition, and it needs no equations about `+` to
use.

## Putting it together: shapes from data

Let us combine everything into one small program: read two matrices whose sizes
are known only at run time, and multiply them if their shapes allow it. In Rust,
`Matrix<R, C>` cannot help, because `R` and `C` must be fixed at compile time; a
Rust program would use a dynamic matrix type with a run-time check in every
multiplication. Lean keeps the static guarantee even though the shapes come from
data. The first step reads a list of rows into a matrix of a given shape, if it
has that shape:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:lists}}
```

`ofLists?` tests a decidable proposition: there are `m` rows, and every row has
length `n`. In the `then` branch its proof `h` is used twice: `omega` finds the
first half in the context to prove that row index `i` is in range, and `h.2`
applied to the selected row proves that column index `j` is. Without the test,
the indexing would not type-check.

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:of_lists_eval}}
```

The second step hides the shape, because before reading the data we do not know
it: a matrix of *some* shape is a Σ-type with two indices. Multiplying two such
matrices tests the inner dimensions, transports, and multiplies:

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:some_mat}}
```

```lean
{{#include ../../code/lean/Book/Ch30/Matrix.lean:some_mat_eval}}
```

Follow the types through `SomeMat.mul`. The arguments are dependent pairs
`⟨m, n, A⟩` and `⟨n', p, B⟩` with `A : Mat m n` and `B : Mat n' p`, so `A * B`
does not type-check: `n` and `n'` are different variables. The dependent `if`
decides `n' = n` at run time, and in the `then` branch its proof `h` transports
`B` to type `Mat n p`; from there on, the multiplication is the
dimension-checked `*` whose laws we proved for all sizes. Every check happens
once, where the data enters, and its result is recorded in a type. This is the
pattern of the whole chapter: Σ for data whose shape is discovered at run time,
decidable tests that produce proofs, transport into the precise types, and
Π-typed functions that rely on them.

## Common confusions

**"Dependent types means types are computed at run time."** No. Type checking
still happens before the program runs, and types are still erased afterwards.
The type checker reasons about values *symbolically*: it knows that
`replicate n x` has length `n` for every `n`, without knowing `n`. Run-time
values enter types only through variables, as in `toVec?`.

**"If `rfl` fails, the equation is false."** `rfl` only checks definitional
equality: whether the two sides compute to the same thing. `0 + n = n` is true
and needs a proof by induction. When `rfl` fails on a statement you believe,
look at how the functions involved recurse.

**"`(5 : Fin 3)` is a type error."** It is not: numerals of type `Fin n` wrap
around modulo `n`. The type promises that an index is in range, not that it is
the index you meant. Use `⟨5, proof⟩` when an out-of-range number should be an
error.

**"Const generics are dependent types."** They are a first step. The values in
Rust's types must be known at compile time, may only be integers, `bool` or
`char`, cannot be combined with arithmetic on stable Rust, and come with no
proofs. Lean's indices can be any terms, including variables bound at run time,
with the whole apparatus of propositional equality.

**"Σ and ∃ are the same thing."** They correspond under Curry–Howard, but Lean
keeps them apart (Chapter 10): from a `Σ n, Vec α n` you can extract the length
and compute with it, from a proof of `∃ n, P n` you cannot.

## Summary

- A type **depends** on a term when it mentions it. A function that returns
  types is a **type family**; Lean has them natively because `Type` is itself a
  type.
- **Π-types** $\Pi x{:}A.\,B$ are dependent functions; their elimination rule
  substitutes the argument into the result type. $A \to B$ is the special case
  where $B$ does not mention $x$. Under Curry–Howard Π is $\forall$.
- **Σ-types** $\Sigma x{:}A.\,B$ are dependent pairs; $A \times B$ is the special
  case. A Rust enum is a Σ-type over its finite set of variants; slices and
  `Vec` are Σ-types over lengths; trait objects hide indices existentially.
- In an inductive family, **parameters** are uniform across constructors and
  **indices** are chosen by each constructor. Dependent pattern matching refines
  indices and discards impossible cases, which makes `head` total and `zip`
  length-preserving.
- `Fin n` and Lean's `Vector α n` turn bounds checks into proof obligations;
  `v[i]`, `v[i]'h`, `v[i]?`, `v[i]!` and the dependent `if h : …` give the
  choice between static proof, `Option`, panic and run-time test with evidence.
- Equality is an inductive family with one constructor; its elimination rule is
  **transport** (`▸`, `subst`, `rw`). **Definitional** equality is decided by
  computation and depends on how functions recurse (`n + 0 = n` by `rfl`,
  `0 + n = n` by induction); **propositional** equality is anything you can
  prove. Indices that follow the recursion avoid transports.
- In the **λ-cube**, Rust has λ2 and fragments of λω and λP; Lean's type theory
  goes beyond the corner λC with inductive types and universes.
- Rust's approximations: const generics (no arithmetic, no proofs on stable),
  type-level Peano numerals (computation by trait resolution, no induction),
  Σ-types as slices and trait objects, and newtypes with private fields as
  refinement types whose invariants are trusted rather than proved.

## Exercises

1. **Reverse, twice.** In a scratch copy of `Vectors.lean`, define
   `snoc : Vec α n → α → Vec α (n + 1)`, which adds an element at the end, and use
   it to define `reverse : Vec α n → Vec α n`. Then try to define the fast
   version `revAcc : Vec α n → Vec α m → Vec α (n + m)` with an accumulator, and
   explain the error.
   *Hint:* `snoc` and `reverse` type-check without any proof, because their
   indices follow the recursion. For `revAcc`, the recursive call
   `revAcc xs (cons x acc)` has length `n + (m + 1)`, but the clause needs
   `(n + 1) + m` (Lean's message may point at `xs` instead, because it matches
   the expected type first). Transport along `Nat.succ_add_eq_add_succ n m`,
   which states `n.succ + m = n + m.succ`, and in the `nil` case along
   `Nat.zero_add m`.

2. **Type-level multiplication.** In `ch30_type_level_nat.rs`, define a trait
   `Times<M>` with an associated type `Product`, using the equations
   $0 \cdot m = 0$ and $(n + 1) \cdot m = m + n \cdot m$. Check with `short_name`
   that the compiler computes $2 \cdot 3 = 6$.
   *Hint:* the second `impl` needs two bounds, one for the recursive product and
   one to add `M` to it: `impl<N: Times<M>, M> Times<M> for S<N> where M: Plus<<N as Times<M>>::Product>`.

3. **The transpose of the identity.** Prove in Lean that
   `(Mat.one n).transpose = Mat.one n`, and that
   `(M * N).transpose.transpose = M * N` (one of the two needs no work at all).
   *Hint:* for the first, `ext i j` and then `simp [eq_comm]`; the entry of the
   transposed identity at `(i, j)` is `if j = i then 1 else 0`.

4. **Π and Σ over `Bool`, by hand.** Write, in Lean, functions
   `toPair : ((b : Bool) → Answer b) → ℕ × String` and
   `fromPair : ℕ × String → ((b : Bool) → Answer b)`, and prove that
   `toPair (fromPair p) = p`. Then do the same for `(b : Bool) × Answer b` and
   `ℕ ⊕ String`. On paper, explain what these two isomorphisms say about the
   names "product" and "sum".
   *Hint:* `fromPair p` is defined by pattern matching on the Boolean:
   `fun | true => p.1 | false => p.2`. The first round trip holds by `rfl`
   after `cases p`.

5. **A `NonEmpty` with a proof.** Define
   `NonEmptyList α := { xs : List α // xs ≠ [] }` and a total function
   `head : NonEmptyList α → α`. Compare with `NonEmpty<T>` in
   `ch30_refinements.rs`: which invariants does each version check, and where?
   Does the Lean version need to hide anything?
   *Hint:* match on the pair: `| ⟨[], h⟩ => absurd rfl h | ⟨x :: _, _⟩ => x`.
   In the first case `h : [] ≠ []`, and `absurd rfl h` derives anything from
   the contradiction.

6. **Where does the arithmetic go?** In Rust, write a function
   `hstack<const R: usize, const C1: usize, const C2: usize, const C: usize>` that
   places two matrices side by side, with the `const` assertion technique of
   `vstack`. In Lean, define `hstack` on `Mat` with result type
   `Mat m (n₁ + n₂)`. Which of the two can be wrong for some sizes without the
   compiler noticing until the function is used?
   *Hint:* in Lean, use `Fin.append` on each row: `⟨fun i => Fin.append (A.entry i) (B.entry i)⟩`.
