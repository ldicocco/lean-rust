# Copy, Clone and the Exponential

The affine λ-calculus of Chapter 22 is strict to the point of being useless. It
cannot use an integer twice. It cannot call a function twice: at the end of
Chapter 22, the Lean version of the upload program could not even send two
messages, because `send` was a variable of the context and every variable is a
resource. A real language needs some values to be freely duplicable, and the
interesting question is which ones, and on what terms.

Linear logic answers with a **modality**, written $!A$ and read "of course $A$":
a marker on the formulas that may be duplicated and discarded at will. Rust
answers with two traits and a library type. `Copy` marks the types whose values
are duplicated implicitly and for free; `Clone` marks the types that can be
duplicated explicitly, by calling a method that may do real work; and `Rc` and
`Arc` share a value among several owners and keep count. These are not three
unrelated features. They are three ways of bringing back the structural rule that
Chapter 22 removed, contraction, each with a different price.

This chapter presents the exponential modality and its rules, shows that `Copy`
behaves like it and that Rust's rules for `Copy` are its rules in disguise,
contrasts `Copy` with `Clone` and `Rc`, and then makes the connection formal:
$\lambda^{\mathsf{aff}}$ extended with a `Copy` predicate, a splitting rule that
may duplicate `Copy` variables, and a generalized usage theorem proved in Lean.

**In this chapter you will learn:**

- the exponential modality $!A$ and its four rules (weakening, contraction,
  dereliction, promotion), and what each one says about resources;
- why `Copy` is contraction for free on a class of types, and why the class is
  what it is: all fields `Copy` (E0204), no destructor (E0184), `&T` but not
  `&mut T`;
- why `Clone` is a different thing: an explicit duplication *term*, with a cost
  and possibly an effect;
- how `Rc` and `Arc` share instead of duplicating, and why counting forbids them
  from being `Copy`;
- the formal statement: $\lambda^{\mathsf{aff}}$ with a `Copy` predicate and a
  splitting rule S-Both, and the generalized usage theorem, proved in Lean with
  multiplicities in $\mathbb{N} \cup \{\infty\}$;
- why functions cannot be `Copy` in general, as a Lean proof that preservation
  would fail;
- how the `affine` crate checks `Copy`, `Clone`, `Rc` and `#[derive(Copy)]`.

## Too affine to be useful

Here is the smallest program that $\lambda^{\mathsf{aff}}$ rejects and every
programmer would accept, checked by the `affine` crate in the pure discipline of
Chapter 22 (the example is `code/rust/crates/affine/examples/ch23_copy.rs`):

```text
{{#include ../../code/rust/output/ch23_copy.txt:1:10}}
```

The message is correct for the calculus: no type is `Copy` there, and the
proof of Chapter 22 that $\lambda x.\,(x, x)$ has no type did not depend on the
type of $x$ at all. Rust, of course, accepts `twice`. To accept it, a type system
has two options, and Rust uses both:

1. let certain types bring contraction back *implicitly*, so that using a
   variable does not consume it;
2. provide *explicit* duplication functions, $\tau \multimap \tau \otimes \tau$,
   which the programmer calls when needed.

The first option is the exponential modality of linear logic, and it is `Copy`.
The second is `Clone`.

## The exponential modality

Girard's linear logic keeps an assumption from being duplicated or discarded,
and then adds a way to say that a particular assumption *may* be. The formula
$!A$ means "as many $A$s as you need, including none". On types, $!\tau$ is the
type of values that may be used any number of times. Four rules say what that
means. We write them as typing rules, with ${!\Gamma}$ for a context in which
every type has the form $!\tau$:

$$
\dfrac{\Gamma \vdash e : \rho}{\Gamma, x : {!\tau} \vdash e : \rho}\;\textsf{!-Weak}
\qquad
\dfrac{\Gamma, x : {!\tau}, y : {!\tau} \vdash e : \rho}{\Gamma, z : {!\tau} \vdash e[z/x, z/y] : \rho}\;\textsf{!-Contr}
$$

$$
\dfrac{\Gamma \vdash e : {!\tau}}{\Gamma \vdash \mathsf{derelict}\,e : \tau}\;\textsf{Dereliction}
\qquad
\dfrac{{!\Gamma} \vdash e : \tau}{{!\Gamma} \vdash {!e} : {!\tau}}\;\textsf{Promotion}
$$

- **!-Weak** says that a $!\tau$ may go unused. In linear logic this is the only
  form of weakening; in affine logic every variable may go unused already, so the
  rule adds nothing new.
- **!-Contr** is contraction, restricted to $!$-types: two variables of type
  $!\tau$ may be identified, so one $!\tau$ serves two uses.
- **Dereliction** uses a $!\tau$ as an ordinary $\tau$, once. You give up the
  right to duplicate it and get the value.
- **Promotion** is the subtle one. It builds a duplicable value $!e$, but only
  from a context in which *everything* is duplicable. The reason is a resource
  argument. If $e$ used a non-duplicable resource $s$, then every copy of $!e$
  would need its own $s$, and duplicating $!e$ would duplicate $s$. So a
  duplicable value may only be built out of duplicable things.

Together they give the derivations you would expect. From $x : {!A}$,
contraction and two derelictions give a pair $A \otimes A$; weakening gives
$\mathbf{1}$. From $x : A$ alone, nothing gives $!A$: promotion needs the whole
context to be of the form ${!\Gamma}$. Girard also showed that ordinary
intuitionistic logic can be translated into linear logic by reading an
intuitionistic implication $A \to B$ as $!A \multimap B$: an ordinary function is
a linear function whose argument may be used any number of times.

Here is how the four rules correspond to Rust. The rest of the chapter explains
every row:

| Linear logic | Rust |
|---|---|
| $!\tau$ | a type `T` with `T: Copy` |
| !-Contr | a `Copy` value is copied implicitly at every use |
| !-Weak | discarding a `Copy` value is free: it has no destructor |
| Dereliction | a `Copy` value can be used like any other value |
| Promotion | `#[derive(Copy)]` requires every field to be `Copy` |
| a term $\tau \multimap \tau \otimes \tau$ | `Clone::clone`, called explicitly |

![Three ways to duplicate in Rust. Copy types are duplicated implicitly and for free; Clone types explicitly, with a call that may cost something; every other type is affine. The exponential of linear logic corresponds to Copy.](../images/ch23-duplication.svg)

In the language of Chapter 19, a $!$-type comes with a copy map
$A \to A \otimes A$ and a discard map $A \to \mathbf{1}$ that fit together: the
comonoid structure that Chapter 19 found on the types that have a diagonal. We
stay with type theory here.

## `Copy`: contraction for free

In Rust, whether `let b = a;` moves `a` or copies it is decided by the type of
`a`, not by anything written in the program. This chapter's Rust example is
`code/rust/examples/ch23_copy_clone.rs`:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:copy_vs_move}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:1:1}}
```

The two `let`s have the same syntax and different rules. For `i32`, the compiler
applies contraction silently: `a` stays usable. For `String`, it applies the
affine rule: `s` is moved, and a later use would be E0382.

There is one difference between `Copy` and $!$ that shapes everything else.
$!\tau$ is a *type constructor*: from any type $\tau$ you can form $!\tau$ and
then build its values by promotion. `Copy` is a *property* of a type: a type is
`Copy` or it is not, and there is no `!String`. A `Copy` type behaves as if it
were already of the form $!\tau$. Contraction and weakening happen at every use
without being written, and dereliction is invisible, because a value of a `Copy`
type can always be used as an ordinary value. What remains of promotion is the
rule that decides which types may be `Copy`.

### Which types are `Copy`

| Type | `Copy`? | Why |
|---|---|---|
| `i32`, `bool`, `char`, `f64`, `()` | yes | plain bits, nothing owned |
| `&T`, for every `T` | yes | a shared read permission |
| `&mut T` | no | a unique permission |
| `(A, B)`, `[T; N]`, `Option<T>` | if the components are | promotion |
| a struct or enum | if it derives `Copy` and all fields are `Copy` | promotion |
| `fn` items and `fn` pointers | yes | they capture nothing |
| a closure | if everything it captures is `Copy` or a shared reference | promotion |
| `String`, `Vec<T>`, `Box<T>` | no | they own a heap allocation |
| any type with a `Drop` impl | no | see below |

A copy is a bitwise copy of the value, the same operation as a move. What
differs is only whether the source stays usable afterwards:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:dup}}
```

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:copies}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:2:4}}
```

`dup_copy` is $\lambda x.\,(x, x)$, the term that Chapter 22 proved untypable, and
its bound `T: Copy` is what makes it legal: Rust's generics have an explicit
contraction permission. The copy `q` has the same bits as `p` and lives in a
different place (`std::ptr::eq` compares addresses). Copying a shared reference
duplicates the *reference*: the two copies point to the same `String`. That is
why `&T` can be `Copy` for every `T`: a shared reference is a permission to read,
and handing out more read permissions does not duplicate the data. Chapter 26
takes this further, and shows that it is precisely why affinity alone cannot
explain references.

### Promotion: every field must be `Copy`

A struct can derive `Copy` only if all its fields are `Copy`:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:point}}
```

```rust
{{#include ../../code/rust/compile_fail/ch23_copy_string_field.rs:reading}}
```

```text
{{#include ../../code/rust/compile_fail/ch23_copy_string_field.stderr}}
```

This is promotion. To make `Reading` duplicable, every resource it is built from
must be duplicable, and a `String` is not: copying a `Reading` bit by bit would
give two owners of one heap buffer, and two frees. The rule is not specific to
`derive`; a hand-written `impl Copy for Reading {}` is rejected with the same
error.

### No destructors

A type with a destructor cannot be `Copy`, even if all its fields are:

```rust
{{#include ../../code/rust/compile_fail/ch23_copy_with_drop.rs:token}}
```

```text
{{#include ../../code/rust/compile_fail/ch23_copy_with_drop.stderr}}
```

`Copy` makes contraction implicit, and a destructor makes weakening an action
(Chapter 24). Put the two together and every silent copy would bring one more
silent destructor call: a token copied three times would be released four times.
In the rules above, that is !-Weak: discarding a $!\tau$ must be free, and a
value whose discarding runs code is not a $!\tau$. This is the reason Chapter 24
gives for E0184.

### `Copy` needs `Clone`

In the standard library the trait is declared as `pub trait Copy: Clone`, so
deriving `Copy` without `Clone` is an error too (E0277, "the trait bound
`Point: Clone` is not satisfied"). Any type that may be duplicated implicitly may
also be duplicated explicitly, and the documentation of `Clone` asks that, for a
`Copy` type, `clone` be equivalent to a copy (`unsafe` code is not allowed to rely
on that). We will prove the type-theoretic version of "`Copy` implies `Clone`"
in Lean below.

### `&mut T` is not `Copy`

A mutable reference is a *unique* permission to read and write. Duplicating it
would give two writers, which is exactly what the borrow checker exists to
prevent, so `&mut T` is affine:

```rust
{{#include ../../code/rust/compile_fail/ch23_mut_ref_not_copy.rs:writers}}
```

```text
{{#include ../../code/rust/compile_fail/ch23_mut_ref_not_copy.stderr}}
```

There is a caveat that every Rust programmer has run into. A `&mut` reference
*can* be passed to two calls in a row:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:reborrow}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:12:12}}
```

That is not a copy. Where a `&mut` reference is expected, the compiler passes a
fresh *reborrow* `&mut *log`, a new unique reference that lives only as long as
the call, and `log` becomes usable again afterwards. Reborrowing belongs to the
calculus of borrows, and Chapter 28 derives this very program. (It is also why
the tuple `(a, w)` in place of `(a, b)` above gets a slightly different message,
"borrow of moved value": the compiler tries to reborrow `w` for the tuple.)

### Functions

`fn` items and function pointers are `Copy`: a function that captures nothing
can be duplicated freely, even as a value (`let g = send; g(a); g(b)` compiles).
That is what justifies the `affine` crate in treating declared functions as
constants that can be called again and again. A closure is a function *with captured values*, and it is
`Copy` exactly when what it captures may be duplicated: promotion again. A
closure that has captured a `String` by value is not `Copy`, and if calling it
consumes the `String`, it is only `FnOnce`, the $\multimap$ of Chapter 22. In
$\lambda^{\mathsf{aff}}$ the type $\tau \multimap \sigma$ says nothing about what
a function captured, so the safe choice is never to make a function type `Copy`.
We will see in Lean what goes wrong otherwise.

## `Clone`: duplication as a term

`Clone` has one method, `fn clone(&self) -> Self`. It is an ordinary function
that the programmer calls, and it may do anything: allocate a new buffer and copy
bytes into it, increment a counter, log a message. The difference between `Copy`
and `Clone` is the difference between a structural rule and a term:

| | `Copy` | `Clone` |
|---|---|---|
| status | a structural rule (S-Both below) | a term, $\tau \multimap \tau \otimes \tau$ |
| written in the program | never | always: `x.clone()` |
| cost | a bitwise copy | anything |
| effects | none | possible |

In the calculus, a `Clone` type comes with a constant
$\mathsf{dup}_\tau : \tau \multimap \tau \otimes \tau$, and a program that needs
two copies of $x$ writes $\mathtt{let}\ (x_1, x_2) = \mathsf{dup}_\tau\,x\ \mathtt{in}\ \dots$,
using $x$ once. (Rust's `clone` takes `&self`, a borrow, and leaves the original
where it was, so the second copy is the original itself; borrowing is Part VI,
and $\tau \multimap \tau \otimes \tau$ is its affine shadow.) The generic
function `dup_clone` above is exactly this term.

The call is visible in the source, and so is its cost:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:tracked}}
```

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:clones}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:5:6}}
```

Cloning a `String` allocates a new buffer (the two strings are equal, their
buffers are not the same), and cloning a `Specimen` runs code that updates a
counter: two calls to `dup_clone`, two clones. Neither could happen silently,
which is the point. A type for which duplication has a cost or an effect should
make every duplication visible, and Rust achieves that by making such a type
`Clone` but not `Copy`.

Not every type is `Clone`. A file handle is not: duplicating a handle to an open
file would need a decision about what two owners of one file descriptor mean
(the standard library's `File` offers a separate `try_clone` for that). For such
types the calculus has no $\mathsf{dup}_\tau$ at all, and they stay strictly
affine.

## `Rc` and `Arc`: counted sharing

`Rc<T>` takes a third way. It does not duplicate the `T` at all. It puts the
`T` in a heap allocation together with a counter, and an `Rc<T>` is a pointer to
that allocation. `Rc::clone` copies the pointer and increments the counter; each
drop of an `Rc` decrements it; when the counter reaches zero, the `T` is dropped
and the allocation freed:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:rc}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:7:10}}
```

So `Rc` turns contraction into bookkeeping. Every duplication of the pointer is
recorded (the count goes up), and so is every discard (the count goes down). The
shared `T` itself is never duplicated. An `Rc<T>` dereferences to a shared
reference `&T`, so the owners can all read the value; to mutate it you need
either proof that you are the only owner (`Rc::get_mut` checks the count) or the
interior mutability of Chapter 26.
In the vocabulary of this chapter, `Rc<T>` is *not* $!T$: it makes both
contraction and weakening *explicit and counted*, where $!$ makes them silent.

That is also why `Rc<T>` cannot be `Copy`, whatever `T` is. A bitwise copy of the
pointer would not increment the counter, and the two copies would later
decrement it twice. And `Rc` has a destructor, the decrement, which E0184
forbids anyway. rustc knows the situation well enough to give it a special
message:

```rust
{{#include ../../code/rust/compile_fail/ch23_rc_not_copy.rs:share}}
```

```text
{{#include ../../code/rust/compile_fail/ch23_rc_not_copy.stderr}}
```

`Arc<T>` is the same with an atomic counter, so that clones can be sent to other
threads:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:arc}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:11:11}}
```

Each thread receives its own clone of the pointer and drops it when it finishes,
so after the joins the count is back to 1. Counting has a known blind spot: two
`Rc`s that point to each other keep each other's counts above zero forever. Such
a cycle is never freed, and Chapter 24 explains why that is a leak and not a
safety problem.

## The formal statement

We now extend $\lambda^{\mathsf{aff}}$ to make all of this precise. The extension
has two parts, and the typing rules of Chapter 22 do not change at all.

**A `Copy` predicate on types.** Fix a set $\mathcal{C}$ of base types that are
`Copy` (for us, the scalar types `i32`, `u64`, `bool`, `char`). Then

$$
\dfrac{b \in \mathcal{C}}{\mathsf{Copy}(b)}
\qquad
\dfrac{}{\mathsf{Copy}(\mathbf{1})}
\qquad
\dfrac{\mathsf{Copy}(\tau) \qquad \mathsf{Copy}(\sigma)}{\mathsf{Copy}(\tau \otimes \sigma)}
\qquad
\dfrac{\mathsf{Copy}(\tau) \qquad \mathsf{Copy}(\sigma)}{\mathsf{Copy}(\tau \oplus \sigma)}
$$

There is no rule for $\tau \multimap \sigma$ and none for
$\tau \mathbin{\&} \sigma$. A function value may hold captured resources, and an
offer is a suspended computation over resources; in both cases the type does not
mention them, so the type cannot promise that duplicating the value is harmless.

**A fourth splitting rule.** A `Copy` variable may go to *both* sides of a split:

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \mathsf{Copy}(\tau)}{\Gamma, x : \tau = (\Gamma_1, x : \tau) \uplus (\Gamma_2, x : \tau)}\;\textsf{S-Both}
$$

That is the whole extension. Compare it with the rules of $!$:

- S-Both is !-Contr, folded into the splitting relation instead of being a rule
  of its own. Wherever the rules of Chapter 22 split a context, a `Copy` variable
  may now be given to both premises.
- !-Weak is already there, as for every variable of an affine calculus.
- Dereliction is invisible: a `Copy` variable is still used by A-Var, like any
  other.
- Promotion survives as the definition of $\mathsf{Copy}$: a compound type is
  `Copy` only if it is built from `Copy` types. That is `#[derive(Copy)]`'s rule.

Chapter 28 uses exactly these four splitting rules, S-Empty, S-Left, S-Right and
S-Both, for its calculus of borrows, where shared references are `Copy` and
mutable references are not.

### In Lean

The Lean file of this chapter, `code/lean/Book/Ch23/Exponential.lean`, imports
Chapter 22's files and reuses their types, terms and `uses` function. The `Copy`
predicate is a function to `Bool`, decided by the structure of the type, as
rustc decides it:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:is_copy}}
```

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:copy_examples}}
```

Each `example` is proved by `rfl`: Lean evaluates `isCopy` and finds `true` or
`false`. The theorem `isCopy_tensor` is promotion for pairs, and `simp [isCopy]`
proves it by unfolding the definition and simplifying the Boolean conjunction.

The splitting relation gets the fourth constructor. We make the predicate a
*parameter* `cp` of the relation, so that at the end of the chapter we can compare
the right choice of `Copy` types with a wrong one; the book's choice is `isCopy`:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:split_c}}
```

The typing rules are those of Chapter 22, with `SplitC cp` in place of `Split`:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:has_type_c}}
```

Since the new splitting relation contains the old one, every derivation of
Chapter 22 is still a derivation, whatever `cp` is; the proof is one line per
rule:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:embed}}
```

And programs that Chapter 22 rejected are now accepted, when the types allow it:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:copy_dup}}
```

`copy_dup` is the type-theoretic version of "`Copy` implies `Clone`": for every
`Copy` type, $\lambda x.\,(x, x)$ is a closed term of type
$\tau \multimap \tau \otimes \tau$, the type of $\mathsf{dup}_\tau$. A `Copy`
type needs no library function for duplication; the language provides one. The
derivation is Chapter 22's failed derivation of `dup`, with the split that did
not exist now supplied by `.both hc .nil`.

### The generalized usage theorem

Chapter 22's usage theorem said that every variable is used at most once. With
S-Both that is false, and `twice` is the counterexample. The right statement
gives each variable a **multiplicity**: one for an ordinary variable, unbounded
for a `Copy` variable, zero for a variable the term did not receive.

> **Theorem (generalized usage).** If $\Gamma \vdash e : \tau$ in
> $\lambda^{\mathsf{aff}}$ with `Copy`, then every variable of $\Gamma$ whose
> type is not `Copy` occurs in $e$ at most once (with the counting convention of
> Chapter 22), and a variable that is not in $\Gamma$ does not occur at all.

To state the multiplicities in Lean we need a number system with an "unbounded"
element. Mathlib provides it: `ℕ∞` (`ENat`), the natural numbers extended with a
top element `⊤`, with an addition in which $n + \top = \top$. We import only
`Mathlib.Data.ENat.Monoid`, which provides `ℕ∞`'s arithmetic and ordering, and
one lemma file about casts:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:avail_c}}
```

The key lemma changes from an equation to an inequality. A split now hands out *at
most* what the context had, because the `both` rule gives `⊤` to both sides of
a position that had `⊤`, and $\top + \top = \top$:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:split_c_avail}}
```

The proof is the same as Chapter 22's, with one more case. In the `both` case at
position 0, `simp [availC, hc]` uses the hypothesis `hc : cp τ = true` to rewrite
each multiplicity to `⊤`, and Mathlib's simplification lemmas for `ℕ∞` know that
$\top + \top \le \top$. The theorem itself also follows Chapter 22's proof
step by step:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:usage_c}}
```

The counts `uses i e` are natural numbers, and the multiplicities live in `ℕ∞`,
so the statement casts the count with `(uses i e : ℕ∞)`. The proof then has to
move between the two. In the `app` case, `Nat.cast_add` rewrites the cast of a
sum as a sum of casts; `add_le_add` adds the two induction hypotheses, giving
$u_1 + u_2 \le a_1 + a_2$; and `.trans` chains that with the splitting lemma
$a_1 + a_2 \le a$. Chapter 22's `omega` cannot be used here, because it works
with natural numbers and integers only, and `⊤` is neither. For the `max` of the
sharing rules there is a small helper, `cast_max_le`, proved just before the
theorem with Mathlib's fact that the cast from `ℕ` to `ℕ∞` is monotone. In the
`var` case, `split <;> simp` considers the two possible multiplicities of the
variable, `⊤` and `1`, and checks that `1` is below each.

The familiar form is a corollary, and so is the fact that `dup` is still
untypable at a non-`Copy` type:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:non_copy_once}}
```

For a non-`Copy` variable, `simp [availC, hi, hσ]` turns the theorem's right-hand
side into `1`, leaving `(uses i e : ℕ∞) ≤ 1`. The tactic `exact_mod_cast`
removes the casts from that hypothesis and from the goal, and finds that they
are the same statement about natural numbers.

The theorem holds for *every* predicate `cp`, not just for `isCopy`. That is
worth pausing on, because it means that the usage theorem alone cannot tell a
good choice of `Copy` types from a bad one. The next section shows what can.

### Why functions are not `Copy`

Suppose we made every function type `Copy`, whatever the function captures.
Here is a program that uses that freedom, with $s : \mathsf{String}$ in the
context:

$$
\mathtt{let}\ f = \lambda u{:}\mathbf{1}.\,s\ \mathtt{in}\ (f\,(),\ f\,())
$$

The closure $f$ captures $s$; the body calls $f$ twice. With function types
`Copy`, the `let` body may give $f$ to both components of the pair, and $s$
occurs once in the program text, so everything type-checks. Now run one step:
the `let` substitutes the closure for $f$, and the result is

$$
((\lambda u{:}\mathbf{1}.\,s)\,(),\ (\lambda u{:}\mathbf{1}.\,s)\,())
$$

in which $s$ occurs twice and must be given to both components. String is not
`Copy`, so this term has no type. A well-typed program stepped to an ill-typed
one: **preservation fails**. In Lean:

```lean
{{#include ../../code/lean/Book/Ch23/Exponential.lean:promotion}}
```

The first half of `promotion_matters` is the derivation of the program, by
hand. The split `.left .nil` gives `s` to the closure, the split
`.both rfl (.hole .nil)` gives the closure `f` to both calls (allowed, since
`fnCopy` says yes to function types), and each call's split `.left (.hole .nil)`
gives `f` to the function position. The second half is the generalized usage
theorem applied to the reduct: variable 0, which is `s`, occurs twice and has
multiplicity 1. The last theorem shows that the real predicate rejects the
program from the start: after inverting the `let`, and the λ to learn that `f` has
a function type, the usage theorem finds the non-`Copy` variable `f` used twice.

This is promotion, seen from the other side. A value may be made duplicable only
if everything it holds is duplicable. Rust's rule for closures, `Copy` only when
every capture is, is that rule; in $\lambda^{\mathsf{aff}}$, where a function
type does not record its captures, the only safe rule is "never".

## `Copy` in the `affine` crate

The crate implements the extension with a `Discipline` switch: `Affine` is
Chapter 22's calculus, and `Copy` turns on the predicates of `copy.rs`, which
follow Rust's rules rather than the minimal calculus (they include references,
structs and `Rc`):

```rust
{{#include ../../code/rust/crates/affine/src/copy.rs:is_copy}}
```

```rust
{{#include ../../code/rust/crates/affine/src/copy.rs:is_clone}}
```

The checker uses `is_copy` in one place, the use of a place that we saw in
Chapter 22: a use of a `Copy` place records no move, which is rule S-Both in
algorithmic form (the variable stays in the leftovers, for the next subterm to
use). A call `x.clone()` requires `is_clone` and reads `x` without moving it.
With the `Copy` discipline, `twice` is accepted, and its derivation shows the
same variable in both premises of A-Pair:

```text
{{#include ../../code/rust/output/ch23_copy.txt:11:15}}
```

The crate also accepts the programs of `ch23_copy.aff`, each of which the pure
affine discipline rejects (the example checks that too):

```text
{{#include ../../code/rust/crates/affine/examples/programs/ch23_copy.aff}}
```

```text
{{#include ../../code/rust/output/ch23_copy.txt:16:21}}
```

`values` combines `Copy` with Chapter 22's places: copying the `Copy` field
`r.value` twice moves nothing, so `r` is still whole afterwards. Rust accepts the
same function. Finally, the checks that rustc makes on `#[derive(Copy)]` are
implemented as a direct transcription of the three rules:

```rust
{{#include ../../code/rust/crates/affine/src/copy.rs:check_derives}}
```

Here are the crate's errors for the program `ch23_errors.aff`, next to rustc's
from earlier in the chapter. Promotion:

```text
{{#include ../../code/rust/output/ch23_copy.txt:23:29}}
```

The destructor:

```text
{{#include ../../code/rust/output/ch23_copy.txt:31:43}}
```

Both match rustc's diagnostics label for label. (rustc points the note at the
`fn drop` inside the `impl`; the crate's `impl Drop for Token {}` has no body, so
it points at the whole `impl`.) A mutable reference used twice is an ordinary
E0382:

```text
{{#include ../../code/rust/output/ch23_copy.txt:45:53}}
```

A file handle cannot be cloned:

```text
{{#include ../../code/rust/output/ch23_copy.txt:55:61}}
```

And an `Rc` used twice gets the generic E0382, with a hint that `Clone` is
available. rustc's special wording for `Rc` ("the type `Rc` does not implement
`Copy`", "clone the value to increment its reference count") says the same thing
more helpfully:

```text
{{#include ../../code/rust/output/ch23_copy.txt:63:73}}
```

## Putting it together: a measurement session

Here is a program from a laboratory, in which all three kinds of duplication meet.
A device is measured twice on the same channel, and both samples are labeled with
the operator's name:

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:session}}
```

```rust
{{#include ../../code/rust/examples/ch23_copy_clone.rs:session_run}}
```

```text
{{#include ../../code/rust/output/ch23_copy_clone.txt:13:15}}
```

Each variable gets the treatment its type calls for.

- `ch: i32` is `Copy`. It is used twice, once per measurement, and nothing is
  written to make that possible: contraction for free.
- `a` and `b` are `Sample`s, a struct that derives `Copy` because both its fields
  are `i32` (promotion). They are used once each here, but could be used more.
- `dev: Device` is affine, and the program *threads* it: each `measure` consumes
  the device and returns it, and the returned one is the only one we may use
  next. Chapter 25 builds protocols on this pattern.
- `op: String` is `Clone` but not `Copy`, so the program duplicates it
  explicitly, once, with `op.clone()`, paying for one allocation.

The same program in the crate's syntax, with two buggy variants, is
`ch23_session.aff`:

```text
{{#include ../../code/rust/crates/affine/examples/programs/ch23_session.aff}}
```

The crate accepts `session`. Its derivation, printed with the contexts as
variable names only so that it fits the page, shows each of the four
treatments:

```text
{{#include ../../code/rust/output/ch23_copy.txt:75:92}}
```

`ch` appears in the contexts of *both* premises of each `measure` split: the first
`measure` receives it, and so does the rest of the program. That is rule S-Both.
`dev`, `dev2` and `dev3` each appear in exactly one leaf. The interesting line is
the one for the pair of labels: `op` appears in both of its premises, although
`String` is not `Copy`. The first premise uses `op` only through `op.clone()`,
which in Rust takes `&self`: it reads `op` through a shared borrow and leaves it
in place. The crate models that as a read that does not move, and the calculus,
which has no borrows, would write it with the constant of the previous sections,
$\mathtt{let}\ (op_1, op_2) = \mathsf{dup}\,op\ \mathtt{in}\ \dots$, using `op`
exactly once.

Forgetting the clone is a contraction of a non-`Copy` variable, and the crate
suggests the clone:

```text
{{#include ../../code/rust/output/ch23_copy.txt:93:104}}
```

Measuring with the old device is the error that typestate (Chapter 25) relies on:
the first `measure` consumed `dev`, and only `dev2` may be used now:

```text
{{#include ../../code/rust/output/ch23_copy.txt:106:114}}
```

In the formal system, the program's context is
`dev : Dev, ch : i32, op : String`, with multiplicities 1, $\infty$ and 1. The
generalized usage theorem says that `dev` and `op` are used at most once in any
derivation, and that `ch` may be used freely: exactly the three treatments above,
with the clone as the explicit term that turns one `op` into two.

## Common confusions

**"`Copy` is a cheap `Clone`."** They are different kinds of thing. `Copy` is a
property that makes duplication implicit, at every use, as a bitwise copy; it
has no method. `Clone` is a method that must be called. Every `Copy` type is
`Clone`, but a cheap `clone` does not make a type `Copy`: `Rc::clone` is cheap and
`Rc` is not `Copy`, because its duplication must be counted.

**"Moving is a `memcpy` and copying is a `memcpy`, so they are the same."** At the
machine level they often are. The difference is in the types: after a move the
source is no longer usable, and after a copy it is. That is the difference
between a split and S-Both, and it is decided by the type.

**"`&mut T` is used twice in my code, so it must be `Copy`."** The second use
receives a reborrow, a new and shorter-lived unique reference, created
implicitly at each call (Chapter 28). `let b = w;` after `let a = w;` is still
E0382.

**"`Rc<T>` makes `T` duplicable."** It makes the *pointer* duplicable, explicitly
and with counting. The `T` is shared, not duplicated, and is reachable only
through shared references.

**"`!A` is a type, so `Copy` should be a type constructor too."** Linear logic has
$!$ as a constructor; Rust, and the calculus of this chapter, use a predicate on
types. The two presentations agree on what may be duplicated; the predicate is
simpler to use (there is no need to write promotions and derelictions) at the
price of fixing, once per type, whether it is duplicable.

**"A type with only `Copy` fields can always be `Copy`."** Only if it has no
destructor. A destructor makes discarding an action, and an action cannot be
duplicated silently.

## Summary

- The exponential $!\tau$ marks the types for which contraction and weakening are
  allowed. Its rules are !-Weak, !-Contr, Dereliction and Promotion; promotion
  says that a duplicable value may only be built from duplicable resources.
- `Copy` behaves as if a type were already of the form $!\tau$: contraction and
  weakening are silent, dereliction is invisible, and promotion is the rule for
  which types may be `Copy` (all fields `Copy`: E0204). Destructors are excluded
  (E0184), shared references are `Copy`, and mutable references are not.
- `Clone` is a different mechanism: an explicit duplication term
  $\tau \multimap \tau \otimes \tau$, visible in the source, with a cost and
  possibly an effect. Every `Copy` type is `Clone`, and Lean proves the
  type-theoretic version: for a `Copy` type, $\lambda x.\,(x, x)$ is such a term.
- `Rc` and `Arc` share a value instead of duplicating it, and count the
  duplications and discards of the pointer; the counting is why they cannot be
  `Copy`.
- Formally, $\lambda^{\mathsf{aff}}$ with `Copy` adds a predicate on types and one
  splitting rule, S-Both; the typing rules are unchanged. The generalized usage
  theorem, proved in Lean with multiplicities in `ℕ∞`, says that non-`Copy`
  variables are still used at most once.
- The usage theorem holds for any choice of duplicable types, but preservation
  does not: if function types were `Copy` regardless of their captures, a
  well-typed program could step to an ill-typed one. That is why promotion
  matters, and why Rust's closures are `Copy` only when their captures are.
- The `affine` crate implements the extension: `Copy` places are not moved,
  `.clone()` reads without moving, and `#[derive(Copy)]` is checked as rustc
  checks it.

## Exercises

1. Using the four rules of $!$, derive $x : {!A} \vdash (\mathsf{derelict}\,x, \mathsf{derelict}\,x) : A \otimes A$
   and $x : {!A} \vdash () : \mathbf{1}$. Then explain why $x : A \vdash {!x} : {!A}$
   has no derivation.
   *Hint:* for the pair, apply !-Contr to a derivation in which two variables of
   type ${!A}$ go to the two components. For the last one, look at the context
   that Promotion requires.

2. Which of these types are `Copy` in Rust? `(i32, &String)`, `[&mut i32; 2]`,
   `Option<fn(i32) -> i32>`, the type of `move || n + 1` where `n: i32`, and the
   type of `move || s.len()` where `s: String`. Check your answers with a generic
   function `fn is_copy<T: Copy>(_: &T) {}`.
   *Hint:* apply the promotion rules component by component; for closures, look
   at what is captured, and how.

3. In Lean, prove that for every `Copy` type the discard map exists as well as
   the copy map: `HasTypeC isCopy [] (.lam τ .unit) (τ ⊸ .unit)`. Then prove that
   it exists for *every* type. Which structural rule makes the second statement
   true, and how would it fail in a linear calculus?
   *Hint:* `.lam .unit` needs no split at all; rule `unit` accepts any context.

4. In Lean, prove that `isCopy` is closed under the sum: `isCopy (τ ⊕ σ) = true ↔ isCopy τ = true ∧ isCopy σ = true`.
   Then add a type former for Rust's arrays to a copy of `Ty` and extend `isCopy`
   accordingly.
   *Hint:* the proof is the same as `isCopy_tensor`.

5. Give the `affine` crate a type `Arc<T>`, which behaves like `Rc<T>` for
   `Copy` and `Clone`, and a test showing that `(a.clone(), a)` is accepted and
   `(a, a)` rejected for `a: Arc<Config>`.
   *Hint:* add a variant to `Ty`, parse it like `Rc`, and add it to the same arms
   of `is_copy` and `is_clone` as `Rc`.

6. Write a Rust type whose `clone` panics on the second call, and use it to
   explain why the compiler may not insert calls to `clone` on its own, the way it
   inserts copies for `Copy` types.
   *Hint:* store a `Cell<bool>` (or an `Rc<Cell<u32>>`) in the value and check it
   in `clone`. An implicit duplication would run that code at places the
   programmer cannot see.
