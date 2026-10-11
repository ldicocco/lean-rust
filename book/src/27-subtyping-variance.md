# Subtyping and Variance

In Chapter 1, Rust rejected `if ready { 1 } else { "not yet" }`, and we noted
what the compiler did *not* do: it did not look for a common supertype of the
two branches, the way a language with subtyping might. Rust has no class
hierarchy, no `Cat` that is also an `Animal`, no `i32` that is also an `i64`.
It would be easy to conclude that Rust has no subtyping at all.

It has some, and you rely on it every day. When you pass a string literal, of
type `&'static str`, to a function that expects a `&'a str` for some short `'a`,
the compiler silently uses the fact that a reference valid for the whole program
is also valid for a shorter region. That is subtyping, on lifetimes. And as soon
as there is subtyping on lifetimes, every type that contains a lifetime raises a
question: if `&'static str` can be used as `&'a str`, can `Vec<&'static str>` be
used as `Vec<&'a str>`? Can `fn(&'static str)` be used as `fn(&'a str)`? Can
`&mut &'static str` be used as `&mut &'a str`? The answers are yes, no, and
*absolutely not*, and the reasons are the theory of **variance**. Getting
variance wrong is one of the few ways to write a use after free in a type
system that otherwise looks sound, which is why it deserves a chapter.

**In this chapter you will learn:**

- what subtyping is, how the subsumption rule brings it into a type system, and
  why it makes the types of a program a preorder, hence a category;
- why lifetimes are Rust's only source of subtyping, and how it shows up in
  ordinary code;
- the four variances (covariant, contravariant, invariant, bivariant), the
  variance of `&'a T`, `&'a mut T`, `fn(T) -> U`, `Box<T>`, `Cell<T>` and
  `*mut T`, and how to make the compiler prove each one;
- why `&mut T` must be invariant in `T`, through the classic unsound program
  that invariance rejects;
- how Rust infers the variance of your own types, and how `PhantomData` chooses
  it when the compiler cannot;
- variance as functoriality: covariant and contravariant functors on the
  category of lifetimes, and variances as a small monoid;
- how to formalize a tiny language with subtyping in Lean and prove that the
  contravariant rule for functions is what makes it sound, and why Lean itself
  has coercions and subtypes but no subtyping.

## Subtyping and subsumption

A type $\sigma$ is a **subtype** of a type $\tau$, written $\sigma <: \tau$, when
every value of type $\sigma$ can be used wherever a value of type $\tau$ is
expected. In an object-oriented language, a `Cat` class extending `Animal` makes
`Cat` a subtype of `Animal`; in a language with refinement types, the type of
positive integers is a subtype of the type of integers. A type system brings
subtyping into its judgments with one rule, called **subsumption**:

$$
\dfrac{\Gamma \vdash e : \sigma \qquad \sigma <: \tau}{\Gamma \vdash e : \tau}\;\textsf{T-Sub}
$$

If $e$ has type $\sigma$, and $\sigma$ is a subtype of $\tau$, then $e$ also has
type $\tau$. The subtyping relation itself is defined by its own rules. Two of
them are always present:

$$
\dfrac{}{\tau <: \tau}\;\textsf{S-Refl}
\qquad\qquad
\dfrac{\sigma <: \tau \qquad \tau <: \upsilon}{\sigma <: \upsilon}\;\textsf{S-Trans}
$$

A relation that is reflexive and transitive is a **preorder**, and Chapter 16
showed that a preorder is a category: the objects are the types, and there is
exactly one arrow $\sigma \to \tau$ when $\sigma <: \tau$ (and none otherwise).
Identity arrows are S-Refl, composition is S-Trans, and the category laws hold
automatically because there is never more than one arrow between two objects.
Keep this picture in mind; it will turn variance into something you already
know.

Subsumption has a cost. Every other rule you have seen is *syntax-directed*:
the shape of the term determines which rule applies. T-Sub applies to every
term, at any point, so a derivation can use it anywhere, any number of times. A
type checker cannot try all of them. Practical checkers use an *algorithmic*
formulation instead, in which subtyping is checked only where it is needed (for
instance, when an argument is passed to a function) and in which transitivity
is built in rather than being a rule. We will build one in Lean later in this
chapter and prove that it decides the same relation.

There are two ways to read $\sigma <: \tau$. The *inclusion* reading says that
the values of $\sigma$ are among the values of $\tau$: every positive integer
*is* an integer, with no conversion. The *coercion* reading says that there is a
conversion from $\sigma$ to $\tau$ that the compiler inserts silently. The two
readings coincide only when the conversion does nothing. Rust's lifetime
subtyping is pure inclusion; its many coercions (deref, unsizing) are something
else, and the last part of the chapter is about the difference.

## Rust's only subtyping: lifetimes

Rust has no subtyping between nominal types. A struct cannot extend another,
an `i32` must be converted to an `i64` explicitly, and a `Box<Valve>` that
becomes a `Box<dyn Describe>` goes through a coercion that builds a new fat
pointer, not through subtyping. The one source of subtyping is the outlives
relation of Chapter 26. If `'long` outlives `'short`, a reference valid
throughout `'long` is valid throughout `'short`:

$$
\dfrac{\Delta \vdash \alpha : \beta}{\Delta \vdash \&\alpha\;\tau <: \&\beta\;\tau}\;\textsf{S-Ref}
$$

Here $\&\alpha\;\tau$ is our notation for `&'a T`, and $\Delta \vdash \alpha : \beta$
is the outlives judgment of Chapter 26. Since `'static` outlives every region,
`&'static T` is a subtype of every `&'a T`. The program
`code/rust/examples/ch27_variance.rs` starts with the most ordinary use:

```rust
{{#include ../../code/rust/examples/ch27_variance.rs:subsumption}}
```

```text
{{#include ../../code/rust/output/ch27_variance.txt:1:1}}
```

`longer` wants two arguments of the same type `&'a str`. The compiler picks
`'a` to be the region of `configured`, and uses subsumption to view `fallback`,
of type `&'static str`, at the type `&'a str`. Nothing happens at run time: the
pointer is the same pointer. Subtyping on lifetimes is invisible in the
generated code, which is exactly what the inclusion reading predicts.

(There is a second, rarer kind of subtyping in Rust, between higher-ranked
types: a function pointer of type `for<'a> fn(&'a str)`, which accepts a
reference with any lifetime, is a subtype of `fn(&'x str)` for each particular
`'x`. It is the same idea as instantiating a generic function, Chapter 12's
universal quantifier, and the call `grow_argument(count)` below relies on it.)

## Variance

Subtyping between two lifetimes induces subtyping between bigger types that
contain them, and how it does so depends on the type constructor. This is
**variance**. For a type constructor $F$ with one parameter:

- $F$ is **covariant** if $\sigma <: \tau$ implies $F\,\sigma <: F\,\tau$: the
  subtyping goes the same way.
- $F$ is **contravariant** if $\sigma <: \tau$ implies $F\,\tau <: F\,\sigma$:
  the subtyping flips.
- $F$ is **invariant** if $F\,\sigma <: F\,\tau$ holds only when $\sigma$ and
  $\tau$ are the same type (or, more precisely, are subtypes of each other).
- $F$ is **bivariant** if $F\,\sigma <: F\,\tau$ always holds: the parameter
  does not matter, which happens when it is not used at all.

A type constructor with several parameters has a variance in each. The rules
for the classic constructors are these:

$$
\dfrac{\sigma <: \sigma' \qquad \tau <: \tau'}{\sigma \times \tau <: \sigma' \times \tau'}\;\textsf{S-Pair}
\qquad\qquad
\dfrac{\sigma' <: \sigma \qquad \tau <: \tau'}{\sigma \to \tau <: \sigma' \to \tau'}\;\textsf{S-Arrow}
$$

Pairs are covariant in both components: a pair of a cat and a dog is a pair of
two animals. Functions are covariant in the result, but **contravariant in the
argument**: notice that the premise about arguments is written $\sigma' <: \sigma$,
the "wrong" way round. The reason is clearest with callbacks. Suppose a
scheduler wants a callback of type $\mathsf{Cat} \to \mathsf{Unit}$, which it will
call with cats. A function of type $\mathsf{Animal} \to \mathsf{Unit}$, which
handles any animal, is perfectly acceptable: whatever the scheduler passes, it
can handle. So $\mathsf{Animal} \to \mathsf{Unit} <: \mathsf{Cat} \to \mathsf{Unit}$,
even though $\mathsf{Cat} <: \mathsf{Animal}$. A function that *accepts more* is
the more useful one, hence the subtype. The opposite, a function that handles
only cats used where any animal may arrive, would be a disaster.

In Rust, the variances of the standard type constructors are fixed by the
language and the standard library:

| Type | Variance in `'a` | Variance in `T` |
|---|---|---|
| `&'a T` | covariant | covariant |
| `&'a mut T` | covariant | **invariant** |
| `Box<T>`, `Vec<T>`, `Option<T>` | | covariant |
| `Cell<T>`, `RefCell<T>`, `UnsafeCell<T>` | | **invariant** |
| `*const T` / `*mut T` | | covariant / **invariant** |
| `fn(T) -> U` | | **contravariant** in `T`, covariant in `U` |
| `PhantomData<T>` | | covariant |

### Making the compiler prove it

You can make the compiler confirm every entry of the table. A function whose
body is just `x`, with a signature that converts one type into another, compiles
only if the conversion is a subtyping step. Each such function is a *witness*:
its existence is a proof, checked by the compiler, that the claimed variance
holds.

```rust
{{#include ../../code/rust/examples/ch27_variance.rs:witnesses}}
```

```text
{{#include ../../code/rust/output/ch27_variance.txt:2:7}}
```

Read the signatures carefully, because the direction of each one is the
content. `shrink_ref` turns `&'long str` into `&'short str`: covariance in the
lifetime. `shrink_ref_ref` does the same one level down, inside a reference:
covariance in `T`. `shrink_mut` shortens the *outer* lifetime of a mutable
reference, but leaves the referent type `&'v str` alone: that is all that is
allowed, as we are about to see. `grow_argument` goes the other way, from a
callback that accepts `&'short str` to one that accepts `&'long str`: the
callback that accepts more is the subtype. And `shrink_twice` shows what happens
when a contravariant position is nested in another contravariant position: the
two flips cancel, and `fn(fn(T))` is covariant in `T`. Every one of these
functions compiles; reversing the direction of any of them would not.

The contravariance of `fn(T)` is also responsible for errors. Here a function
that only accepts `'static` strings is passed where a callback for a short-lived
string is needed:

```rust
{{#include ../../code/rust/compile_fail/ch27_contravariance.rs:callback}}
```

```text
{{#include ../../code/rust/compile_fail/ch27_contravariance.stderr}}
```

`call_with` wants a callback of type `fn(&'a str) -> usize` and a message of type
`&'a str`, with one `'a`. The callback `needs_static` has type
`fn(&'static str) -> usize`. For it to be a `fn(&'a str) -> usize`, contravariance
requires `&'a str <: &'static str`, which holds only if `'a` is `'static`. So the
compiler sets `'a` to `'static`, and then `&msg` would have to be a
`&'static str`, which it is not: `msg` is a local `String`. The compiler reports
the consequence (E0597), and its label mentions the "coercion" of the function
item `needs_static` to a function pointer, the place where the subtyping
requirement arose. This is the scheduler disaster in Rust form: a callback that
can handle only long-lived strings, offered to code that will call it with a
short-lived one.

## Why `&mut T` must be invariant

Covariance of `&'a T` in `T` is safe because a shared reference only reads: if
you can read a `&'static str` out of it, you can certainly treat what you read
as a `&'short str`. A mutable reference also *writes*, and writing reverses the
direction. Here is the classic program that shows why, kept in
`code/rust/compile_fail/ch27_mut_invariance.rs`:

```rust
{{#include ../../code/rust/compile_fail/ch27_mut_invariance.rs:overwrite}}
```

Suppose, for a moment, that `&mut T` were covariant in `T`. Then
`&mut s : &mut &'static str` could be viewed as `&mut &'short str`, where
`'short` is the region of `local`. The call `overwrite(&mut s, &local)` would
type-check with `T = &'short str`, and it would store a pointer to `local` into
`s`. At the closing brace `local` is dropped, and `println!("{s}")` reads freed
memory, through a variable whose type still promises a string that lives
forever. Every step is locally reasonable; only the covariance assumption is
wrong.

Rust's actual rule rejects the program:

```text
{{#include ../../code/rust/compile_fail/ch27_mut_invariance.stderr}}
```

Because `&mut T` is invariant in `T`, the type `&mut &'static str` of the first
argument fixes `T = &'static str` exactly, with no room to shorten it. Then the
second argument `&local` must be a `&'static str`, and the compiler explains
that the type annotation on `s` "requires that `local` is borrowed for
`'static`", which is impossible.

The same attack can be written inside a single function, with the conflict in
the signature itself. Here the compiler names the culprit explicitly:

```rust
{{#include ../../code/rust/compile_fail/ch27_invariance_escape.rs:remember}}
```

```text
{{#include ../../code/rust/compile_fail/ch27_invariance_escape.stderr}}
```

If `&mut Vec<&'static str>` could be viewed as `&mut Vec<&'1 str>`, the `push`
would type-check, and the caller would later read a dangling `&'static str` out
of its log. The two notes at the end say exactly what this section says:
"mutable references are invariant over their type parameter".

Interior mutability writes through a *shared* reference, so it has the same
problem, and `Cell<T>` is invariant too:

```rust
{{#include ../../code/rust/compile_fail/ch27_cell_invariance.rs:set_label}}
```

```text
{{#include ../../code/rust/compile_fail/ch27_cell_invariance.stderr}}
```

The principle behind all three is worth stating as a rule of thumb:
**reading is covariant, writing is contravariant, and both is invariant.** A
place you can read from is a *source* of $\tau$ values, like a function
$\mathsf{Unit} \to \tau$, covariant in $\tau$. A place you can write to is a
*sink* for $\tau$ values, like a function $\tau \to \mathsf{Unit}$,
contravariant in $\tau$. A mutable reference is both at once, and the only way
for both views to be subtypes is for the types to be equal. The same reasoning
explains the rest of the table: `*const T` only reads and is covariant, `*mut T`
writes and is invariant, and the lifetime `'a` of `&'a mut T` stays covariant
because shortening a loan only gives the permission back sooner, which is
always safe.

Variance is not a style rule. A type with the wrong variance, typically a
hand-written abstraction over raw pointers, lets safe code produce exactly the
dangling reference of the classic program. That is why the next section
matters to anyone who writes `unsafe` code.

## The variance of your own types

You never declare the variance of a struct in Rust; the compiler **infers** it
from the fields. Each field's type has a variance in each parameter, and the
struct's variance is the strongest constraint among them: if a parameter
appears covariantly in one field and contravariantly in another, the struct is
invariant in it; if it appears in no field at all, the struct would be bivariant
in it. Nesting composes: a parameter inside a `fn` argument inside a `fn`
argument is covariant, as `shrink_twice` showed. We will make this calculation
precise in Lean.

A parameter that appears in no field is a problem, because a bivariant
parameter means nothing at all, and Rust rejects it (Chapter 25 met the same
error for a typestate parameter):

```rust
{{#include ../../code/rust/compile_fail/ch27_unused_param.rs:raw_view}}
```

```text
{{#include ../../code/rust/compile_fail/ch27_unused_param.stderr}}
```

The help names the solution: `PhantomData`, a zero-sized marker type in
`std::marker`. A field of type `PhantomData<X>` takes no space, and tells the
compiler to treat the struct, for variance and for a few other purposes, *as if*
it contained an `X`. By choosing `X`, you choose the variance:

| Marker | Variance in `T` | Notes |
|---|---|---|
| `PhantomData<T>` | covariant | "owns a `T`": inherits `T`'s `Send`/`Sync` |
| `PhantomData<&'a T>` | covariant (and in `'a`) | a borrow of `T` for `'a` |
| `PhantomData<&'a mut T>` | invariant (covariant in `'a`) | a unique borrow |
| `PhantomData<fn() -> T>` | covariant | produces `T`s; always `Send` and `Sync` |
| `PhantomData<fn(T)>` | contravariant | consumes `T`s; always `Send` and `Sync` |
| `PhantomData<fn(T) -> T>` | invariant | always `Send` and `Sync` |

The last column matters as much as the second. Auto traits such as `Send` and
`Sync` are also computed from the fields, so the marker decides them too. A
function pointer is always `Send` and `Sync`, whatever its argument type, so
the `fn` markers give the variance you want without dragging in the thread-safety
of `T`. `PhantomData<T>` also tells the compiler's drop checker that dropping
the struct may drop a `T`, which matters for types that really own values
through raw pointers.

Here is a common pattern, a typed identifier that cannot be confused across
tables:

```rust
{{#include ../../code/rust/examples/ch27_variance.rs:typed_id}}
```

`Id<Order>` and `Id<Customer>` are different types, so passing one where the
other is expected is a type error, while at run time both are a plain `u64`.
The marker `PhantomData<fn() -> T>` makes `Id<T>` covariant, owning nothing, and
thread-safe regardless of `T`, which is what the program checks with an `Rc`,
the standard example of a type that is neither `Send` nor `Sync`:

```text
{{#include ../../code/rust/output/ch27_variance.txt:8:9}}
```

With `PhantomData<T>` instead, `Id<Rc<String>>` would be neither `Send` nor
`Sync`, for no good reason.

## Variance as functoriality

Now return to the picture from the beginning of the chapter. Lifetimes ordered
by outlives form a preorder, so a category $\mathcal{L}$: one object per
lifetime, one arrow $\alpha \to \beta$ when $\alpha$ outlives $\beta$. Types
ordered by subtyping form another category $\mathcal{T}$. A type with a lifetime
parameter, such as `&'x i32`, is a map from lifetimes to types:
$\alpha \mapsto \&\alpha\;\mathtt{i32}$.

Chapter 17 defined a **functor** between categories: a map on objects and a map
on arrows that preserves identities and composition. Between preorders, there
is at most one arrow between two objects, so preserving identities and
composition is automatic, and a functor is simply a map on objects that sends
arrows to arrows: a **monotone** map. Covariance of `&'x i32` in `'x` says
exactly that whenever $\alpha \to \beta$ in $\mathcal{L}$, there is an arrow
$\&\alpha\;\mathtt{i32} \to \&\beta\;\mathtt{i32}$ in $\mathcal{T}$. **A
covariant type constructor is a functor $\mathcal{L} \to \mathcal{T}$.**

Contravariance reverses arrows. Chapter 16 built the *opposite* category
$\mathcal{L}^{op}$, with the same objects and every arrow turned around. A
contravariant constructor such as `fn(&'x i32)` sends an arrow
$\alpha \to \beta$ to an arrow $F\beta \to F\alpha$, which is an arrow-preserving
map from $\mathcal{L}^{op}$: **a contravariant type constructor is a functor
$\mathcal{L}^{op} \to \mathcal{T}$**. This is the same "contravariant functor"
that Chapter 17 met with predicates and comparators.

![Covariance and contravariance as functors from the category of lifetimes: &'x T sends each outlives arrow to a subtyping arrow in the same direction, fn(&'x T) to one in the opposite direction.](../images/ch27-functors.svg)

The two other variances fit the same pattern. An invariant constructor sends an
arrow $\alpha \to \beta$ to an arrow only when $\alpha = \beta$: it is a functor
only from the *discrete* category on the lifetimes, which keeps the objects and
throws away every arrow except the identities. A bivariant constructor sends
every pair of lifetimes to related types: it is a functor from the category with
an arrow between any two objects. So the four variances are the four ways a
type can be functorial in its parameter.

Composition of functors explains the sign rule. If $F$ and $G$ are both
contravariant, $F \circ G$ turns arrows around twice, which is not turning them
around at all: a functor $(\mathcal{L}^{op})^{op} = \mathcal{L} \to \mathcal{T}$,
covariant. That is `shrink_twice`. The variances, with composition, behave like
signs under multiplication, with two extra elements: invariance absorbs
covariance and contravariance, and bivariance absorbs everything. When a
parameter occurs in several places, the constraints are combined by a *meet* in
the lattice below: covariant and contravariant together give invariant, and
bivariant (no occurrence) is neutral.

![The four variances ordered by how much they allow: bivariant on top, covariant and contravariant in the middle, invariant at the bottom. Combining two occurrences of a parameter takes the meet.](../images/ch27-variances.svg)

### Functors in Lean

The file `code/lean/Book/Ch27/Functoriality.lean` makes this literal, with the
book's `Category` class from Chapter 16 (`Book.Ch16.Category`, which it
imports). Lifetimes are modeled by the point where they end, so `'a` outlives
`'b` when `b ≤ a`, and types by a small language of Rust-like types, `RTy ℕ`,
defined in `Variance.lean` below together with its subtyping relation `RSub`:

```lean
{{#include ../../code/lean/Book/Ch27/Functoriality.lean:categories}}
```

A morphism is a *proof* wrapped in `PLift`. The class requires morphisms to live
in `Type`, and a proof of `b ≤ a` lives in `Prop`; `PLift` lifts a proposition
into a type with one element per proof. Since all proofs of a proposition are
equal (proof irrelevance, Chapter 10), there is at most one morphism between two
objects, and the category laws hold by `rfl`.

We need a notion of functor for the book's class. Chapter 17 defines one,
`CatFunctor`; since a file of this chapter may import only Chapter 16 and its own
files, we redefine a minimal version here under the name `Fun`:

```lean
{{#include ../../code/lean/Book/Ch27/Functoriality.lean:functor}}
```

`Fun.ofMonotone` is the observation above, as a definition (Chapter 17's
`monotoneFunctor` is the same idea for Mathlib's preorders): to build a functor
into a thin category, a map on objects and a map on arrows suffice, and the laws
are proved by `rfl`, because two morphisms with the same ends are definitionally
equal. Now covariant and contravariant types become functors:

```lean
{{#include ../../code/lean/Book/Ch27/Functoriality.lean:functors}}
```

`covariantFunctor` takes a type `t` with a lifetime parameter and a proof that
its inferred variance is `co`, and produces a functor from lifetimes. The map on
arrows is the theorem `RTy.covariant`, which we prove in the next section from
the soundness of variance inference. `contravariantFunctor` does the same from
`Op Lifetime`, Chapter 16's opposite category, whose arrows are the reversed
arrows of `Lifetime`. The two examples at the end pass `rfl` as the variance
proof: Lean computes the variance of `&'x i32` and of `fn(&'x i32)` and checks
that they are `co` and `contra`.

Mathlib has the same construction in general: every preorder is a category, and
a monotone function is a functor.

```lean
{{#include ../../code/lean/Book/Ch27/Functoriality.lean:mathlib}}
```

`Monotone.functor` takes a proof of monotonicity and returns a
`CategoryTheory.Functor` (written `ℕ ⥤ ℕ` in Mathlib's notation).

## Variance in Lean

The file `code/lean/Book/Ch27/Variance.lean` turns the algebra of variances into
definitions and theorems, and uses them to prove that variance inference, the
calculation the compiler performs for your structs, is sound.

### The algebra of variances

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:variance}}
```

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:mul}}
```

`mul` is composition: `v * w` is the variance of a position of variance `w`
nested inside a position of variance `v`. Bivariance absorbs everything, then
invariance absorbs what is left, covariance is the identity, and two
contravariances make a covariance. The instances `Mul` and `One` let us write
`*` and `1`.

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:meet}}
```

`meet` combines two occurrences of the same parameter: bivariance (no
occurrence) is neutral, two equal variances stay as they are, and any other
combination is invariant.

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:monoid}}
```

`CommMonoid` is Mathlib's class of commutative monoids. Its laws are proved by
brute force: `cases a <;> cases b <;> cases c <;> rfl` splits into the
$4 \times 4 \times 4 = 64$ combinations and checks each by computation. Being a
monoid instance gives us Mathlib's notation for free, including powers:
`contra ^ 3` is three nested contravariant positions, which is contravariant.

### What a variance means

Tables of rules are only as trustworthy as their meaning. A variance has a
precise meaning: given the relation that holds between two parameters (for
lifetimes, "outlives"), it says which relation must hold for the types to be in
the subtyping relation.

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:apply}}
```

Covariance uses the relation as it is, contravariance flips it, invariance
needs it in both directions, and bivariance needs nothing. With this meaning, the
algebra is no longer arbitrary: the two operations are exactly composition and
intersection of meanings.

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:apply_mul}}
```

Both proofs are case analyses over the 16 combinations, with `simp` unfolding the
definitions. What remains in some cases is a small propositional fact such as
`R a b ∧ R b a ↔ R b a ∧ R a b`, which `tauto` (a Mathlib tactic that proves
tautologies of propositional logic) finishes. In `apply_mul`, the `simp` set
includes `HMul.hMul` and `Mul.mul` so that the `*` notation unfolds to our `mul`.
These two theorems say that the map from variances to relation transformers
turns `*` into composition and the meet into conjunction: the variance algebra
is a faithful summary of how relations are transformed.

### Variance inference, proved sound

Now a small language of Rust-like types, with the lifetime of each reference
drawn from a set `L`:

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:rty}}
```

`RTy ℕ` is a closed type, whose lifetimes are end points, and `RTy Lft` is a
type with one lifetime parameter `'x`. Subtyping on closed types follows the
Rust table:

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:rsub}}
```

Invariance is written as subtyping in both directions (`RSub t u → RSub u t`),
as in the definition at the start of the chapter. The variance that the
compiler would infer for a type with a parameter `'x` is computed by recursion,
and `inst` replaces `'x` by a concrete lifetime:

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:infer}}
```

Each case is a line of the Rust table, written with the algebra: a reference
`&'a T` is covariant in `'a` (if `'a` is `'x`) and covariant in `T`, so its
variance is the meet of the two; a mutable reference has `inv` in front of its
referent; a function has `contra` in front of its argument and `co` in front of
its result; a two-field struct is the meet of its fields. Lean computes:

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:infer_eval}}
```

The last line is a struct `Holder<'x>` with a reference field and a
`Cell<i32>` field. The `Cell` makes its contents invariant, but its contents do
not mention `'x`, so the field is bivariant in `'x` and the struct is covariant.

The theorem that makes all this trustworthy says that the inferred variance is
*sound*: whatever relation between two lifetimes the variance asks for, it
suffices for subtyping.

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:infer_sound}}
```

The proof is by induction on the type, with one case per constructor, and each
case has the same shape: rewrite the hypothesis `h` with the definition of
`RTy.var` and the two meaning theorems, then build the subtyping proof from the
pieces. Take the `fn t u` case. After
`rw [RTy.var, apply_meet, apply_mul, apply_mul] at h`, the hypothesis says that
`contra.apply (t.var.apply Outlives) a b` and `co.apply (u.var.apply Outlives) a b`
hold. The first is, by the definition of `apply`, the relation for `t` with `a`
and `b` *swapped*. So the induction hypothesis for the argument is used at
`b a`, giving `RSub (t.inst b) (t.inst a)`, which is exactly the
contravariant premise of `RSub.fn`. The `refMut` and `cell` cases use their
induction hypothesis twice, at `a b` and at `b a`, for the two directions that
invariance demands. In the `ref` and `refMut` cases, `cases l` distinguishes
the parameter `'x` (where the outlives fact comes from `h`) from a fixed scope
(where both instantiations give the same lifetime, and `Nat.le_refl` applies).

The corollaries specialize the theorem to the two variances we used to build
functors:

```lean
{{#include ../../code/lean/Book/Ch27/Variance.lean:corollaries}}
```

## A tiny language with subtyping

`RSub` was given by rules, chosen to match Rust. Why are those the *right*
rules? In particular, why must the function rule be contravariant? To answer, a
type system needs a meaning, and the subtyping rules must be sound for it. The
file `code/lean/Book/Ch27/Subtyping.lean` does this for a tiny language, small
enough that the whole argument fits in a few theorems.

### Types as refinements

The language has three base types, `pos`, `nat` and `int`, all represented at
run time by integers, and function types. To give types a meaning, each type is
indexed by its *shape*, which says what its values look like at run time:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:shape}}
```

`Shape.Val` computes a Lean type for each shape: integers for base types,
functions for arrows. It is marked `@[reducible]` so that Lean unfolds it
freely when checking types, which lets us write `0 < z` for a `z` of type
`Shape.base.Val`.

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:ty}}
```

`Ty` is an indexed family (Chapter 25 used them for typestate): a `Ty s` is a type
of shape `s`. `Ty.Holds τ v` says that the run-time value `v` belongs to the type
`τ`. A positive integer is one that is greater than zero, and a function belongs
to $\sigma \Rightarrow \tau$ when it sends every value of $\sigma$ to a value of
$\tau$. This is the inclusion reading of types, made precise: a type is a
*predicate* on run-time values, also called a *refinement*.

The subtyping rules:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:sub}}
```

Because the relation is indexed by shape, only types of the same shape can be
compared, and an arrow is never a subtype of a base type. The arrow rule has the
contravariant premise `Sub σ' σ`.

### Soundness, and where contravariance is needed

Soundness says that subtyping is inclusion: every value of a subtype is a value
of the supertype. That is what makes rule T-Sub safe: a term that produces a
value of $\sigma$ can be used where a value of $\tau$ is expected, because that
value *is* a value of $\tau$.

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:sound}}
```

The proof is by induction on the derivation of `σ <: τ`. Reflexivity is
immediate, and transitivity chains the two induction hypotheses. For `pos_nat`,
`Ty.Holds` unfolds to `0 < v` and the goal to `0 ≤ v`, and Mathlib's
`le_of_lt` converts one into the other; for `nat_int` the goal is `True`.

The arrow case is the one that matters. We have a function `f` with
`hf : (σ ⇒ τ).Holds f`, which says that `f` sends values of `σ` to values of
`τ`, and we must show that it sends values of `σ'` to values of `τ'`. So take
`x` with `hx : σ'.Holds x`. To apply `hf`, we need `x` to be a value of `σ`. The
premise of the rule is `σ' <: σ`, so the induction hypothesis `ihσ` converts
`σ'.Holds x` into `σ.Holds x`: this is the step that needs the argument premise
to point from `σ'` to `σ`. Now `hf x hxσ` says that `f x` is a value of `τ`, and
`ihτ` (from `τ <: τ'`) makes it a value of `τ'`.

With a covariant argument premise, `σ <: σ'`, the induction hypothesis would
convert `σ.Holds x` into `σ'.Holds x`, the wrong direction, and the proof would
be stuck. Being stuck in a proof is not yet a counterexample, so the file proves
that the covariant rule really is unsound:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:bad}}
```

The covariant rule derives `nat ⇒ nat <: int ⇒ nat` from `nat <: int`. The
identity function on integers belongs to `nat ⇒ nat`, since it sends naturals to
naturals. If subsumption were sound for the bad rule, the identity would also
belong to `int ⇒ nat`, and applied to `-1` it would give a natural number, that
is `0 ≤ -1`. The hypothesis `hneg` states exactly this, and `linarith`, Mathlib's
tactic for linear arithmetic, derives the contradiction. In Rust terms: the
identity is a callback that is fine for `'static` strings; treating it as a
callback for any string is fine too, but treating a callback *for long-lived
values only* as a callback for short-lived ones is exactly the
`ch27_contravariance` error.

### An algorithm, and why transitivity can go

To check subtyping, an implementation cannot search for derivations that use
S-Trans, because the middle type $\tau$ of a transitivity step can be anything.
The algorithmic version builds transitivity in:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:algorithmic}}
```

On base types it compares ranks in the chain `pos < nat < int`; on arrows it
recurses with the variance of each side. There is no case for transitivity.
`subtype` is defined by *dependent* pattern matching: matching on the shape
first tells Lean that in the `.arrow` case both types must be arrows, so no
other combination needs a case.

The file proves the algorithm sound (`subtype_sound`: if it says `true`, there
is a derivation) and complete (`subtype_complete`: if there is a derivation, it
says `true`). Completeness is the interesting direction, because the rules have
S-Trans and the algorithm does not, so we must show that transitivity is
*admissible* for the algorithm, in the sense of Chapter 6: it can be derived
rather than assumed.

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:subtype_trans}}
```

This theorem is written as a recursive function, by pattern matching on the
shape: a proof by structural recursion is a proof by induction (Chapter 10 made
the same observation about derivations). On base types, `simp only` turns the Boolean
comparisons into inequalities between ranks, and `omega` chains them. On
arrows, the argument comparisons go the other way: from `σ ⇒ τ <: σ' ⇒ τ'` and
`σ' ⇒ τ' <: σ'' ⇒ τ''` we have `σ' <: σ` and `σ'' <: σ'`, so the recursive call
chains them as `σ'' <: σ' <: σ`, *in the reverse order*: `subtype_trans h₂.1 h₁.1`.
Contravariance shows up even in the proof of transitivity.

With both directions proved, the algorithm decides the relation, and `decide`
can prove and refute subtyping judgments:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:decide}}
```

The third example is the type-level version of `shrink_twice`: in an argument of
an argument, the subtyping goes in the same direction, `pos` on the subtype side
and `nat` on the supertype side.

## Coercions are not subtyping

Rust performs many implicit conversions that look like subtyping and are not.
They are called **coercions**, and they happen only at certain *coercion sites*
(a `let` with a type annotation, a function argument, a struct field, a return
value). The main ones are:

- *deref coercion*: `&String` to `&str`, `&Box<T>` to `&T`, `&Vec<T>` to
  `&[T]`, and in general `&U` to `&T` when `U: Deref<Target = T>`;
- *unsizing*: `&[T; N]` to `&[T]`, `Box<T>` to `Box<dyn Trait>`;
- *weakening a permission*: `&mut T` to `&T`;
- *function items and non-capturing closures to function pointers*;
- the never type `!` to any type (Chapter 1).

A subtyping step reuses a value as it is. A coercion converts it, and the
example `code/rust/examples/ch27_coercions.rs` makes the conversions visible.
First, a deref coercion calls code, here a `Deref` implementation that counts
its calls:

```rust
{{#include ../../code/rust/examples/ch27_coercions.rs:counting_deref}}
```

Second, unsizing and function-pointer coercions change the representation:

```rust
{{#include ../../code/rust/examples/ch27_coercions.rs:representation}}
```

Third, lifetime subtyping changes nothing:

```rust
{{#include ../../code/rust/examples/ch27_coercions.rs:subtyping_is_free}}
```

```text
{{#include ../../code/rust/output/ch27_coercions.txt:1:5}}
```

The `Deref` implementation ran once while `shout(&name)` was being called. A
reference to an array is a thin pointer (8 bytes on a 64-bit machine); as a
slice it becomes a fat pointer with a length (16 bytes), and the same happens
when a `Box<Valve>` becomes a `Box<dyn Describe>`, which carries a vtable
pointer (Chapter 15). A function item has a zero-sized type of its own, and only
the coercion to a function pointer materializes an address. The lifetime
subtyping step, in contrast, leaves the size and the address unchanged.

There is a second, structural difference. Subtyping lifts through type
constructors according to their variance: `Vec<&'static str>` is a subtype of
`Vec<&'a str>` because `Vec` is covariant, so no work is needed to use one as
the other. Coercions do not lift:

```rust
{{#include ../../code/rust/compile_fail/ch27_no_coercion_in_vec.rs:names}}
```

```text
{{#include ../../code/rust/compile_fail/ch27_no_coercion_in_vec.stderr}}
```

`&String` coerces to `&str`, but `Vec<&String>` does not coerce to `Vec<&str>`.
It could not, cheaply: each element would have to be converted, which means
building a new vector.

```rust
{{#include ../../code/rust/examples/ch27_coercions.rs:no_lifting}}
```

The weakening of `&mut T` to `&T` is worth a separate look, because it connects
to Chapter 26: a unique permission can always be given up in favor of a shared
one.

```rust
{{#include ../../code/rust/examples/ch27_coercions.rs:mut_to_shared}}
```

### Lean: coercions and subtypes, no subtyping

Lean has no subtyping at all: a term has a type, and no rule lets it be used at a
bigger one. What looks like subtyping is a coercion that the elaborator inserts,
and Lean shows it to you, marked `↑`. The examples are in
`code/lean/Book/Ch27/Coercions.lean`:

```lean
{{#include ../../code/lean/Book/Ch27/Coercions.lean:coe_nat_int}}
```

Passing a natural number to a function on integers works, and `#check` reveals
how: the argument became `↑3`, a call to the conversion function `Int.ofNat`, as
the `example` confirms by `rfl`. The conversion goes only one way:

```lean
{{#include ../../code/lean/Book/Ch27/Coercions.lean:no_coe_back}}
```

You can add coercions for your own types with an instance of the class `Coe`,
which is how the elaborator finds them:

```lean
{{#include ../../code/lean/Book/Ch27/Coercions.lean:custom_coe}}
```

The `#check` shows the inserted call (the field access `c.amount`, followed by
the `ℕ`-to-`ℤ` coercion), and the `#eval` shows that the list literal mixing
`Cents` and integers is accepted. This is Rust's deref coercion in Lean form: a
function call that the compiler writes for you.

Lean's **subtypes** are something else again, despite the name. The type
`{n : ℕ // n % 2 = 0}` is a *refinement*: its values are pairs of a number and a
proof that the number is even (Chapter 10 introduced `Subtype`).

```lean
{{#include ../../code/lean/Book/Ch27/Coercions.lean:subtype}}
```

An `Even` is not a natural number; `.val` (or the coercion `↑`, which unfolds to
it) extracts one. And like Rust's coercions, this one does not lift through
`List`:

```lean
{{#include ../../code/lean/Book/Ch27/Coercions.lean:no_lift}}
```

Our tiny language connects the two ideas. Its types *are* refinements of the
run-time values, so each type gives a Lean subtype, and a subtyping proof gives a
coercion between them that does nothing to the value:

```lean
{{#include ../../code/lean/Book/Ch27/Subtyping.lean:coe}}
```

`Ty.Sem τ` is the Lean subtype of run-time values that belong to `τ`.
`Sub.coe` keeps the value `v.val` and only replaces the proof, using
`Sub.sound`; `Sub.coe_val` states, by `rfl`, that the value is untouched. In
the *coercion* reading of subtyping, our language's subtyping is a coercion
whose run-time part is the identity, which is exactly what Rust's lifetime
subtyping is, and what Rust's deref and unsizing coercions are not.

## Putting it together: the variance of a raw-pointer view

Let us design a type with a variance that we choose on purpose: a borrowed view
of a slice, implemented with a raw pointer, the kind of type that sits at the
bottom of many data-structure crates. The first attempt was
`ch27_unused_param.rs`: a pointer and a length, with a lifetime parameter `'a`
that nothing mentions, rejected with E0392 because the compiler cannot infer a
variance for an unused parameter.

**Step 1: say what the type means.** A `RawView<'a, T>` should behave exactly
like a `&'a [T]`: it borrows the elements for `'a` and only reads them. So it
should have the variance of `&'a [T]`: covariant in `'a` and in `T`.

**Step 2: choose the marker.** "Behaves like a `&'a T`" is precisely what
`PhantomData<&'a T>` says:

```rust
{{#include ../../code/rust/examples/ch27_variance.rs:raw_view}}
```

The inferred variance is now the meet of the fields' variances. `ptr: *const T`
is covariant in `T` and does not mention `'a`; `len` mentions nothing;
`_borrow: PhantomData<&'a T>` is covariant in both. The meet is covariant in
both, as intended. In the notation of `Variance.lean`, the variance in `'a` is
$\mathsf{bi} \sqcap \mathsf{bi} \sqcap \mathsf{co} = \mathsf{co}$.

**Step 3: make the compiler confirm it.** `shrink_view` is the witness: it
compiles, so `RawView` is covariant in `'a`. The output shows the view at work
after shrinking:

```text
{{#include ../../code/rust/output/ch27_variance.txt:10:10}}
```

**Step 4: ask what would go wrong with another choice.** Suppose the view were
mutable, a `RawViewMut<'a, T>` that can write through its pointer. If it were
covariant in `T`, a `RawViewMut<'a, &'static str>` could be viewed as a
`RawViewMut<'a, &'short str>`, a short-lived string written into it, and the
original owner of the `&'static str` slots would read a dangling reference: the
classic program of `ch27_mut_invariance`, in a library instead of in your code.
The right marker is `PhantomData<&'a mut T>`, which makes the type invariant in
`T` and covariant in `'a`, like `&'a mut [T]`. With `*mut T` as the pointer type,
the field `ptr` would already be invariant in `T`, and the marker would only be
needed for `'a`.

**Step 5: check the auto traits.** A raw pointer is neither `Send` nor `Sync`,
so `RawView` is neither, whatever the marker. Since the view behaves like
`&'a [T]`, which is `Send` and `Sync` exactly when `T` is `Sync`, a library would
restore that with `unsafe impl<'a, T: Sync> Send for RawView<'a, T> {}` (and the
same for `Sync`), an `unsafe` promise that Chapter 32 teaches you to justify. For
the typed identifier the marker alone decided the auto traits, and that is why
`Id<T>` used `PhantomData<fn() -> T>` rather than `PhantomData<T>`.

The whole design took one line of code. The reasoning behind that line is the
entire theory of this chapter: subtyping on lifetimes, the variance of each
field, the meet that combines them, and the classic program that tells you which
answer is unsafe.

## Common confusions

**"Rust has no subtyping."** It has subtyping between lifetimes (and between
higher-ranked function types), and through variance this subtyping reaches
every type that contains a lifetime. You use it whenever a `&'static str` is
passed where a shorter `&str` is expected.

**"`&mut T` is invariant."** It is invariant in `T` and covariant in its
lifetime. Shortening the loan is always safe; changing what it points to is not.

**"Contravariance is an exotic corner case."** Every callback parameter is a
contravariant position. In Rust it shows up mostly with function pointers and
closures that take references, and in the `PhantomData<fn(T)>` marker.

**"Variance is declared."** In C#, Kotlin and Scala you declare it (`in`/`out`,
`-T`/`+T`). In Rust it is always inferred from the fields; `PhantomData` is how
you influence it.

**"A coercion is a kind of subtyping."** A coercion converts a value, may run
code, may change the representation, and does not lift through type
constructors. A subtyping step reuses the value unchanged and lifts according to
variance.

**"Lean's subtypes are subtyping."** A value of `{x // p x}` is a pair of a value
and a proof; to use it as an `α` you take its `.val`, which is a coercion. Lean
has no subsumption rule.

## Summary

- Subtyping $\sigma <: \tau$ enters a type system through the subsumption rule
  T-Sub. It is a preorder, hence a thin category, and it makes typing
  non-syntax-directed, which algorithmic formulations fix.
- Rust's only subtyping is on lifetimes: `'long: 'short` gives
  `&'long T <: &'short T`. It is pure inclusion: no code runs.
- Variance says how subtyping lifts through a type constructor: covariant,
  contravariant, invariant or bivariant. Functions are contravariant in their
  argument; `&'a T` is covariant in both parameters; `&'a mut T`, `Cell<T>` and
  `*mut T` are invariant in `T`.
- `&mut T` must be invariant: with covariance, the classic `overwrite` program
  stores a short-lived reference in a `'static` slot. Reading is covariant,
  writing contravariant, both invariant.
- Rust infers the variance of structs from their fields (a meet over
  occurrences, a product along nesting). Unused parameters are rejected (E0392);
  `PhantomData` chooses variance and auto traits.
- Variance is functoriality: covariant types are functors from the category of
  lifetimes, contravariant ones from its opposite. Variances form a commutative
  monoid under composition, with a meet for combining occurrences, and in Lean
  variance inference is proved sound.
- In a tiny language whose types are refinements, subsumption is proved sound,
  the contravariant arrow rule is exactly what the proof needs, a covariant one
  is refuted, and transitivity is admissible for the algorithm.
- Coercions (deref, unsizing, `&mut` to `&`, function pointers) are conversions,
  not subtyping. Lean has coercions (`↑`, `Coe`) and subtypes (refinements), but
  no subtyping.

## Exercises

1. Determine the variance in `'a` and in `T` of
   `struct Callback<'a, T> { f: fn(&'a T) -> usize }`. Confirm your answer by
   writing witness functions in the style of `ch27_variance.rs`, and show that
   the opposite directions do not compile.
   *Hint:* both parameters occur only inside the argument of a function pointer.

2. Assume, contrary to fact, that `Cell<T>` were covariant in `T`. Write a safe
   Rust program that would then read a dangling reference, modeled on
   `ch27_mut_invariance.rs`. Then compile it and read the actual error.
   *Hint:* create a `Cell<&'static str>`, view it as a `&Cell<&'short str>`, and
   `set` a reference to a local `String`.

3. Why is it safe for `&'a mut T` to be covariant in `'a`? Give an informal
   argument in terms of permissions (Chapter 26), and a witness function.
   *Hint:* `shrink_mut` in `ch27_variance.rs` is the witness. What can the
   holder of a shorter loan do that the holder of the longer loan could not?

4. In `code/lean/Book/Ch27/Variance.lean`, prove that `meet` is commutative,
   associative and idempotent, and that `bi` is its unit, so that the variances
   form a semilattice. Then prove `Variance.apply_meet` again, from these laws,
   for `v ⊓ v`.
   *Hint:* `cases v <;> cases w <;> rfl` for the laws.

5. Add a constructor `ptrMut (t : RTy L)`, standing for `*mut T`, to `RTy`, with
   an `RSub` rule and a `var` case, and repair `RTy.var_sound`. Which existing
   case does your proof resemble?
   *Hint:* `*mut T` is invariant in `T`, like `Cell<T>`.

6. Add pair types to `Subtyping.lean`: a shape `prod s t`, values
   `s.Val × t.Val`, a type `σ ⊗ τ` with `Holds` componentwise, the covariant
   rule S-Pair, and the corresponding case of `subtype`. Repair `Sub.sound`,
   `subtype_sound`, `subtype_trans` and `subtype_complete`.
   *Hint:* every new case follows the arrow case, but without the flip.
