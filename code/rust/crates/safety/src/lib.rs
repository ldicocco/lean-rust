//! Small-step semantics for the simply typed λ-calculus with booleans and
//! natural numbers, and property-based tests of progress, preservation and
//! determinism (Chapter 9).
//!
//! The modules follow the Lean development in `code/lean/Book/Ch09/`:
//!
//! - [`syntax`]: types, terms in de Bruijn notation, a printer;
//! - [`subst`]: renaming, shifting and substitution;
//! - [`typing`]: the type checker (and a deliberately broken variant);
//! - [`eval`]: the step relation as a function returning every step, and the
//!   call-by-value evaluator;
//! - [`rng`], [`generate`]: a seeded PRNG and generators of random terms;
//! - [`props`]: the property checks, the fuzzing driver and a shrinker.

pub mod eval;
pub mod generate;
pub mod props;
pub mod rng;
pub mod subst;
pub mod syntax;
pub mod typing;
