//! A type checker and an interpreter for the core calculus of borrowing of
//! Chapter 28: owned locations (`Box τ`), moves, drops, `Copy`, shared and
//! mutable borrows with lexically scoped lifetimes, reborrowing and the escape
//! check.
//!
//! - [`syntax`]: types and terms, and how to print them;
//! - [`parse`]: a parser for programs such as
//!   `fn twice<'a>(r: &'a mut Int) { ... }`;
//! - [`check`]: the typing rules, producing derivation trees or errors;
//! - [`eval`]: the small-step semantics over a store with loan states.
//!
//! Built in Chapter 28.

pub mod check;
pub mod eval;
pub mod parse;
pub mod syntax;

pub use check::{Derivation, TypeError, check, check_program};
pub use eval::{Machine, Outcome};
pub use parse::{Program, parse_program, parse_term, parse_ty};
pub use syntax::{BorrowKind, Term, Ty};
