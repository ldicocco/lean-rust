//! The simply typed lambda calculus: a bidirectional type checker and an environment-based evaluator.
//!
//! Built in Chapter 8.
//!
//! - [`syntax`]: types (`Unit`, `Bool`, `Nat`, `→`, `×`, `+`) and terms, with a
//!   printer;
//! - [`parse`]: a parser for the same concrete syntax;
//! - [`check`]: bidirectional type checking (`infer` synthesizes, `check`
//!   checks against a given type) with readable errors;
//! - [`eval`]: call-by-value evaluation with environments and closures.

pub mod check;
pub mod eval;
pub mod parse;
pub mod syntax;

pub use check::{TypeError, check, check_with_trace, infer};
pub use eval::{Closure, Stuck, Value, run};
pub use parse::{ParseError, parse_term, parse_type};
pub use syntax::{Term, Ty};
