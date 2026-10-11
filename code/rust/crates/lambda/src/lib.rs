//! The untyped lambda calculus: named and de Bruijn terms, substitution, reduction strategies.
//!
//! Built in Chapter 7.
//!
//! - [`term`]: named terms, free variables, α-equivalence, capture-avoiding
//!   substitution and a pretty printer;
//! - [`parse`]: a parser, so that terms can be written as text (`λf. λx. f x`);
//! - [`debruijn`]: nameless terms, shifting and substitution;
//! - [`reduce`]: normal-order, call-by-name and call-by-value reduction with a
//!   step limit ("fuel");
//! - [`church`]: Church booleans, pairs and numerals, arithmetic, `Ω`, `Y`, `Z`.

pub mod church;
pub mod debruijn;
pub mod parse;
pub mod reduce;
pub mod term;

pub use debruijn::{DbTerm, to_de_bruijn};
pub use parse::{ParseError, parse};
pub use reduce::{Reduction, Strategy, is_normal, reduce, step, trace};
pub use term::{Term, app, apps, lam, var};
