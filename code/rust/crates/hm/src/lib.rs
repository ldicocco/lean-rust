//! Hindley-Milner type inference (algorithm W) for a small ML-like language.
//!
//! Built in Chapter 13. The pipeline is
//!
//! ```text
//! source text --parser--> Expr --infer--> principal type scheme
//!                                    \--> Diagnostic (a readable error)
//! ```
//!
//! - `types`: types with type variables, and type schemes;
//! - `syntax` and `parser`: the abstract syntax of mini-ML and its parser;
//! - `unify`: substitutions and first-order unification with the occurs check;
//! - `infer`: generalization, instantiation and algorithm W;
//! - `diagnostic`: error messages that point into the source.

pub mod diagnostic;
pub mod infer;
pub mod parser;
pub mod syntax;
pub mod types;
pub mod unify;

pub use diagnostic::Diagnostic;
pub use infer::{infer_program, trace_program};
pub use types::{Namer, Scheme, TyCon, TyVar, Type};
pub use unify::{Subst, UnifyError};

/// The principal type of a closed program, printed with readable names
/// (`forall a. a -> a`), or the rendered error message.
pub fn principal_type(source: &str) -> Result<String, String> {
    match infer_program(source) {
        Ok(scheme) => Ok(Namer::new().show_scheme(&scheme)),
        Err(diag) => Err(diag.render("input", source)),
    }
}
