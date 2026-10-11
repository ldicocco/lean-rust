//! Arith: a tiny typed expression language with a type checker and an evaluator.
//!
//! Built in Chapter 3. The pieces follow the chapter:
//!
//! - [`syntax`]: the abstract syntax (types and expressions as enums), with a
//!   printer that inserts only the parentheses that are needed;
//! - [`parse`]: concrete syntax, a recursive-descent parser from text to trees;
//! - [`typing`]: the typing judgment Γ ⊢ e : τ, derivation trees as data, and a
//!   checker that either builds a derivation or explains why none exists;
//! - [`eval`]: a big-step evaluator that does not look at types, and can
//!   therefore get stuck on ill-typed programs.
//!
//! The Lean formalization of the same language, with the proof that the
//! checker is sound, is in `code/lean/Book/Ch03/`.

pub mod eval;
pub mod parse;
pub mod syntax;
pub mod typing;

pub use eval::{Env, EvalError, Value, eval};
pub use parse::{ParseError, parse};
pub use syntax::{Expr, Ty};
pub use typing::{Ctx, Derivation, Judgment, Rule, TypeError, check, type_of};

#[cfg(test)]
mod safety_tests {
    //! Type safety, tested: on thousands of random closed expressions, every
    //! expression the checker accepts evaluates to a value of the type the
    //! checker predicted, and never gets stuck. Chapter 9 proves the analogous
    //! theorem for a richer language; here we only test it.

    use super::*;
    use crate::syntax::build::*;

    /// SplitMix64: a tiny, well-known pseudo-random generator. Seeded, so the
    /// tests are deterministic.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    const NAMES: [&str; 3] = ["x", "y", "z"];

    /// A random expression of depth at most `depth`. Most of them are ill
    /// typed; enough of them are well typed to make the test meaningful.
    fn random_expr(rng: &mut Rng, depth: u32) -> Expr {
        let leaf = depth == 0 || rng.below(4) == 0;
        if leaf {
            return match rng.below(3) {
                0 => num(rng.below(10)),
                1 => boolean(rng.below(2) == 0),
                _ => var(NAMES[rng.below(3) as usize]),
            };
        }
        let d = depth - 1;
        match rng.below(4) {
            0 => add(random_expr(rng, d), random_expr(rng, d)),
            1 => eq(random_expr(rng, d), random_expr(rng, d)),
            2 => ite(
                random_expr(rng, d),
                random_expr(rng, d),
                random_expr(rng, d),
            ),
            _ => {
                let x = NAMES[rng.below(3) as usize];
                let_in(x, random_expr(rng, d), random_expr(rng, d))
            }
        }
    }

    // ANCHOR: safety_test
    #[test]
    fn well_typed_programs_do_not_go_wrong() {
        let mut rng = Rng(2024);
        let mut well_typed = 0;
        for _ in 0..20_000 {
            let e = random_expr(&mut rng, 5);
            if let Ok(d) = check(&Ctx::new(), &e) {
                well_typed += 1;
                assert!(d.verify(), "invalid derivation for {e}");
                match eval(&Env::new(), &e) {
                    Ok(v) => assert_eq!(v.ty(), d.ty(), "wrong type of value for {e}"),
                    Err(err) => panic!("well-typed {e} went wrong: {err}"),
                }
            }
        }
        // Make sure the test is not vacuous.
        assert!(well_typed > 2_000, "only {well_typed} well-typed samples");
    }
    // ANCHOR_END: safety_test

    #[test]
    fn printing_then_parsing_gives_back_the_same_tree() {
        let mut rng = Rng(7);
        for _ in 0..5_000 {
            let e = random_expr(&mut rng, 5);
            assert_eq!(parse(&e.to_string()), Ok(e.clone()), "round trip of {e}");
        }
    }
}
