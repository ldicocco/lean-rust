// harness: run
//! Unification step by step: the worked examples of Chapter 13, replayed by
//! the `hm` crate with a trace of every rule it applies, followed by traces
//! of algorithm W on `twice` and on a polymorphic `let`.
//!
//! Run with: `cargo run -p hm --example ch13_unify`

use hm::parser::parse_type;
use hm::{Namer, Subst, UnifyError, trace_program};

// ANCHOR: problems
/// Pairs of types to unify. `?n` is a type variable.
const PROBLEMS: [(&str, &str); 5] = [
    ("?0 -> Int", "Bool -> ?1"),
    ("?0 -> ?0", "Int -> ?1"),
    ("List ?0 -> ?1", "?1 -> List Int"),
    ("Int -> ?0", "Bool -> ?0"),
    ("?0", "?0 -> ?1"),
];
// ANCHOR_END: problems

// ANCHOR: solve
fn solve(left: &str, right: &str) {
    let (left, right) = (parse_type(left).unwrap(), parse_type(right).unwrap());
    let mut subst = Subst::new();
    let vars: Vec<_> = (0..2).map(|_| subst.fresh()).collect();
    subst.start_trace();
    let outcome = subst.unify(&left, &right);
    for step in subst.take_trace() {
        println!("  {step}");
    }
    match outcome {
        Ok(()) => {
            // The unifier, applied to each variable, and the common instance.
            let solved: Vec<String> = vars
                .iter()
                .map(|v| format!("?{} = {}", v.0, subst.apply(&hm::Type::Var(*v))))
                .collect();
            println!("  unifier: {}", solved.join(", "));
            assert_eq!(subst.apply(&left), subst.apply(&right));
            println!("  both sides become {}", subst.apply(&left));
        }
        Err(UnifyError::Mismatch(a, b)) => println!("  fails: {a} and {b} clash"),
        Err(UnifyError::Occurs(v, t)) => println!("  fails: ?{} occurs in {t}", v.0),
    }
}
// ANCHOR_END: solve

fn main() {
    for (i, (left, right)) in PROBLEMS.iter().enumerate() {
        println!("({}) {left}  ~  {right}", i + 1);
        solve(left, right);
    }
    for program in [
        "fun f x -> f (f x)",
        "let id = fun x -> x in (id 1, id true)",
    ] {
        println!();
        println!("algorithm W on: {program}");
        let (trace, result) = trace_program(program);
        for line in trace {
            println!("  {line}");
        }
        let scheme = result.expect("the program is well typed");
        println!("principal type: {}", Namer::new().show_scheme(&scheme));
    }
}
