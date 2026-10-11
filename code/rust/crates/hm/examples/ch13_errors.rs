// harness: run
//! Type errors in mini-ML, rendered in the style of rustc: the occurs check,
//! a `fun`-bound variable used at two types, a `let` that cannot be
//! generalized, incompatible branches and polymorphic recursion.
//!
//! Run with: `cargo run -p hm --example ch13_errors`

use hm::infer_program;

// ANCHOR: programs
/// Each program is ill-typed; the name says why.
const PROGRAMS: [(&str, &str); 5] = [
    ("self-application", "fun x -> x x"),
    ("fun-bound", "(fun id -> (id 1, id true)) (fun x -> x)"),
    ("not-generalized", "fun x -> let y = x in (y 1, y true)"),
    ("branches", "fun b -> if b then 1 else false"),
    (
        "polymorphic-recursion",
        "let rec f x = if true then 0 else f 1 + f true in f",
    ),
];
// ANCHOR_END: programs

fn main() {
    for (name, program) in PROGRAMS {
        let diag = infer_program(program).expect_err("the program is ill-typed");
        print!("{}", diag.render(name, program));
        println!();
    }
}
