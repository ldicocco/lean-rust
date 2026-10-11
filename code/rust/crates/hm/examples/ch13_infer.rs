// harness: run
//! Hindley-Milner type inference for mini-ML: the principal types of some
//! sample programs, and the difference between `let` and `fun`.
//!
//! Run with: `cargo run -p hm --example ch13_infer`

use hm::{Namer, infer_program};

// ANCHOR: programs
/// Sample programs, from the identity function to `map`.
const PROGRAMS: [&str; 9] = [
    "fun x -> x",
    "fun x y -> x",
    "fun f x -> f (f x)",
    "fun f g x -> f (g x)",
    "fun p -> (snd p, fst p)",
    "fun x -> x + 1",
    "let rec length xs =
       if null xs then 0 else 1 + length (tail xs)
     in length",
    "let rec map f xs =
       if null xs then [] else f (head xs) :: map f (tail xs)
     in map",
    "let rec map f xs =
       if null xs then [] else f (head xs) :: map f (tail xs)
     in map (fun n -> n < 3) [1, 2, 3]",
];
// ANCHOR_END: programs

// ANCHOR: let_vs_fun
/// The same computation written with `let` and with `fun`, and a `let` whose
/// variable cannot be generalized.
const POLYMORPHISM: [&str; 3] = [
    "let id = fun x -> x in (id 1, id true)",
    "(fun id -> (id 1, id true)) (fun x -> x)",
    "fun x -> let y = x in (y 1, y true)",
];
// ANCHOR_END: let_vs_fun

fn report(program: &str) {
    // Print the program as written, minus the indentation of the constant.
    for line in program.lines() {
        println!("{}", line.strip_prefix("     ").unwrap_or(line));
    }
    match infer_program(program) {
        Ok(scheme) => println!("  : {}", Namer::new().show_scheme(&scheme)),
        Err(diag) => println!("  error: {}", diag.message),
    }
}

fn main() {
    println!("== principal types ==");
    for program in PROGRAMS {
        report(program);
    }
    println!();
    println!("== let versus fun ==");
    for program in POLYMORPHISM {
        report(program);
    }
}
