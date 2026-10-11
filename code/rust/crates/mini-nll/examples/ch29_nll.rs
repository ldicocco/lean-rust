// harness: run
//! The four borrow checkers of Chapter 29 on the same nine programs, and one
//! of the errors, printed the way rustc prints it.
//!
//! Run with: `cargo run -p mini-nll --example ch29_nll`

use mini_nll::{Checker, check, programs};

fn main() {
    // ANCHOR: table
    let mut header = format!("{:<22}", "program");
    for checker in Checker::ALL {
        header += &format!(" {:<12}", checker.name());
    }
    println!("{}", header.trim_end());
    for body in programs::all() {
        let mut row = format!("{:<22}", body.name);
        for checker in Checker::ALL {
            let codes: Vec<&str> =
                check(&body, checker).iter().map(|d| d.code).collect();
            let cell = if codes.is_empty() {
                "ok".to_string()
            } else {
                codes.join(",")
            };
            row += &format!(" {cell:<12}");
        }
        println!("{}", row.trim_end());
    }
    // ANCHOR_END: table
    println!();
    let body = programs::still_used();
    for d in check(&body, Checker::Nll) {
        print!("{}", d.render(&body));
    }
}
