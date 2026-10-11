// harness: run
//! Chapter 23: the affine checker extended with `Copy` and `Clone`. The same
//! program is rejected by the pure affine discipline of Chapter 22 and
//! accepted with `Copy`; then programs that use `Copy` structs, shared
//! references, `.clone()` and `Rc`; then the errors of the extension, modeled
//! on rustc's E0204, E0184, E0382 and E0599; and the chapter's walkthrough,
//! a measurement session that uses `Copy`, `Clone` and an affine device.
//!
//! Run with: `cargo run -p affine --example ch23_copy`

use affine::{Discipline, Show, check_source, render};

const TWICE: &str = include_str!("programs/ch23_twice.aff");
const COPY: &str = include_str!("programs/ch23_copy.aff");
const ERRORS: &str = include_str!("programs/ch23_errors.aff");
const SESSION: &str = include_str!("programs/ch23_session.aff");

// ANCHOR: main
fn main() {
    println!("== ch23_twice.aff, pure λ^aff (Chapter 22)");
    print!(
        "{}",
        render("ch23_twice.aff", TWICE, Discipline::Affine, Show::Verdicts)
    );
    println!("== ch23_twice.aff, with Copy (Chapter 23)");
    print!(
        "{}",
        render("ch23_twice.aff", TWICE, Discipline::Copy, Show::Derivations)
    );

    println!("== ch23_copy.aff, with Copy");
    print!(
        "{}",
        render("ch23_copy.aff", COPY, Discipline::Copy, Show::Verdicts)
    );
    let report = check_source(COPY, Discipline::Copy).expect("parses");
    assert!(report.errors.is_empty());
    // Without Copy and Clone, every one of these functions is rejected.
    let affine = check_source(COPY, Discipline::Affine).expect("parses");
    assert_eq!(affine.errors.len(), report.functions.len());

    println!("== ch23_errors.aff, with Copy");
    print!(
        "{}",
        render("ch23_errors.aff", ERRORS, Discipline::Copy, Show::Verdicts)
    );
    let codes: Vec<String> = check_source(ERRORS, Discipline::Copy)
        .expect("parses")
        .errors
        .into_iter()
        .filter_map(|d| d.code)
        .collect();
    assert_eq!(codes, ["E0204", "E0184", "E0382", "E0599", "E0382"]);

    println!("== ch23_session.aff, with Copy");
    print!(
        "{}",
        render("ch23_session.aff", SESSION, Discipline::Copy, Show::Compact)
    );
    let report = check_source(SESSION, Discipline::Copy).expect("parses");
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.errors.len(), 2);
}
// ANCHOR_END: main
