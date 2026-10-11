// harness: run
//! Chapter 22: the affine checker on the programs of the chapter. For every
//! function that it accepts it prints the derivation that it reconstructs from
//! its input and output contexts (each judgment shows the part of the context
//! that the subterm consumed), and the variables that were discarded unused.
//! The last program is the chapter's walkthrough: an upload, with two bugs.
//!
//! Run with: `cargo run -p affine --example ch22_affine_checker`

use affine::{Discipline, Show, check_source, render};

// ANCHOR: main
const ACCEPTED: &str = include_str!("programs/ch22_accepted.aff");
const UPLOAD: &str = include_str!("programs/ch22_upload.aff");

fn main() {
    let out = render(
        "ch22_accepted.aff",
        ACCEPTED,
        Discipline::Affine,
        Show::Derivations,
    );
    print!("{out}");
    let report = check_source(ACCEPTED, Discipline::Affine).expect("parses");
    assert!(report.errors.is_empty());
    assert_eq!(report.functions.len(), 5);

    println!();
    let out = render(
        "ch22_upload.aff",
        UPLOAD,
        Discipline::Affine,
        Show::Derivations,
    );
    print!("{out}");
    // `upload` and `upload_leaky` are accepted; `upload_twice` is not.
    let report = check_source(UPLOAD, Discipline::Affine).expect("parses");
    assert_eq!(report.functions.len(), 2);
    assert_eq!(report.errors.len(), 1);
    assert_eq!(report.functions[1].dropped, ["opened"]);
}
// ANCHOR_END: main
