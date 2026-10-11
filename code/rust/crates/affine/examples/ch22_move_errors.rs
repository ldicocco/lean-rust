// harness: run
//! Chapter 22: the affine checker on programs that it rejects. The errors are
//! modeled on rustc's E0382, "use of moved value".
//!
//! Run with: `cargo run -p affine --example ch22_move_errors`

use affine::{Discipline, Show, check_source, render};

// ANCHOR: programs
const PROGRAMS: [(&str, &str); 6] = [
    ("ch22_dup.aff", include_str!("programs/ch22_dup.aff")),
    ("ch22_coin.aff", include_str!("programs/ch22_coin.aff")),
    ("ch22_route.aff", include_str!("programs/ch22_route.aff")),
    ("ch22_split.aff", include_str!("programs/ch22_split.aff")),
    (
        "ch22_capture.aff",
        include_str!("programs/ch22_capture.aff"),
    ),
    ("ch22_twice.aff", include_str!("programs/ch22_twice.aff")),
];

fn main() {
    for (i, (file, src)) in PROGRAMS.iter().enumerate() {
        if i > 0 {
            println!();
        }
        print!("{}", render(file, src, Discipline::Affine, Show::Verdicts));
        // Each program has exactly one error, and it is E0382.
        let report = check_source(src, Discipline::Affine).expect("parses");
        assert_eq!(report.errors.len(), 1);
        assert_eq!(report.errors[0].code.as_deref(), Some("E0382"));
    }
}
// ANCHOR_END: programs
