// harness: run
//! The hand-built miniature MIR of `maybe_archive`, printed in rustc's format.
//!
//! Compare with the real MIR in `code/rust/output/ch29_maybe_archive.nll.mir.txt`.
//!
//! Run with: `cargo run -p mini-nll --example ch29_mir`

use mini_nll::programs;

fn main() {
    let body = programs::maybe_archive();
    println!("{body}");
    let edges: Vec<String> = body
        .block_ids()
        .flat_map(|bb| {
            body.successors(bb)
                .into_iter()
                .map(move |s| format!("{bb}->{s}"))
        })
        .collect();
    println!("edges: {}", edges.join(" "));
}
