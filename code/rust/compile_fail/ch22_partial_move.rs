// harness: compile-fail E0382
//! Rust tracks moves per place: after `p.0` is moved, `p.1` is still usable,
//! but `p` as a whole is not.

pub struct File;

// ANCHOR: split
fn split(p: (String, File)) -> (String, (String, File)) {
    let s = p.0;
    (s, p)
}
// ANCHOR_END: split
