// harness: compile-fail E0382
//! `bind` for `Vec` cannot take an `FnOnce`: it calls `f` once per element.

// ANCHOR: bind_once
pub fn bind_vec<A, B, F: FnOnce(A) -> Vec<B>>(m: Vec<A>, f: F) -> Vec<B> {
    let mut out = Vec::new();
    for a in m {
        out.extend(f(a));
    }
    out
}
// ANCHOR_END: bind_once
