// harness: compile-fail E0644
//! Self-application again: a closure whose argument would have to be of the
//! closure's own type. Its type would contain itself.

// ANCHOR: self_apply
fn self_apply<F: Fn(&F)>(f: F) {
    f(&f)
}

pub fn demo() {
    self_apply(|_me| println!("called"));
}
// ANCHOR_END: self_apply
