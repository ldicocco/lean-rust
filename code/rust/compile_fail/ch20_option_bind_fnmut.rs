// harness: compile-fail E0507
//! A `bind` that takes `FnMut` (so that `Vec` can implement it) rejects, for
//! `Option`, closures that give away what they captured.

// ANCHOR: give_away
fn bind_option<A, B, F>(m: Option<A>, mut f: F) -> Option<B>
where
    F: FnMut(A) -> Option<B>,
{
    match m {
        Some(a) => f(a),
        None => None,
    }
}

pub fn ticket(id: Option<u32>, customer: String) -> Option<(u32, String)> {
    bind_option(id, move |n| Some((n, customer)))
}
// ANCHOR_END: give_away
