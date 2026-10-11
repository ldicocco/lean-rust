// harness: compile-fail E0597
//! `fn(T)` is contravariant in `T`: a function that needs `&'static str` cannot
//! stand in for one that must accept a short-lived `&str`.

// ANCHOR: callback
fn needs_static(msg: &'static str) -> usize {
    msg.len()
}

fn call_with<'a>(callback: fn(&'a str) -> usize, msg: &'a str) -> usize {
    callback(msg)
}

pub fn report() {
    let msg = String::from("built at run time");
    call_with(needs_static, &msg);
}
// ANCHOR_END: callback
