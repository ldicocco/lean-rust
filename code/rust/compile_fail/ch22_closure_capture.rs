// harness: compile-fail E0382
//! A closure that uses a variable by value captures it: the closure owns it.

pub struct Conn;

fn send(c: Conn, msg: String) -> Conn {
    drop(msg);
    c
}

// ANCHOR: capture
fn capture(c: Conn, msg: String) -> (impl FnOnce() -> Conn, String) {
    let f = || send(c, msg);
    (f, msg)
}
// ANCHOR_END: capture
