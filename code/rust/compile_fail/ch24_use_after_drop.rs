// harness: compile-fail E0382
//! `drop` is an ordinary function that takes ownership: after `drop(conn)`
//! the variable is moved out, and using it again is rejected.

pub struct Connection {
    pub host: String,
}

// ANCHOR: use_after_drop
pub fn close_then_use(conn: Connection) -> usize {
    drop(conn);
    conn.host.len()
}
// ANCHOR_END: use_after_drop
