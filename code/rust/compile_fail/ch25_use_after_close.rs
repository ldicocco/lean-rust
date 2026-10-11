// harness: compile-fail E0382
//! Typestate relies on affinity: `close` consumes the connection, so the old
//! state cannot be used again.

use std::marker::PhantomData;

pub struct Closed;
pub struct Connected;

pub struct Connection<S> {
    host: String,
    _state: PhantomData<S>,
}

impl Connection<Connected> {
    pub fn send(&mut self, line: &str) {
        self.host.push_str(line);
    }

    pub fn close(self) -> Connection<Closed> {
        Connection {
            host: self.host,
            _state: PhantomData,
        }
    }
}

// ANCHOR: use_after_close
pub fn finish(mut conn: Connection<Connected>) -> Connection<Closed> {
    let closed = conn.close();
    conn.send("QUIT");
    closed
}
// ANCHOR_END: use_after_close
