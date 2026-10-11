// harness: compile-fail E0599
//! A protocol violation is a type error: `query` exists only on an
//! authenticated connection.

use std::marker::PhantomData;

pub struct Connected;
pub struct Authenticated;

pub struct Connection<S> {
    host: String,
    _state: PhantomData<S>,
}

impl Connection<Connected> {
    pub fn login(self, _password: &str) -> Connection<Authenticated> {
        Connection {
            host: self.host,
            _state: PhantomData,
        }
    }
}

impl Connection<Authenticated> {
    pub fn query(&self, sql: &str) -> String {
        format!("{}: {sql}", self.host)
    }
}

// ANCHOR: wrong_state
pub fn report(conn: Connection<Connected>) -> String {
    conn.query("SELECT * FROM samples")
}
// ANCHOR_END: wrong_state
