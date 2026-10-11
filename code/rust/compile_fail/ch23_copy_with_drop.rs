// harness: compile-fail E0184
//! A type with a destructor cannot be `Copy`: every implicit copy would run
//! the destructor once more.

// ANCHOR: token
#[derive(Clone, Copy)]
struct Token {
    id: u64,
}

impl Drop for Token {
    fn drop(&mut self) {
        println!("releasing token {}", self.id);
    }
}
// ANCHOR_END: token
