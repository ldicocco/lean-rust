// harness: compile-fail E0366
//! A destructor cannot be written for a single state: `Drop` must be
//! implemented for every `Instrument<S>` or for none.

pub struct Idle;
pub struct Measuring;

pub struct Instrument<S> {
    pub name: String,
    pub state: S,
}

// ANCHOR: drop_one_state
impl Drop for Instrument<Measuring> {
    fn drop(&mut self) {
        println!("{} dropped while measuring", self.name);
    }
}
// ANCHOR_END: drop_one_state
