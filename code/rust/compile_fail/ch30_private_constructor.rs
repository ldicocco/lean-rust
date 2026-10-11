// harness: compile-fail E0603
//! A newtype with a private field can only be built through its constructor.
mod percent {
    pub struct Percent(u8);

    impl Percent {
        pub fn new(value: u8) -> Option<Percent> {
            if value <= 100 {
                Some(Percent(value))
            } else {
                None
            }
        }
    }
}

// ANCHOR: forge
pub fn forge() -> percent::Percent {
    percent::Percent(250)
}
// ANCHOR_END: forge
