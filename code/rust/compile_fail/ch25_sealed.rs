// harness: compile-fail E0277
//! A sealed trait: outside its module, nobody can add a new state.

pub mod connection {
    mod sealed {
        pub trait Sealed {}
    }

    pub trait State: sealed::Sealed {}

    pub struct Closed;
    impl sealed::Sealed for Closed {}
    impl State for Closed {}
}

// ANCHOR: sealed
pub struct Hijacked;

impl connection::State for Hijacked {}
// ANCHOR_END: sealed
