// harness: run
//! Typestate: protocol states as types. A database connection whose states
//! are type parameters (sealed, with `PhantomData`), and a lab instrument whose
//! states carry data, with a destructor that complains when a measurement is
//! abandoned half-way.
//!
//! Run with: `cargo run --example ch25_typestate`

mod connection {
    use std::marker::PhantomData;

    // ANCHOR: states
    mod sealed {
        /// Only this module can implement `Sealed`, so only the three states
        /// below can ever implement `State`.
        pub trait Sealed {}
    }

    /// The states of the protocol: a closed set of types.
    pub trait State: sealed::Sealed {
        const NAME: &'static str;
    }

    /// States in which the connection is open.
    pub trait Open: State {}

    // Empty enums: types with no values, used only as labels.
    pub enum Closed {}
    pub enum Connected {}
    pub enum Authenticated {}

    impl sealed::Sealed for Closed {}
    impl sealed::Sealed for Connected {}
    impl sealed::Sealed for Authenticated {}
    impl State for Closed {
        const NAME: &'static str = "Closed";
    }
    impl State for Connected {
        const NAME: &'static str = "Connected";
    }
    impl State for Authenticated {
        const NAME: &'static str = "Authenticated";
    }
    impl Open for Connected {}
    impl Open for Authenticated {}
    // ANCHOR_END: states

    // ANCHOR: connection_struct
    /// A connection in state `S`. The state exists only in the type:
    /// `PhantomData<S>` has size zero.
    #[must_use = "transitions return the connection in its new state"]
    pub struct Connection<S: State> {
        host: String,
        _state: PhantomData<S>,
    }

    impl<S: State> Connection<S> {
        /// Available in every state.
        pub fn describe(&self) -> String {
            format!("{} [{}]", self.host, S::NAME)
        }

        /// Change the state: same data, new type.
        fn into_state<T: State>(self) -> Connection<T> {
            Connection {
                host: self.host,
                _state: PhantomData,
            }
        }
    }

    // ANCHOR_END: connection_struct

    // ANCHOR: transitions
    impl Connection<Closed> {
        pub fn new(host: &str) -> Self {
            Connection {
                host: host.to_string(),
                _state: PhantomData,
            }
        }

        pub fn connect(self) -> Connection<Connected> {
            self.into_state()
        }
    }

    impl Connection<Connected> {
        /// A fallible transition: on failure, the caller gets the connection
        /// back, still in state `Connected`.
        pub fn login(
            self,
            user: &str,
            password: &str,
        ) -> Result<Connection<Authenticated>, Connection<Connected>> {
            if user == "lab" && password == "secret" {
                Ok(self.into_state())
            } else {
                Err(self)
            }
        }
    }

    impl Connection<Authenticated> {
        /// Does not change the state: takes `&self`, not `self`.
        pub fn query(&self, sql: &str) -> String {
            format!("result of `{sql}` from {}", self.host)
        }

        pub fn logout(self) -> Connection<Connected> {
            self.into_state()
        }
    }

    impl<S: Open> Connection<S> {
        /// Close from any open state.
        pub fn close(self) -> Connection<Closed> {
            self.into_state()
        }
    }
    // ANCHOR_END: transitions
}

mod instrument {
    // ANCHOR: instrument_states
    /// The states carry data: what is known in that state, and nothing more.
    pub struct Idle;
    pub struct Calibrated {
        offset: f64,
    }
    pub struct Measuring {
        offset: f64,
        samples: Vec<f64>,
        armed: bool,
    }

    pub struct Instrument<S> {
        name: String,
        state: S,
    }
    // ANCHOR_END: instrument_states

    // ANCHOR: instrument_transitions
    impl Instrument<Idle> {
        pub fn new(name: &str) -> Self {
            Instrument {
                name: name.to_string(),
                state: Idle,
            }
        }

        /// Compare a reading of a known reference with its true value.
        pub fn calibrate(self, reference: f64, reading: f64) -> Instrument<Calibrated> {
            let offset = reference - reading;
            Instrument {
                name: self.name,
                state: Calibrated { offset },
            }
        }
    }

    impl Instrument<Calibrated> {
        pub fn start(self) -> Instrument<Measuring> {
            let offset = self.state.offset;
            let state = Measuring {
                offset,
                samples: Vec::new(),
                armed: true,
            };
            Instrument {
                name: self.name,
                state,
            }
        }

        pub fn power_down(self) -> Instrument<Idle> {
            Instrument {
                name: self.name,
                state: Idle,
            }
        }
    }

    impl Instrument<Measuring> {
        pub fn record(&mut self, raw: f64) {
            self.state.samples.push(raw + self.state.offset);
        }

        /// Finish the measurement: back to `Calibrated`, with the samples.
        pub fn stop(mut self) -> (Instrument<Calibrated>, Vec<f64>) {
            // `Measuring` implements `Drop`, so its fields cannot be moved out
            // (E0509): take the samples, and disarm the complaint.
            let samples = std::mem::take(&mut self.state.samples);
            self.state.armed = false;
            let state = Calibrated {
                offset: self.state.offset,
            };
            (
                Instrument {
                    name: self.name,
                    state,
                },
                samples,
            )
        }
    }

    impl<S> Instrument<S> {
        pub fn name(&self) -> &str {
            &self.name
        }
    }
    // ANCHOR_END: instrument_transitions

    // ANCHOR: complaint
    /// A destructor that complains: the protocol says a measurement must be
    /// stopped, and the type system cannot force it.
    impl Drop for Measuring {
        fn drop(&mut self) {
            if self.armed {
                let n = self.samples.len();
                println!("  warning: measurement abandoned, {n} sample(s) lost");
            }
        }
    }
    // ANCHOR_END: complaint
}

use connection::Connection;
use instrument::Instrument;

// ANCHOR: session
fn session() {
    let conn = Connection::new("db.lab.internal");
    println!("  {}", conn.describe());
    let conn = conn.connect();
    println!("  {}", conn.describe());
    let conn = match conn.login("lab", "wrong") {
        Ok(_) => unreachable!("the password is wrong"),
        Err(conn) => {
            println!("  login failed, still {}", conn.describe());
            conn
        }
    };
    let Ok(conn) = conn.login("lab", "secret") else {
        unreachable!("the password is right");
    };
    println!("  {}", conn.describe());
    println!("  {}", conn.query("SELECT * FROM samples"));
    let conn = conn.logout().close();
    println!("  {}", conn.describe());
}
// ANCHOR_END: session

// ANCHOR: measure
fn measure() {
    let probe = Instrument::new("thermometer").calibrate(100.0, 99.5);
    let mut run = probe.start();
    for raw in [20.0, 20.5, 21.0] {
        run.record(raw);
    }
    let (probe, samples) = run.stop();
    println!("  {}: samples {samples:?}", probe.name());

    let probe = probe.power_down().calibrate(100.0, 100.0);
    let mut run = probe.start();
    run.record(22.0);
    run.record(22.5);
    println!("  dropping {} in the middle of a measurement", run.name());
} // `run` is dropped here, still in state Measuring
// ANCHOR_END: measure

fn main() {
    println!("connection:");
    session();
    println!("instrument:");
    measure();
    println!(
        "size of Connection<Authenticated>: {} bytes (a String)",
        std::mem::size_of::<Connection<connection::Authenticated>>()
    );
}
