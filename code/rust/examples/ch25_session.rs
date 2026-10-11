// harness: run
//! Session types, briefly: a protocol as a type, and its dual computed by the
//! trait system. `Chan::pair` creates two endpoints with dual protocols; each
//! endpoint can only send and receive what its protocol allows, in order.
//!
//! Run with: `cargo run --example ch25_session`

use std::cell::RefCell;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::rc::Rc;

// ANCHOR: session_types
/// "Send a `T`, then continue as `S`."
pub struct Send<T, S>(PhantomData<(T, S)>);
/// "Receive a `T`, then continue as `S`."
pub struct Recv<T, S>(PhantomData<(T, S)>);
/// "The conversation is over."
pub struct End;

/// Every session type has a dual: the same protocol seen from the other side.
pub trait Session {
    type Dual: Session;
}

impl Session for End {
    type Dual = End;
}
impl<T, S: Session> Session for Send<T, S> {
    type Dual = Recv<T, S::Dual>;
}
impl<T, S: Session> Session for Recv<T, S> {
    type Dual = Send<T, S::Dual>;
}
// ANCHOR_END: session_types

// ANCHOR: protocol
/// The client names a sensor, receives its reading, sends back a correction
/// and learns whether the corrected value is in range.
type Client = Send<u32, Recv<f64, Send<f64, Recv<bool, End>>>>;
/// The server's protocol is computed, not written by hand.
type Server = <Client as Session>::Dual;

/// Compiles only if the dual of `A` is `B`.
fn assert_dual<A: Session<Dual = B>, B>() {}
// ANCHOR_END: protocol

// ANCHOR: channel
/// What travels on the wire.
#[derive(Debug)]
enum Msg {
    Nat(u32),
    Real(f64),
    Flag(bool),
}

/// The payload types the wire can carry.
trait Payload: Sized {
    fn wrap(self) -> Msg;
    fn unwrap(msg: Msg) -> Option<Self>;
}

impl Payload for u32 {
    fn wrap(self) -> Msg {
        Msg::Nat(self)
    }
    fn unwrap(msg: Msg) -> Option<Self> {
        if let Msg::Nat(n) = msg { Some(n) } else { None }
    }
}

impl Payload for f64 {
    fn wrap(self) -> Msg {
        Msg::Real(self)
    }
    fn unwrap(msg: Msg) -> Option<Self> {
        if let Msg::Real(x) = msg {
            Some(x)
        } else {
            None
        }
    }
}

impl Payload for bool {
    fn wrap(self) -> Msg {
        Msg::Flag(self)
    }
    fn unwrap(msg: Msg) -> Option<Self> {
        if let Msg::Flag(b) = msg {
            Some(b)
        } else {
            None
        }
    }
}

type Queue = Rc<RefCell<VecDeque<Msg>>>;

/// An endpoint that must follow protocol `S`. Every operation consumes the
/// endpoint and returns it at the next step of the protocol.
struct Chan<S> {
    incoming: Queue,
    outgoing: Queue,
    _protocol: PhantomData<S>,
}

impl<S: Session> Chan<S> {
    /// Two connected endpoints, with dual protocols.
    fn pair() -> (Chan<S>, Chan<S::Dual>) {
        let a_to_b: Queue = Rc::default();
        let b_to_a: Queue = Rc::default();
        let a = Chan {
            incoming: Rc::clone(&b_to_a),
            outgoing: Rc::clone(&a_to_b),
            _protocol: PhantomData,
        };
        let b = Chan {
            incoming: a_to_b,
            outgoing: b_to_a,
            _protocol: PhantomData,
        };
        (a, b)
    }
}

impl<S> Chan<S> {
    fn advance<S2>(self) -> Chan<S2> {
        Chan {
            incoming: self.incoming,
            outgoing: self.outgoing,
            _protocol: PhantomData,
        }
    }
}

impl<T: Payload, S> Chan<Send<T, S>> {
    fn send(self, value: T) -> Chan<S> {
        self.outgoing.borrow_mut().push_back(value.wrap());
        self.advance()
    }
}

impl<T: Payload, S> Chan<Recv<T, S>> {
    fn recv(self) -> (T, Chan<S>) {
        let msg = self.incoming.borrow_mut().pop_front();
        let value = msg
            .and_then(T::unwrap)
            .expect("the peer follows the dual protocol");
        (value, self.advance())
    }
}

impl Chan<End> {
    fn close(self) {}
}
// ANCHOR_END: channel

fn main() {
    // ANCHOR: run
    assert_dual::<Client, Server>();
    assert_dual::<Server, Client>();
    let short = |name: &str| name.replace("ch25_session::", "");
    println!("Client = {}", short(std::any::type_name::<Client>()));
    println!("Server = {}", short(std::any::type_name::<Server>()));

    // The two sides take turns (in a real program, two threads or tasks).
    let (client, server) = Chan::<Client>::pair();
    let client = client.send(7_u32);
    let (sensor, server) = server.recv();
    let server = server.send(21.5_f64);
    let (reading, client) = client.recv();
    let client = client.send(reading - 0.5);
    let (corrected, server) = server.recv();
    let server = server.send((15.0..=25.0).contains(&corrected));
    let (in_range, client) = client.recv();
    client.close();
    server.close();
    println!("sensor {sensor}: reading {reading}, corrected {corrected}");
    println!("in range: {in_range}");
    // ANCHOR_END: run
}
