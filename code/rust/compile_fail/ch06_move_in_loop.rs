// harness: compile-fail E0382
//! A loop body that moves a value would use it once per iteration: that is
//! contraction in disguise, and it is refused.

pub struct Connection {
    pub host: String,
}

pub fn send(conn: Connection, order: u32) {
    println!("order {order} via {}", conn.host);
}

// ANCHOR: send_all
pub fn send_all(conn: Connection, orders: Vec<u32>) {
    for order in orders {
        send(conn, order);
    }
}
// ANCHOR_END: send_all
