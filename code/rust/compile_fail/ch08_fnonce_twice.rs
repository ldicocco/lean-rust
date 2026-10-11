// harness: compile-fail E0382
//! A closure that moves a captured value out of itself is only `FnOnce`: it can
//! be called once, because the call consumes it.

// ANCHOR: send_twice
pub fn send_twice() {
    let report = String::from("Q3 report");
    let send = move || report; // returns `report`, moving it out
    let first = send();
    let second = send();
}
// ANCHOR_END: send_twice
