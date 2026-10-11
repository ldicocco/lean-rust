// harness: compile-fail E0004
//! Rule +E needs one branch per summand: a `match` that forgets a variant is
//! rejected.

// ANCHOR: payment
enum Payment {
    Card { last4: u16 },
    Invoice { days: u32 },
    Voucher(u32),
}

fn describe(p: &Payment) -> String {
    match p {
        Payment::Card { last4 } => format!("card ending in {last4}"),
        Payment::Invoice { days } => format!("invoice, due in {days} days"),
    }
}
// ANCHOR_END: payment
