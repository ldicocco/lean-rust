// harness: compile-fail E0597
//! A reference must not outlive its referent: `reading` dies at the end of the
//! inner block, but `r` is used after it.

// ANCHOR: dangling
pub fn dangling() {
    let r;
    {
        let reading = 42;
        r = &reading;
    }
    println!("{r}");
}
// ANCHOR_END: dangling
