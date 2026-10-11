// harness: compile-fail E0382
//! A value moved on one path is "maybe uninitialized" where the paths merge.

fn archive(job: String) -> usize {
    job.len()
}

// ANCHOR: conditional_move
fn conditional_move(urgent: bool) -> usize {
    let job = String::from("backup");
    if urgent {
        archive(job);
    }
    job.len()
}
// ANCHOR_END: conditional_move
