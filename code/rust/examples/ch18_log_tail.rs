// harness: run
//! Putting free theorems to work: `latest<T>` keeps the last `n` entries of a
//! log without looking at them, so formatting can be moved after it. The two
//! pipelines give the same lines; the second formats 3 entries instead of 1000.
//!
//! Run with: `cargo run --example ch18_log_tail`

use std::cell::Cell;

// ANCHOR: event
#[derive(Clone, Debug, PartialEq)]
enum Level {
    Info,
    Warn,
    Error,
}

impl Level {
    fn label(&self) -> &'static str {
        match self {
            Level::Info => "INFO",
            Level::Warn => "WARN",
            Level::Error => "ERROR",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Event {
    seq: u32,
    level: Level,
    message: String,
}

/// A synthetic log: every seventh event is a warning, every 50th an error.
fn sample_log(len: u32) -> Vec<Event> {
    (1..=len)
        .map(|seq| Event {
            seq,
            level: if seq % 50 == 0 {
                Level::Error
            } else if seq % 7 == 0 {
                Level::Warn
            } else {
                Level::Info
            },
            message: format!("request {seq} handled"),
        })
        .collect()
}
// ANCHOR_END: event

// ANCHOR: latest
/// The last `n` entries. The signature says it all: for every `T`, a
/// `Vec<T>` in, a `Vec<T>` out, and no bound on `T`. It can drop, keep and
/// reorder entries, but it cannot look at them.
fn latest<T>(mut log: Vec<T>, n: usize) -> Vec<T> {
    let start = log.len().saturating_sub(n);
    log.split_off(start)
}
// ANCHOR_END: latest

fn main() {
    // ANCHOR: pipelines
    let log = sample_log(1000);
    let calls = Cell::new(0u32);
    let render = |e: Event| {
        calls.set(calls.get() + 1);
        format!("#{:04} {:<5} {}", e.seq, e.level.label(), e.message)
    };

    // Format everything, then keep the last three lines.
    calls.set(0);
    let eager: Vec<String> = latest(log.clone().into_iter().map(render).collect(), 3);
    let eager_calls = calls.get();

    // Keep the last three events, then format them.
    calls.set(0);
    let lazy: Vec<String> = latest(log, 3).into_iter().map(render).collect();
    let lazy_calls = calls.get();

    assert_eq!(eager, lazy);
    for line in &lazy {
        println!("{line}");
    }
    println!("render called {eager_calls} times (map, then latest)");
    println!("render called {lazy_calls} times (latest, then map)");
    // ANCHOR_END: pipelines
}
