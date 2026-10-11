// harness: run
//! `async`/`.await` as an effect that the compiler supports directly: a future
//! is a computation that may suspend, `.await` sequences two of them (bind),
//! and `?` inside an `async fn` adds a second effect, failure. A minimal
//! executor built from the standard library runs the futures and counts how
//! often it had to poll them.
//!
//! Run with: `cargo run --example ch20_async`

use std::future::{self, Future};
use std::pin::{Pin, pin};
use std::task::{Context, Poll, Waker};

// ANCHOR: block_on
/// A minimal executor: poll the future until it is ready, and report how many
/// polls it took. A real executor sleeps until a waker fires; ours retries at
/// once, which is enough for futures that never wait for the outside world.
fn block_on<F: Future>(fut: F) -> (F::Output, u32) {
    let mut fut = pin!(fut);
    let mut cx = Context::from_waker(Waker::noop());
    let mut polls = 0;
    loop {
        polls += 1;
        if let Poll::Ready(value) = fut.as_mut().poll(&mut cx) {
            return (value, polls);
        }
    }
}
// ANCHOR_END: block_on

// ANCHOR: network_delay
/// A future that is not ready the first time it is polled, standing in for a
/// network round trip.
struct NetworkDelay {
    waited: bool,
}

impl Future for NetworkDelay {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.waited {
            Poll::Ready(())
        } else {
            self.waited = true;
            cx.waker().wake_by_ref(); // "poll me again"
            Poll::Pending
        }
    }
}

fn network_delay() -> NetworkDelay {
    NetworkDelay { waited: false }
}
// ANCHOR_END: network_delay

// ANCHOR: quote
#[derive(Debug, PartialEq)]
enum ShopError {
    UnknownItem(String),
}

/// Ask the (simulated) price service for the unit price of an item.
async fn fetch_price(item: &str) -> Result<u32, ShopError> {
    network_delay().await;
    match item {
        "bolts" => Ok(25),
        "nuts" => Ok(10),
        _ => Err(ShopError::UnknownItem(item.to_string())),
    }
}

/// Two effects in one function: `.await` may suspend, `?` may fail. Each is a
/// bind, and the compiler supports both.
async fn quote(lines: &[(&str, u32)]) -> Result<u32, ShopError> {
    let mut total = 0;
    for &(item, qty) in lines {
        let price = fetch_price(item).await?;
        total += price * qty;
    }
    Ok(total)
}
// ANCHOR_END: quote

// ANCHOR: and_then
/// `bind` for futures, written with `async` itself: run `first`, feed its
/// output to `f`, run the future that `f` returns.
fn and_then<A, B, Fut1, Fut2>(
    first: Fut1,
    f: impl FnOnce(A) -> Fut2,
) -> impl Future<Output = B>
where
    Fut1: Future<Output = A>,
    Fut2: Future<Output = B>,
{
    async move {
        let a = first.await;
        f(a).await
    }
}
// ANCHOR_END: and_then

fn main() {
    let order = [("bolts", 2), ("nuts", 3)];
    let (total, polls) = block_on(quote(&order));
    println!("quote({order:?}) = {total:?} after {polls} polls");

    let order = [("bolts", 2), ("screws", 1), ("nuts", 3)];
    let (total, polls) = block_on(quote(&order));
    println!("quote({order:?}) = {total:?} after {polls} polls");
    if let Err(ShopError::UnknownItem(item)) = total {
        println!("  (stopped at {item:?}: the line after it was never priced)");
    }

    // `future::ready` is `pure` for futures: ready at the first poll.
    let (n, polls) = block_on(and_then(future::ready(20), |n| future::ready(n + 1)));
    println!("and_then(ready(20), |n| ready(n + 1)) = {n} after {polls} poll");

    // Left identity, checked on a sample: and_then(ready(a), f) behaves like f(a).
    let price = |item: &'static str| fetch_price(item);
    let (lhs, _) = block_on(and_then(future::ready("nuts"), price));
    let (rhs, _) = block_on(price("nuts"));
    assert_eq!(lhs, rhs);
}
