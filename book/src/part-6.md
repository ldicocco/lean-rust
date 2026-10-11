Part VI is about the other half of Rust's discipline: references. Affinity alone
cannot explain borrowing (a shared reference can be copied freely), so we turn to
regions, permissions and subtyping. We build a small calculus with ownership,
lifetimes, shared and mutable borrows and reborrowing, check it in Rust and
formalize it in Lean, and then look at how the real compiler does it: not by
building derivations, but by dataflow analysis over a control-flow graph.
