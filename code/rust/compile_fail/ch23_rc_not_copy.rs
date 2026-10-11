// harness: compile-fail E0382
//! `Rc<T>` is not `Copy`: a copy of the pointer must be counted, so it has to
//! be made explicitly, with `Rc::clone`.

use std::rc::Rc;

// ANCHOR: share
fn share(cfg: Rc<String>) -> (Rc<String>, Rc<String>) {
    (cfg, cfg)
}
// ANCHOR_END: share
