// harness: run
//! Region inference on `record_count` (compare with rustc's own region
//! values), and the loan of `readings` in `first_then_push` under the
//! non-lexical and the lexical rules.
//!
//! Run with: `cargo run -p mini-nll --example ch29_regions`

use mini_nll::borrowck::{Checker, check, collect_loans};
use mini_nll::mir::{Body, Ty};
use mini_nll::programs;
use mini_nll::regions::{RegionMode, infer};

/// Which local (or loan) a region belongs to, for the printout.
fn owner(body: &Body, r: usize) -> String {
    for (i, decl) in body.locals.iter().enumerate() {
        if let Ty::Ref(region, ..) = decl.ty {
            if region.0 == r {
                return format!("type of _{i}");
            }
        }
    }
    for (i, loan) in collect_loans(body, true).iter().enumerate() {
        if loan.region.0 == r {
            return format!("loan L{i} = {}", body.fmt_rvalue_of_loan(loan));
        }
    }
    String::from("-")
}

fn main() {
    let body = programs::record_count();
    let nll = infer(&body, RegionMode::Nll);
    println!("record_count: outlives constraints");
    for c in &nll.constraints {
        let (sup, sub) = (body.region_name(c.sup), body.region_name(c.sub));
        println!("  {sup}: {sub}  at {}", c.location);
    }
    println!("record_count: region values ({} passes)", nll.passes);
    for r in 0..body.regions.len() {
        let value = nll.values.describe(&body, mini_nll::mir::RegionVid(r));
        println!("  '?{r} = {value:<26} {}", owner(&body, r));
    }

    let body = programs::first_then_push();
    let loan = &collect_loans(&body, true)[0];
    println!(
        "first_then_push: loan L0 = {}",
        body.fmt_rvalue_of_loan(loan)
    );
    for (mode, name) in [(RegionMode::Nll, "NLL"), (RegionMode::Lexical, "lexical")] {
        let values = infer(&body, mode).values;
        println!(
            "  {name:<7} '?{} = {}",
            loan.region.0,
            values.describe(&body, loan.region)
        );
    }
    for d in check(&body, Checker::Lexical) {
        print!("{}", d.render(&body));
    }
}
