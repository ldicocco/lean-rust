// harness: compile-fail E0283
//! `collect` can build many different collections; nothing says which one.

// ANCHOR: ports
fn parse_ports(text: &str) {
    let ports = text
        .split(',')
        .map(|p| p.trim().parse::<u16>().unwrap())
        .collect();
    println!("{ports:?}");
}
// ANCHOR_END: ports
