use krs_macros::claim;

#[claim(all_paths, label = "assumed", circularity, trusted)] //~ ERROR a trusted claim is assumed, not proved; circularity has no effect
fn invalid() {}

fn main() {}
