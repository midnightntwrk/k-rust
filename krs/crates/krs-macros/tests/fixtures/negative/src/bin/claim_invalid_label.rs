use krs_macros::claim;

#[claim(all_paths, label = "contains:colon")] //~ ERROR must be a portable K claim label
fn invalid() {}

fn main() {}
