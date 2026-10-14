use krs_macros::claim;

#[claim(all_paths, label = "contains:colon")] //~ ERROR invalid portable K claim label
fn invalid() {}

fn main() {}
