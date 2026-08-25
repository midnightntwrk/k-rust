use krs_macros::claim;

#[claim(all_paths, label = "contains:colon")]
fn invalid() {}

fn main() {}
