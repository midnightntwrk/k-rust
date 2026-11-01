use krs_macros::claim;

#[claim(all_paths, label = "assumed", trusted, trusted)] //~ ERROR duplicate argument `trusted`
fn invalid() {}

fn main() {}
