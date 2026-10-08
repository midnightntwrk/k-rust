use krs_macros::claim;

#[claim(all_paths, label = "assumed", trusted, trusted)] //~ ERROR duplicate trusted modifier
fn invalid() {}

fn main() {}
