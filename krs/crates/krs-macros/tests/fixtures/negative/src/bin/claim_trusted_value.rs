use krs_macros::claim;

#[claim(all_paths, label = "assumed", trusted = true)] //~ ERROR `trusted` must be a bare flag, without a value
fn invalid() {}

fn main() {}
