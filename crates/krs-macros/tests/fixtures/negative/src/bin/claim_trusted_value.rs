use krs_macros::claim;

#[claim(all_paths, label = "assumed", trusted = true)] //~ ERROR `trusted` is a bare flag; write `trusted` without a value
fn invalid() {}

fn main() {}
