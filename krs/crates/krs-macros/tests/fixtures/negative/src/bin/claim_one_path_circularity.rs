use krs_macros::claim;

#[claim(one_path, label = "incompatible", circularity)] //~ ERROR circularity is valid only on an all-path claim
fn invalid() {}

fn main() {}
