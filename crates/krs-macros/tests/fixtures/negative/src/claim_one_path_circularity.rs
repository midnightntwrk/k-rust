use krs_macros::claim;

#[claim(one_path, label = "incompatible", circularity)]
fn invalid() {}

fn main() {}
