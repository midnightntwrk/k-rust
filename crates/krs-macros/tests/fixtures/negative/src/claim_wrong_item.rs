use krs_macros::claim;

#[claim(all_paths, label = "wrong-item")]
trait Invalid {}

fn main() {}
