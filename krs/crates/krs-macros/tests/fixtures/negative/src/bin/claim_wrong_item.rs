use krs_macros::claim;

#[claim(all_paths, label = "wrong-item")]
trait Invalid {} //~ ERROR expected `fn`

fn main() {}
