use krs_macros::configuration;

#[configuration(root = "machine")]
enum Machine {} //~ ERROR expected `struct`

fn main() {}
