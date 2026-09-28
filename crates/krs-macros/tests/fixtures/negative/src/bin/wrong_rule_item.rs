use krs_macros::rule;

#[rule]
trait NotAFunction {} //~ ERROR expected `fn`

fn main() {}
