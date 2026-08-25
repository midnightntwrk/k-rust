use krs_macros::constructor;

#[constructor(syntax = "missing sort")]
struct Broken;

fn main() {}
