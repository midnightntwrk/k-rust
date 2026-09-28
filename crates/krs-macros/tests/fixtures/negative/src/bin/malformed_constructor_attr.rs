use krs_macros::constructor;

#[constructor(syntax = "missing sort")] //~ ERROR missing required argument `sort = ...`
struct Broken;

fn main() {}
