use krs_macros::sort;

#[sort]
struct NotATrait; //~ ERROR expected `trait`

fn main() {}
