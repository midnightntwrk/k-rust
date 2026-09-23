#[rustfmt::skip::macros(vec)]
pub fn a() {}

#[rustfmt::other]
pub fn b() {}

#[clippy::skip]
pub fn c() {}

#[::rustfmt::skip]
pub fn d() {}

#[rustfmt::skip = "x"]
pub fn e() {}
