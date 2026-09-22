// Known gap: sign or zero extension from i8 to i16 (`x as i16` for an i8,
// `x as u16` for a u8, i8 multiply overflow checks, i16::signum) is not lowered.
use std::hint::black_box;

#[inline(never)]
fn widen(a: i8, b: u8) -> (i16, u16) {
    (a as i16, b as u16)
}

fn main() {
    println!("{:?}", widen(black_box(-3), black_box(250)));
}
