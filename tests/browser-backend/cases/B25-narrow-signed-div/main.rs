// Known gap (silent miscompile): signed division, remainder, and arithmetic
// shift right on i8 and i16 treat the operands as unsigned. Compiles and runs,
// with wrong values.
use std::hint::black_box;

#[inline(never)]
fn ops8(a: i8, b: i8) -> (i8, i8, i8, i8) {
    (a / b, a % b, a >> (b as u32 & 7), a / 3)
}

#[inline(never)]
fn ops16(a: i16, b: i16) -> (i16, i16, i16, i16) {
    (a / b, a % b, a >> (b as u32 & 15), a % 10)
}

fn main() {
    println!("i8 {:?}", ops8(black_box(-100), black_box(7)));
    println!("i16 {:?}", ops16(black_box(-1003), black_box(7)));
    println!("i16 div_euclid {} rem_euclid {}", black_box(-1000_i16).div_euclid(black_box(7)), black_box(-1000_i16).rem_euclid(black_box(7)));
}
