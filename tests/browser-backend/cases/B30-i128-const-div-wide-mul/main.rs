// i128/u128 division and remainder by constants, and 128-bit multiplies whose high
// half matters. cg_clif lowers these to __divti3 & co. and __rust_{u,i}128_mulo, so
// clif2wasm's unimplemented i128 division immediates and i128 smulhi/umulhi are not
// reached (IR-22); this case keeps that observation checked.
use std::hint::black_box;

fn main() {
    let xs: [i128; 6] = [0, 1, -1, i128::MAX, i128::MIN, -123_456_789_012_345_678_901_234_567_890];
    for &x in &xs {
        let x = black_box(x);
        println!("{} {} {} {} {:?} {} {}", x / 7, x % 7, x / -10, x.div_euclid(1_000_000_007), x.checked_div(3), x.rem_euclid(97), x >> 5);
    }
    let us: [u128; 4] = [0, 1, u128::MAX, 340_282_366_920_938_463_463_374_607_431_768_211];
    for &u in &us {
        let u = black_box(u);
        println!("{} {} {} {}", u / 10, u % 10, u / (1 << 64), u / 1_000_000_000_000_000_000);
    }
    println!("{}", black_box(12_345_678_901_234_567_890_123_456_789_i128) / 1000);
    let a = black_box(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210_i128);
    let b = black_box(-0x7fff_ffff_0000_0001_i128);
    println!("{:?} {:?} {} {}", a.checked_mul(b), a.overflowing_mul(b), a.saturating_mul(b), a.wrapping_mul(b));
    let ua = a as u128;
    let ub = black_box(0xffff_ffff_0000_0001_u128);
    println!("{:?} {:?} {}", ua.checked_mul(ub), ua.overflowing_mul(ub), ua.saturating_mul(ub));
    let x = black_box(0x9e37_79b9_7f4a_7c15_u64);
    let y = black_box(u64::MAX - 3);
    println!("{:#x} {:?}", ((x as u128) * (y as u128)) >> 64, a.checked_pow(black_box(3)));
}
