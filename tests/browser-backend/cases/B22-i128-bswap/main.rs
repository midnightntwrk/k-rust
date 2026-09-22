// Known gap: u128::swap_bytes (bswap.i128).
use std::hint::black_box;

#[inline(never)]
fn swap(a: u128) -> u128 {
    a.swap_bytes()
}

fn main() {
    println!("{:#x}", swap(black_box(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210)));
}
