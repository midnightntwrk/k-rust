// Known gap (silent miscompile): a left shift on u8/u16 keeps the bits shifted
// out of the narrow type, so a following right shift or widening sees them.
use std::hint::black_box;

#[inline(never)]
fn shl_shr(a: u8, b: u16) -> (u8, u16, u32) {
    ((a << 4) >> 4, (b << 8) >> 8, u32::from(a.wrapping_shl(3)))
}

fn main() {
    println!("{:?}", shl_shr(black_box(0xab), black_box(0x1234)));
}
