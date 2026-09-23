// Known gap: rotate_left/rotate_right on u8 and u16.
use std::hint::black_box;

#[inline(never)]
fn rotate(a: u8, b: u16) -> (u8, u16) {
    (a.rotate_left(3), b.rotate_right(5))
}

fn main() {
    println!("{:?}", rotate(black_box(0x81), black_box(0x1234)));
}
