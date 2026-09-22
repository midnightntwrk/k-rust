// Known gap: u64 checked_mul / overflowing_mul / saturating_mul lower to
// umulhi.i64 at every opt level, which clif2wasm does not implement.
use std::hint::black_box;

#[inline(never)]
fn checked(a: u64, b: u64) -> Option<u64> {
    a.checked_mul(b)
}

fn main() {
    println!("{:?} {:?}", checked(black_box(3), black_box(4)), checked(black_box(u64::MAX), black_box(2)));
}
