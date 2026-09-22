// Known gap: an i64 multiply with an overflow check (every `a * b` at
// opt-level 0, where lesson code is compiled) lowers to smulhi.i64, which
// clif2wasm does not implement. opt-level 2 has no overflow check and passes.
use std::hint::black_box;

#[inline(never)]
fn product(a: i64, b: i64) -> i64 {
    a * b
}

fn main() {
    println!("{}", product(black_box(3), black_box(-4)));
}
