// Known gap: f32/f64 mul_add (fma).
use std::hint::black_box;

#[inline(never)]
fn fused(a: f64, b: f64, c: f64) -> f64 {
    a.mul_add(b, c)
}

fn main() {
    println!("{}", fused(black_box(2.5), black_box(-1.5), black_box(1.0)));
}
