// Known gap: float -> 128-bit integer conversions (`f as i128`, `f as u128`)
// call __fixdfti / __fixunsdfti / __fixsfti / __fixunssfti with a multi-value
// i128 return, while compiler_builtins in the sysroot (LLVM) returns through a
// pointer; riwl rejects the signature mismatch at link time.
use std::hint::black_box;

#[inline(never)]
fn convert(a: f64) -> u128 {
    a as u128
}

fn main() {
    println!("{}", convert(black_box(1.0e30)));
}
