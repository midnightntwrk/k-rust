// std::simd mul_add (simd_fma): each lane is a fused multiply-add. On wasm32 cg_clif
// calls fma/fmaf per lane (IR-22); before, clif2wasm failed on the fma instruction.
#![feature(portable_simd)]
use std::hint::black_box;
use std::simd::{f32x4, f64x2, StdFloat};

fn main() {
    let a = black_box(f32x4::from_array([1.5, -2.0, 0.1, 3.0]));
    let b = black_box(f32x4::from_array([2.0, 0.5, 0.1, -1.0]));
    let c = black_box(f32x4::splat(0.25));
    println!("f32x4 {:?}", a.mul_add(b, c).to_array());
    // 0.1 * 10 - 1 is 5.551115123125783e-17 fused and 0 unfused; 1e308 * 10 - 1e308 overflows.
    let d = black_box(f64x2::from_array([0.1, 1e308]));
    let e = black_box(f64x2::from_array([10.0, 10.0]));
    let f = black_box(f64x2::from_array([-1.0, -1e308]));
    println!("f64x2 {:?}", d.mul_add(e, f).to_array());
}
