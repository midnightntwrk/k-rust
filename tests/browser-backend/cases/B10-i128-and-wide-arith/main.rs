// u128/i128 multiply, divide, remainder, shifts, and u64 overflow checks
// (StableHasher's u64 wrapping multiply; i128 lowering in clif2wasm).
// Since eb8eda040 also: checked/overflowing/saturating u64 multiply (B18),
// checked i128 ops and signum (B21), u128 swap_bytes/reverse_bits (B22),
// mul_add (B23), and float -> 128-bit conversions (B24).
use std::hint::black_box;

fn main() {
    let a = black_box(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210_u128);
    let b = black_box(0xffff_ffff_0000_0001_u128);
    println!("u128 mul {:#x} div {:#x} rem {:#x}", a.wrapping_mul(b), a / b, a % b);
    println!("u128 shl {:#x} shr {:#x} rotl {:#x}", a << black_box(67), a >> black_box(65), a.rotate_left(black_box(13)));
    println!("u128 lz {} tz {} ones {}", a.leading_zeros(), b.trailing_zeros(), a.count_ones());
    let c = black_box(-170_141_183_460_469_231_731_687_303_715_884_105_727_i128);
    let d = black_box(-7_i128);
    println!("i128 div {} rem {} mul {} shr {}", c / d, c % d, c.wrapping_mul(d), c >> black_box(100));
    println!("i128 abs_diff {} pow {} wrapping_neg {}", c.abs_diff(d), black_box(3_i128).pow(80), c.wrapping_neg());
    let x = black_box(0x9e37_79b9_7f4a_7c15_u64);
    let mut state = black_box(0_u64);
    for byte in b"stable hasher input" {
        state = (state.rotate_left(5) ^ u64::from(*byte)).wrapping_mul(x);
    }
    println!("u64 hasher state {state:#018x}");
    println!(
        "u64 checked_add {:?} {:?} overflowing_add {:?} wrapping_mul {} widening {:#x}",
        x.checked_add(black_box(1)),
        u64::MAX.checked_add(black_box(1)),
        x.overflowing_add(black_box(u64::MAX)),
        x.wrapping_mul(black_box(0x1_0000_0001)),
        u128::from(x) * u128::from(black_box(u64::MAX))
    );
    println!("u64 div {} rem {} i64 div {} rem {}", x / black_box(12345), x % black_box(12345), black_box(i64::MIN) / black_box(7), black_box(i64::MIN) % black_box(7));
    println!("i128 -> float {} {} {}", black_box(u128::MAX) as f64, black_box(i128::MIN) as f64, black_box(-12345678901234567890123_i128) as f32);
    println!("u128 parse {:?} fmt {}", "340282366920938463463374607431768211455".parse::<u128>(), black_box(u128::MAX) / 3);
    println!(
        "u64 checked_mul {:?} {:?} overflowing_mul {:?} saturating_mul {} i64 checked_mul {:?}",
        x.checked_mul(black_box(3)),
        x.checked_mul(black_box(u64::MAX)),
        x.overflowing_mul(black_box(0x1_0000_0001)),
        x.saturating_mul(black_box(1 << 20)),
        black_box(i64::MIN / 3).checked_mul(black_box(-3))
    );
    println!(
        "i128 checked {:?} {:?} {:?} signum {} {} {} u128 checked {:?} {:?}",
        c.checked_add(black_box(-2)),
        c.checked_mul(d),
        d.checked_pow(black_box(40)),
        c.signum(),
        black_box(0_i128).signum(),
        d.wrapping_neg().signum(),
        a.checked_mul(b),
        a.checked_sub(black_box(u128::MAX))
    );
    println!("u128 swap_bytes {:#x} reverse_bits {:#x} i128 swap_bytes {}", a.swap_bytes(), b.reverse_bits(), c.swap_bytes());
    println!(
        "mul_add {} {} {}",
        black_box(0.1_f64).mul_add(black_box(10.0), black_box(-1.0)),
        black_box(2.5_f32).mul_add(black_box(-1.5), black_box(1.0)),
        black_box(1e308_f64).mul_add(black_box(10.0), black_box(-1e308))
    );
    println!(
        "float -> 128 {} {} {} {} {} {}",
        black_box(1.5e38_f64) as u128,
        black_box(-1.7e38_f64) as i128,
        black_box(1e40_f64) as u128,
        black_box(-1.0_f64) as u128,
        black_box(f64::NAN) as i128,
        black_box(3.4e38_f32) as u128
    );
}
