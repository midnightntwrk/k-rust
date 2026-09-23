// Every ireduce pair and the inverse extensions (clif2wasm/src/ops.rs; the
// i16 -> i8 ireduce backend control). Values pass through black_box and
// non-inlined functions so that the narrowing is not constant-folded.
use std::hint::black_box;

macro_rules! narrow {
    ($name:ident, $from:ty => $to:ty) => {
        #[inline(never)]
        fn $name(value: $from) -> $to {
            value as $to
        }
    };
}

narrow!(i128_i64, i128 => i64);
narrow!(i128_i32, i128 => i32);
narrow!(i128_i16, i128 => i16);
narrow!(i128_i8, i128 => i8);
narrow!(u128_u64, u128 => u64);
narrow!(u128_u8, u128 => u8);
narrow!(i64_i32, i64 => i32);
narrow!(i64_i16, i64 => i16);
narrow!(i64_i8, i64 => i8);
narrow!(u64_u16, u64 => u16);
narrow!(i32_i16, i32 => i16);
narrow!(i32_i8, i32 => i8);
narrow!(u32_u8, u32 => u8);
narrow!(i16_i8, i16 => i8);
narrow!(u16_u8, u16 => u8);
narrow!(i16_u8, i16 => u8);
// Extensions (uextend / sextend), including i8 -> i16 and u8 -> u16 (B19, fixed in eb8eda040).
narrow!(i8_i16, i8 => i16);
narrow!(u8_u16, u8 => u16);
narrow!(i8_u16, i8 => u16);
narrow!(i8_i32, i8 => i32);
narrow!(i8_i64, i8 => i64);
narrow!(i8_i128, i8 => i128);
narrow!(u8_u64, u8 => u64);
narrow!(u8_u128, u8 => u128);
narrow!(i16_i32, i16 => i32);
narrow!(i16_i64, i16 => i64);
narrow!(i16_i128, i16 => i128);
narrow!(u16_u32, u16 => u32);
narrow!(i32_i64, i32 => i64);
narrow!(i32_i128, i32 => i128);
narrow!(u32_u128, u32 => u128);
narrow!(i64_i128, i64 => i128);
narrow!(u64_u128, u64 => u128);
narrow!(i8_u128, i8 => u128);

fn main() {
    let wide: [i128; 6] = [0, -1, 0x1234_5678_9abc_def0_0fed_cba9_8765_4321, i128::MIN, i128::MAX, -0x8081];
    for value in wide {
        let value = black_box(value);
        println!(
            "i128 {value}: i64={} i32={} i16={} i8={} u128->u64={} u128->u8={}",
            i128_i64(value),
            i128_i32(value),
            i128_i16(value),
            i128_i8(value),
            u128_u64(value as u128),
            u128_u8(value as u128)
        );
    }
    let values64: [i64; 6] = [0, -1, 0x1234_5678_9abc_def0, i64::MIN, i64::MAX, -129];
    for value in values64 {
        let value = black_box(value);
        println!("i64 {value}: i32={} i16={} i8={} u64->u16={}", i64_i32(value), i64_i16(value), i64_i8(value), u64_u16(value as u64));
    }
    let values32: [i32; 6] = [0, -1, 0x1234_5678, i32::MIN, i32::MAX, 0xff80];
    for value in values32 {
        let value = black_box(value);
        println!("i32 {value}: i16={} i8={} u32->u8={}", i32_i16(value), i32_i8(value), u32_u8(value as u32));
    }
    let values16: [i16; 7] = [0, -1, 0x1234, i16::MIN, i16::MAX, -128, 0xff];
    for value in values16 {
        let value = black_box(value);
        println!("i16 {value}: i8={} u16->u8={} i16->u8={}", i16_i8(value), u16_u8(value as u16), i16_u8(value));
    }
    for value in [0_i8, -1, i8::MIN, i8::MAX, 0x55] {
        let value = black_box(value);
        println!(
            "i8 {value}: i16={} i8->u16={} u8->u16={} i32={} i64={} i128={} u128={} u8->u64={} u8->u128={}",
            i8_i16(value),
            i8_u16(value),
            u8_u16(value as u8),
            i8_i32(value),
            i8_i64(value),
            i8_i128(value),
            i8_u128(value),
            u8_u64(value as u8),
            u8_u128(value as u8)
        );
    }
    for value in [0_i16, -1, i16::MIN, i16::MAX] {
        let value = black_box(value);
        println!("i16 ext {value}: i32={} i64={} i128={} u16->u32={}", i16_i32(value), i16_i64(value), i16_i128(value), u16_u32(value as u16));
    }
    for value in [0_i32, -1, i32::MIN, i32::MAX] {
        let value = black_box(value);
        println!("i32 ext {value}: i64={} i128={} u32->u128={}", i32_i64(value), i32_i128(value), u32_u128(value as u32));
    }
    for value in [0_i64, -1, i64::MIN, i64::MAX] {
        let value = black_box(value);
        println!("i64 ext {value}: i128={} u64->u128={}", i64_i128(value), u64_u128(value as u64));
    }
    // The ireduce control: narrow(0x1234) = 52, narrow(0xffff) = 255.
    println!("bl003 narrow(0x1234)={} narrow(0xffff)={}", u16_u8(black_box(0x1234)), u16_u8(black_box(0xffff)));
    // Wrapping arithmetic in narrow types (i8/i16 results of add, sub, mul, neg, unsigned shr).
    let a = black_box(100_i8);
    let b = black_box(-3_i16);
    println!(
        "narrow arithmetic: {} {} {} {} {} {}",
        a.wrapping_add(100),
        a.wrapping_mul(3),
        a.wrapping_sub(-100),
        b.wrapping_mul(20000),
        b.wrapping_neg(),
        (b as u16) >> 3
    );
    // Checked narrow arithmetic (overflow checks at opt-level 0; i8 multiply sign-extends to i16,
    // B19), narrow shl, signed div/rem/shr (B25, B26), and rotates (B20), all fixed in eb8eda040.
    let c = black_box(-100_i8);
    let d = black_box(7_i8);
    let e = black_box(0xab_u8);
    let f = black_box(-1234_i16);
    println!(
        "narrow checked: {} {} {:?} {:?} {:?} {:?}",
        c / d * 2 + 1,
        c % d - 3,
        c.checked_mul(d),
        d.checked_mul(black_box(18)),
        e.checked_add(black_box(0x60)),
        f.checked_mul(black_box(30))
    );
    println!(
        "narrow shifts: {} {} {} {} {} {} {} {}",
        (e << black_box(4)) >> 4,
        c >> black_box(7),
        f >> black_box(3),
        f / black_box(-7),
        f % black_box(100),
        e.rotate_left(black_box(3)),
        (f as u16).rotate_right(black_box(5)),
        c.rotate_left(black_box(9))
    );
}
