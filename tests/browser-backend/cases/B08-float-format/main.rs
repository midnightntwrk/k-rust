// serde_json f64/f32 output (serde_json 1.0.151 formats floats through zmij).
use std::hint::black_box;

fn main() {
    let values: [f64; 12] = [0.1, 1.5, 1e300, -0.0, 0.0, 5e-324, 2.2250738585072014e-308, f64::MAX, f64::MIN_POSITIVE, -123456.789, 1e21, 1e-7];
    for value in values {
        let value = black_box(value);
        println!("{} {} {:?} {:e}", serde_json::to_string(&value).expect("f64"), value, value, value);
    }
    let singles: [f32; 5] = [0.1, 1.5, f32::MAX, 1e-45, -0.0];
    for value in singles {
        let value = black_box(value);
        println!("{} {} {:?}", serde_json::to_string(&value).expect("f32"), value, value);
    }
    for value in [f64::NAN, f64::INFINITY] {
        println!("non-finite {}", serde_json::to_string(&black_box(value)).expect("non-finite"));
    }
    let parsed: Vec<f64> = serde_json::from_str("[0.1, 1e300, -0.0, 5e-324, 1.7976931348623157e308, 3.141592653589793]").expect("parse");
    println!("{:?} {}", parsed, serde_json::to_string(&parsed).expect("round trip"));
    println!("{:.3} {:10.2e} {:+}", black_box(2.0_f64).sqrt(), black_box(12345.678_f64), black_box(1.0_f64) / 3.0);
}
