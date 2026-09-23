// itoa 1.0.18 formatting of integer extremes (an earlier itoa failure was
// `ireduce i16 -> i8` in itoa's digit loop) and serde_json serialization of a
// struct with those fields. The Serialize impl is written by hand: serde_derive
// is metadata-only in the pack (-Zproc-macro-metadata-only), so a
// #[derive] in browser-compiled code cannot expand.
use serde::ser::{Serialize, SerializeStruct, Serializer};
use std::hint::black_box;

struct Extremes {
    small: u8,
    medium: u16,
    signed: i16,
    large: u64,
    wide: i128,
    label: &'static str,
    list: Vec<i16>,
}

impl Serialize for Extremes {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("Extremes", 7)?;
        state.serialize_field("small", &self.small)?;
        state.serialize_field("medium", &self.medium)?;
        state.serialize_field("signed", &self.signed)?;
        state.serialize_field("large", &self.large)?;
        state.serialize_field("wide", &self.wide)?;
        state.serialize_field("label", &self.label)?;
        state.serialize_field("list", &self.list)?;
        state.end()
    }
}

fn main() {
    let mut buffer = itoa::Buffer::new();
    for value in [0_u8, 1, 9, 10, 99, 100, u8::MAX] {
        print!("{} ", buffer.format(black_box(value)));
    }
    println!();
    for value in [0_u16, 999, 1000, 9999, 10000, u16::MAX] {
        print!("{} ", buffer.format(black_box(value)));
    }
    println!();
    for value in [i16::MIN, -1000, -1, 0, 1, 1000, i16::MAX] {
        print!("{} ", buffer.format(black_box(value)));
    }
    println!();
    for value in [0_u64, 1, 10_000_000_000, u64::from(u32::MAX) + 1, u64::MAX] {
        print!("{} ", buffer.format(black_box(value)));
    }
    println!();
    for value in [i128::MIN, -1, 0, i128::MAX] {
        print!("{} ", buffer.format(black_box(value)));
    }
    println!();
    print!("{} ", buffer.format(black_box(u128::MAX)));
    println!("{}", buffer.format(black_box(i64::MIN)));
    let values = [
        Extremes { small: u8::MAX, medium: u16::MAX, signed: i16::MIN, large: u64::MAX, wide: i128::MIN, label: "max \"quoted\" \u{e9}\n", list: vec![i16::MIN, -1, 0, i16::MAX] },
        Extremes { small: 0, medium: 0, signed: -1, large: 0, wide: i128::MAX, label: "", list: Vec::new() },
    ];
    println!("{}", serde_json::to_string(black_box(&values)).expect("serialize"));
    println!("{}", serde_json::to_string_pretty(&values[1]).expect("serialize pretty"));
    let parsed: serde_json::Value = serde_json::from_str("{\"a\":[1,-2,3.5,\"x\"],\"b\":{\"c\":null,\"d\":true},\"e\":18446744073709551615}").expect("parse");
    println!("{parsed}");
}
