// TypeId equality and inequality within one instance, across crates, and
// through stored `fn() -> TypeId` pointers (collector-runner type_id_equal /
// type_id_unequal; krs-ir HostTypeKey).
use b03_types::{circle_key, generic_key, square_key, Circle, Generic, Shape, Square, KEYS};
use std::any::{Any, TypeId};
use std::hint::black_box;

struct Local;

fn check(label: &str, value: bool) {
    println!("{label}={value}");
}

fn main() {
    let stored: fn() -> TypeId = black_box(square_key);
    check("local_equal", TypeId::of::<Local>() == TypeId::of::<Local>());
    check("local_vs_square", TypeId::of::<Local>() != TypeId::of::<Square>());
    check("cross_crate_equal", TypeId::of::<Square>() == square_key());
    check("cross_crate_unequal", TypeId::of::<Square>() != circle_key());
    check("stored_fn_equal", stored() == TypeId::of::<Square>());
    check("stored_fn_unequal", stored() != TypeId::of::<Circle>());
    check("generic_equal", generic_key::<u8>() == TypeId::of::<Generic<u8>>());
    check("generic_unequal", generic_key::<u8>() != generic_key::<i8>());
    check("reference_unequal", TypeId::of::<&'static str>() != TypeId::of::<String>());
    let boxed: Box<dyn Any> = Box::new(Square);
    check("dyn_any_type_id", (*boxed).type_id() == square_key());
    check("downcast", boxed.downcast_ref::<Square>().map(Shape::name) == Some("square"));
    for key in &KEYS {
        let id = black_box(key.type_id)();
        let matches: Vec<&str> = KEYS.iter().filter(|other| (other.type_id)() == id).map(|other| other.name).collect();
        println!("key {} matches {:?}", key.name, matches);
    }
    let mut sorted: Vec<(TypeId, &str)> = KEYS.iter().map(|key| ((key.type_id)(), key.name)).collect();
    sorted.sort();
    sorted.dedup_by_key(|entry| entry.0);
    println!("distinct_keys={}", sorted.len());
    // The TypeId values themselves (identical for the twin and rustc.wasm of one fork commit).
    println!("type_id square={:?}", TypeId::of::<Square>());
    println!("type_id generic_u8={:?}", TypeId::of::<Generic<u8>>());
    println!("type_id local={:?}", TypeId::of::<Local>());
}
