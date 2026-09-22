// Indirect calls through cross-crate fn-pointer tables, dyn Trait dispatch,
// and non-capturing closures coerced to fn pointers.
use b04_factories::{HostRegistration, Pair, Render, TABLE};
use std::hint::black_box;

#[derive(Debug)]
struct Local(u8);

impl Render for Local {
    fn render(&self) -> String {
        format!("local:{}", self.0)
    }
    fn weight(&self) -> u64 {
        u64::from(self.0) + 100
    }
}

static LOCAL_TABLE: [HostRegistration; 3] = [
    HostRegistration::new("local", || Box::new(Local(9))),
    HostRegistration::new("pair", || Box::new(Pair("right", 11))),
    HostRegistration::new("constant", TABLE[0].factory),
];

fn apply(functions: &[fn(i64) -> i64], value: i64) -> Vec<i64> {
    functions.iter().map(|function| black_box(*function)(value)).collect()
}

fn main() {
    for registration in &TABLE {
        let value = (black_box(registration.factory))();
        println!(
            "{} -> {} weight={} debug={:?} transform(21)={}",
            registration.name,
            value.render(),
            value.weight(),
            value,
            (registration.transform)(21)
        );
    }
    let mut built: Vec<(String, u64)> = LOCAL_TABLE
        .iter()
        .map(|registration| {
            let value = black_box(registration).build();
            (format!("{}={}", registration.name, value.render()), value.weight())
        })
        .collect();
    built.sort();
    println!("{built:?}");
    let closures: [fn(i64) -> i64; 4] = [|x| x + 1, |x| x.wrapping_mul(x), |x| x.wrapping_neg(), TABLE[1].transform];
    println!("closures {:?}", apply(&closures, black_box(-5)));
    let objects: Vec<Box<dyn Render>> = vec![Box::new(Local(1)), (TABLE[1].factory)(), Box::new(Pair("mid", 2))];
    let total: u64 = objects.iter().map(|object| object.weight()).sum();
    println!("dyn total weight={total} renders={:?}", objects.iter().map(|object| object.render()).collect::<Vec<_>>());
    let reloaded: fn(i64) -> i64 = black_box(TABLE[1].transform);
    println!("fn_addr_eq table={} reloaded={}", std::ptr::fn_addr_eq(TABLE[1].transform, TABLE[1].transform), std::ptr::fn_addr_eq(reloaded, TABLE[1].transform));
}
