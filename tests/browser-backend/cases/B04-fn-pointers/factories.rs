// Static tables of function pointers in a library crate (the BL-003 factory
// and render pointers; krs HostRegistration::new).
use std::fmt::Debug;

pub trait Render: Debug {
    fn render(&self) -> String;
    fn weight(&self) -> u64 {
        1
    }
}

#[derive(Debug)]
pub struct Constant(pub i64);

#[derive(Debug)]
pub struct Pair(pub &'static str, pub u16);

impl Render for Constant {
    fn render(&self) -> String {
        format!("constant:{}", self.0)
    }
}

impl Render for Pair {
    fn render(&self) -> String {
        format!("pair:{}:{}", self.0, self.1)
    }
    fn weight(&self) -> u64 {
        // A checked u64 multiply at opt-level 0 (umulhi.i64; B18, fixed in eb8eda040).
        u64::from(self.1) * 3
    }
}

pub type Factory = fn() -> Box<dyn Render>;

fn make_constant() -> Box<dyn Render> {
    Box::new(Constant(-42))
}

fn make_pair() -> Box<dyn Render> {
    Box::new(Pair("left", 7))
}

pub struct Registration {
    pub name: &'static str,
    pub factory: Factory,
    pub transform: fn(i64) -> i64,
}

fn double(value: i64) -> i64 {
    // A checked i64 multiply at opt-level 0 (smulhi.i64; B17, fixed in eb8eda040).
    value * 2
}

fn negate(value: i64) -> i64 {
    -value
}

pub static TABLE: [Registration; 2] = [
    Registration { name: "constant", factory: make_constant, transform: double },
    Registration { name: "pair", factory: make_pair, transform: negate },
];

pub struct HostRegistration {
    pub name: &'static str,
    factory: Factory,
}

impl HostRegistration {
    pub const fn new(name: &'static str, factory: Factory) -> Self {
        Self { name, factory }
    }
    pub fn build(&self) -> Box<dyn Render> {
        (self.factory)()
    }
}
