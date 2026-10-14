// Types and TypeId keys defined in a library crate (HostTypeKey shape: a
// stored `fn() -> TypeId` compared inside one instance).
use std::any::TypeId;

pub struct Square;
pub struct Circle;
pub struct Generic<T>(pub T);

pub trait Shape {
    fn name(&self) -> &'static str;
}

impl Shape for Square {
    fn name(&self) -> &'static str {
        "square"
    }
}

pub fn square_key() -> TypeId {
    TypeId::of::<Square>()
}

pub fn circle_key() -> TypeId {
    TypeId::of::<Circle>()
}

pub fn generic_key<T: 'static>() -> TypeId {
    TypeId::of::<Generic<T>>()
}

pub struct HostTypeKey {
    pub name: &'static str,
    pub type_id: fn() -> TypeId,
}

pub static KEYS: [HostTypeKey; 3] = [
    HostTypeKey { name: "square", type_id: square_key },
    HostTypeKey { name: "circle", type_id: circle_key },
    HostTypeKey { name: "generic_u8", type_id: generic_key::<u8> },
];
