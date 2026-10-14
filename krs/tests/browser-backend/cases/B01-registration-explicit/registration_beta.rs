// Ported from the collector control's beta registration: the factory,
// TypeId, and render function pointers are unchanged; the registration is a
// plain static that the collector names in an explicit table (no .init_array).
use b01_model::Registration;
use std::any::{Any, TypeId};

fn factory() -> Box<dyn Any> {
    Box::new(String::from("ready"))
}

fn expected_type_id() -> TypeId {
    TypeId::of::<String>()
}

fn render(value: &dyn Any) -> Result<String, &'static str> {
    value
        .downcast_ref::<String>()
        .map(|value| format!("beta:{value}"))
        .ok_or("beta factory returned the wrong type")
}

pub static REGISTRATION: Registration = Registration {
    name: "beta",
    ordinal: 10,
    factory,
    expected_type_id,
    render,
};
