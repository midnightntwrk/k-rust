// Ported from spikes/BL-003/browser-control/registration-alpha.rs: the factory,
// TypeId, and render function pointers are unchanged; the registration is a
// plain static that the collector names in an explicit table (no .init_array).
use b01_model::Registration;
use std::any::{Any, TypeId};

fn factory() -> Box<dyn Any> {
    Box::new(17_u32)
}

fn expected_type_id() -> TypeId {
    TypeId::of::<u32>()
}

fn render(value: &dyn Any) -> Result<String, &'static str> {
    value
        .downcast_ref::<u32>()
        .map(|value| format!("alpha:{value}"))
        .ok_or("alpha factory returned the wrong type")
}

pub static REGISTRATION: Registration = Registration {
    name: "alpha",
    ordinal: 20,
    factory,
    expected_type_id,
    render,
};
