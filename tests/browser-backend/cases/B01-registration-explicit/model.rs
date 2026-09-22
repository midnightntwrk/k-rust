// Ported from spikes/BL-003/crates/collector-model: the same Registration
// record, without the `inventory::collect!` collection (IR-07 explicit registration).
use std::any::{Any, TypeId};

pub struct Registration {
    pub name: &'static str,
    pub ordinal: u32,
    pub factory: fn() -> Box<dyn Any>,
    pub expected_type_id: fn() -> TypeId,
    pub render: fn(&dyn Any) -> Result<String, &'static str>,
}
