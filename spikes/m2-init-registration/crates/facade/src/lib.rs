//! Host-only registration surface for the M2 associated-initializer spike.

use std::any::TypeId;

pub use m2_init_macros::{configuration, init};

/// Parsed initializer data made available without executing the initializer.
#[derive(Clone, Copy, Debug)]
pub struct InitPayload {
    /// Authored method name.
    pub method: &'static str,
}

/// One process-local configuration/initializer registration.
#[derive(Clone, Copy)]
pub struct Descriptor {
    /// Stable host lookup spelling assembled from real Cargo/module/item data.
    pub identity: &'static str,
    /// Build-local type join key. It is deliberately never printed or serialized.
    pub type_key: fn() -> TypeId,
    /// Rust's diagnostic type spelling, used only as empirical evidence.
    pub type_name: fn() -> &'static str,
    /// Declarative initializer payload factory.
    pub payload: fn() -> InitPayload,
}

/// One linker registration entry.
pub struct Registration {
    factory: fn() -> Descriptor,
}

impl Registration {
    /// Creates a registration around a descriptor factory.
    #[must_use]
    pub const fn new(factory: fn() -> Descriptor) -> Self {
        Self { factory }
    }

    fn make(&self) -> Descriptor {
        (self.factory)()
    }
}

inventory::collect!(Registration);

/// Enumerates freshly constructed descriptors in unspecified linker order.
pub fn descriptors() -> impl Iterator<Item = Descriptor> {
    inventory::iter::<Registration>.into_iter().map(Registration::make)
}

/// Hidden rename-safe inventory boundary used by the procedural macros.
#[doc(hidden)]
#[macro_export]
macro_rules! __submit {
    ($factory:path $(,)?) => {
        $crate::__private::inventory::submit! {
            $crate::Registration::new($factory)
        }
    };
}

/// Expansion-only dependencies.
#[doc(hidden)]
pub mod __private {
    pub use inventory;
}

