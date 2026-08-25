//! Rename-safe Rust facade and host-only registry for builtin operations.

use std::any::TypeId;
use std::sync::atomic::{AtomicUsize, Ordering};

pub use m3_builtin_macros::builtin_application;
pub use m3_builtin_model::{BuiltinOp, BuiltinSignature, BuiltinSort};

static MARKER_DROPS: AtomicUsize = AtomicUsize::new(0);

/// Ordinary Rust marker types for the integer builtin family.
pub mod int {
    use super::{MARKER_DROPS, Ordering};

    /// Host marker for the K `Int` sort.
    #[derive(Clone, Copy, Debug)]
    pub struct Int;

    /// Tuple marker carrying the ordinary Rust signature of integer addition.
    #[derive(Debug)]
    pub struct Add(pub Int, pub Int);

    /// Tuple marker carrying the ordinary Rust signature of integer subtraction.
    #[derive(Debug)]
    pub struct Sub(pub Int, pub Int);

    impl Drop for Add {
        fn drop(&mut self) {
            MARKER_DROPS.fetch_add(1, Ordering::Relaxed);
        }
    }

    impl Drop for Sub {
        fn drop(&mut self) {
            MARKER_DROPS.fetch_add(1, Ordering::Relaxed);
        }
    }

    // A `use` alias preserves both namespaces: these names are tuple
    // constructors in value position and types in `TypeId::of::<...>()`.
    pub use Add as add;
    pub use Sub as sub;
}

/// One closed builtin catalog entry. `TypeId` is only a process-local join key.
#[derive(Clone, Copy)]
pub struct HostBuiltinRegistration {
    /// Function returning the marker type key.
    pub type_key: fn() -> TypeId,
    /// Target-neutral operation identity.
    pub operation: BuiltinOp,
    /// Target-neutral operation signature.
    pub signature: BuiltinSignature,
}

/// One parsed application registered by an author crate.
#[derive(Clone, Copy)]
pub struct HostBuiltinApplication {
    /// Stable Cargo/module/function identity.
    pub identity: &'static str,
    /// Authored, alias-preserving Rust path spelling.
    pub authored_path: &'static str,
    /// Parsed operand count.
    pub arity: usize,
    /// Function returning the resolved marker type key.
    pub type_key: fn() -> TypeId,
}

/// Linker entry around an application factory.
pub struct ApplicationRegistration {
    factory: fn() -> HostBuiltinApplication,
}

impl ApplicationRegistration {
    /// Creates a linker entry.
    #[must_use]
    pub const fn new(factory: fn() -> HostBuiltinApplication) -> Self {
        Self { factory }
    }

    fn make(&self) -> HostBuiltinApplication {
        (self.factory)()
    }
}

inventory::collect!(HostBuiltinRegistration);
inventory::collect!(ApplicationRegistration);

const INT_BINARY: BuiltinSignature = BuiltinSignature {
    operands: &[BuiltinSort::Int, BuiltinSort::Int],
    result: BuiltinSort::Int,
};

fn add_key() -> TypeId {
    TypeId::of::<int::add>()
}

fn sub_key() -> TypeId {
    TypeId::of::<int::sub>()
}

inventory::submit! {
    HostBuiltinRegistration {
        type_key: add_key,
        operation: BuiltinOp::IntAdd,
        signature: INT_BINARY,
    }
}

inventory::submit! {
    HostBuiltinRegistration {
        type_key: sub_key,
        operation: BuiltinOp::IntSub,
        signature: INT_BINARY,
    }
}

/// Enumerates builtin catalog entries in unspecified linker order.
pub fn builtin_registrations() -> impl Iterator<Item = &'static HostBuiltinRegistration> {
    inventory::iter::<HostBuiltinRegistration>.into_iter()
}

/// Enumerates parsed authored applications in unspecified linker order.
pub fn builtin_applications() -> impl Iterator<Item = HostBuiltinApplication> {
    inventory::iter::<ApplicationRegistration>
        .into_iter()
        .map(ApplicationRegistration::make)
}

/// Number of tuple markers actually constructed and dropped in this process.
#[must_use]
pub fn marker_drops() -> usize {
    MARKER_DROPS.load(Ordering::Relaxed)
}

/// Hidden rename-safe linker boundary used by the procedural macro.
#[doc(hidden)]
#[macro_export]
macro_rules! __submit_builtin_application {
    ($factory:path $(,)?) => {
        $crate::__private::inventory::submit! {
            $crate::ApplicationRegistration::new($factory)
        }
    };
}

/// Expansion-only dependencies.
#[doc(hidden)]
pub mod __private {
    pub use inventory;
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    #[test]
    fn aliases_share_identity_but_operations_do_not() {
        use crate::int as integer;
        use integer::add as plus;

        assert_eq!(TypeId::of::<crate::int::add>(), TypeId::of::<plus>());
        assert_ne!(TypeId::of::<integer::add>(), TypeId::of::<integer::sub>());
    }
}

