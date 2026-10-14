//! Fixed configuration-cell wrappers used by explicit fixed-state definitions.

use std::marker::PhantomData;

use crate::builtin::KSequence;

/// Type-level spelling of one fixed leaf cell containing a term of `T`.
///
/// This is an authoring marker, not a host container. Its constructor keeps
/// declarative configuration initializers ordinary rustc-valid Rust while
/// KRS records the structured initializer instead of executing it.
///
/// ```
/// use krs as language;
/// use language::{Term, builtin::{Id, Map}, configuration::Cell};
///
/// trait Value {}
/// type Environment = Map<Id, Term<dyn Value>>;
/// let _: Cell<Environment> = Cell::new(Environment::__new());
/// ```
///
/// The content type remains checked by rustc:
///
/// ```compile_fail
/// use krs::{Term, builtin::{Id, Map}, configuration::Cell};
///
/// trait Value {}
/// let _: Cell<Map<Id, Term<dyn Value>>> = Cell::new(Map::<Id, ()>::__new());
/// ```
pub struct Cell<T> {
    marker: PhantomData<fn() -> T>,
}

impl<T> Cell<T> {
    /// Wraps one checked fixed-cell initializer value.
    #[must_use]
    pub fn new(_contents: T) -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

/// Type-level spelling of the standard computation cell.
///
/// Like [`KSequence`], this is a zero-sized authoring value. Constructing
/// it lets the associated initializer remain ordinary rustc-valid Rust;
/// collection never executes that initializer.
///
/// ```
/// use krs as language;
/// use language::{builtin::KSequence, configuration::KCell};
///
/// let _: KCell<KSequence> = KCell::new(KSequence::__new());
/// ```
pub struct KCell<T> {
    marker: PhantomData<fn() -> T>,
}

impl KCell<KSequence> {
    /// Wraps one checked computation-sequence authoring expression.
    #[must_use]
    pub const fn new(_contents: KSequence) -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

/// Stands in for a ground initializer term such as `1` or `list::empty()`.
///
/// KRS checks the term itself, and the paths it names reach rustc through the
/// collected descriptor; the generated initializer body passes this
/// placeholder to [`Cell::new`] so the term need not be a Rust value of the
/// cell's marker type. Collection never executes that initializer.
#[doc(hidden)]
#[must_use]
pub fn __term<T>() -> T {
    unreachable!("KRS never executes a configuration initializer")
}

/// Opaque authoring type for a compiler-owned nested-cell term.
///
/// Values are created only by [`crate::fragment!`]. The host type carries
/// the nominal parent for rustc while KRS validates the actual child set
/// against the collected fixed-configuration declaration.
pub struct CellFragment<Parent> {
    marker: PhantomData<fn() -> Parent>,
}

impl<Parent> CellFragment<Parent> {
    /// Constructs the zero-sized result of a checked macro expansion.
    #[doc(hidden)]
    #[must_use]
    pub const fn __new() -> Self {
        Self {
            marker: PhantomData,
        }
    }
}
