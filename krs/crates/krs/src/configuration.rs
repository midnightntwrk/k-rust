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

/// Implemented by no type: a configuration reaches the bound below only when
/// it has no inherent `#[k::init]` initializer, and rustc then reports this
/// trait's message at the configuration's name.
///
/// An initializer is required: it gives each cell its initial content, which
/// a cell's sort does not determine (no cell has a default value).
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "[krs::expand::missing-initializer] configuration `{Self}` has no `#[k::init]` initializer",
    label = "`{Self}` has no initializer",
    note = "an initializer gives each cell its initial value: `impl {Self} {{ #[k::init] pub fn init() -> Self {{ Self {{ .. }} }} }}`"
)]
pub trait __KrsInitializer {}

/// The initializer payload a configuration's descriptor factory reads when its
/// configuration has no inherent `#[k::init]`.
///
/// An inherent associated function is found before a trait's, so a
/// configuration with an initializer calls the payload `#[k::init]` emits and
/// never this one; one without an initializer resolves to this method, whose
/// unsatisfiable bound reports [`__KrsInitializer`]'s message.
///
/// A payload hands the initializer's wire and slot table to `configuration`,
/// which the factory passes to decode them inside the payload's body, and
/// returns what it returns with the initializer's provenance: a slot that
/// names a declaration through the lexical witness is a value computed in
/// that body, so the table cannot outlive it.
#[doc(hidden)]
pub trait __KrsInitializerFallback {
    /// Never callable: no type implements [`__KrsInitializer`].
    ///
    /// # Errors
    ///
    /// Never returns.
    fn __krs_initializer_payload<R>(
        configuration: impl FnOnce(&'static str, crate::__KrsSlots<'_>) -> R,
    ) -> Result<(R, crate::HostProvenance), crate::HostProvenanceError>
    where
        Self: __KrsInitializer;
}

impl<T: ?Sized> __KrsInitializerFallback for T {
    fn __krs_initializer_payload<R>(
        _configuration: impl FnOnce(&'static str, crate::__KrsSlots<'_>) -> R,
    ) -> Result<(R, crate::HostProvenance), crate::HostProvenanceError>
    where
        Self: __KrsInitializer,
    {
        unreachable!("no type implements `__KrsInitializer`")
    }
}
