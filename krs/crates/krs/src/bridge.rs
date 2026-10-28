//! The hidden seams through which a KRS expansion asks rustc to resolve an
//! authored path or to check an authored item.
//!
//! They live apart from `lib.rs` because collection reads the framework
//! declarations of `lib.rs` (`__framework_sorts!`) as authored source: their
//! origin byte ranges and that file's content hash are part of every port's
//! emitted artifacts, so an edit here leaves those artifacts alone.

use std::marker::PhantomData;

use crate::{HostApplicationTarget, Term};

/// Rust-resolved metadata for an unqualified term head: the declaration a
/// one-segment path names, as rustc resolves it in the author's scope.
///
/// This is a hidden proc-macro implementation seam. The const selector is the
/// authored name, which keeps enum variants distinct after rustc has inferred
/// their owning enum from the author's lexical imports. Standalone
/// constructor types implement every selector.
///
/// A name that resolves to a Rust item no KRS macro declared (the prelude's
/// `Some`), or to a constructor family under a name none of its variants is
/// declared with, reaches this trait unimplemented, at the authored path.
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "[krs::expand::not-a-declaration] `{Self}` is not a KRS declaration of this name: a term names a constructor, function, constant, cell group or builtin operation",
    label = "this name resolves to `{Self}`, which KRS did not declare under it",
    note = "a constructor family's variant is named as it is declared; a `use` that renames it (`use Family::Variant as Other;`) gives rustc a name KRS does not declare"
)]
pub trait __KrsRuleApplication<const SELECTOR: u64>: 'static {
    /// Produces the exact host declaration target for the resolved Rust type.
    #[doc(hidden)]
    fn __krs_rule_application(authored_path: &str) -> HostApplicationTarget;
}

/// Resolves an unqualified readable-rule application from an inferred Rust
/// witness type.
#[doc(hidden)]
#[must_use]
pub fn __krs_resolve_rule_application<T, const SELECTOR: u64>(
    _witness: &Option<T>,
    authored_path: &str,
) -> HostApplicationTarget
where
    T: __KrsRuleApplication<SELECTOR>,
{
    T::__krs_rule_application(authored_path)
}

/// Classifies a reference-layer turbofish argument (KF-027) by autoref
/// method resolution: `(&&__KrsTurbofishProbe::<T>::new()).__krs_turbofish_kind()`
/// is a [`__KrsTurbofishAlias`] when `T` is a `Term<..>` sort alias such as
/// `Exp`, and a [`__KrsTurbofishMarker`] for a sort marker such as
/// `dyn ExpSort` or `k::builtin::Int`. The expansion requires the latter
/// with a diagnostic that names the marker.
#[doc(hidden)]
pub struct __KrsTurbofishProbe<T: ?Sized> {
    marker: PhantomData<fn(&T)>,
}

impl<T: ?Sized> __KrsTurbofishProbe<T> {
    #[doc(hidden)]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

/// The classification of a turbofish argument that is a `Term<..>` alias.
#[doc(hidden)]
pub struct __KrsTurbofishAlias;

/// The classification of a turbofish argument that is a sort marker.
#[doc(hidden)]
pub struct __KrsTurbofishMarker;

/// Selected first, through the extra reference, when the probed type is a
/// `Term<..>` alias.
#[doc(hidden)]
pub trait __KrsTurbofishAliasKind {
    #[doc(hidden)]
    fn __krs_turbofish_kind(&self) -> __KrsTurbofishAlias {
        __KrsTurbofishAlias
    }
}

impl<S: ?Sized> __KrsTurbofishAliasKind for &__KrsTurbofishProbe<Term<S>> {}

/// Selected for every other probed type, a sort marker.
#[doc(hidden)]
pub trait __KrsTurbofishMarkerKind {
    #[doc(hidden)]
    fn __krs_turbofish_kind(&self) -> __KrsTurbofishMarker {
        __KrsTurbofishMarker
    }
}

impl<T: ?Sized> __KrsTurbofishMarkerKind for __KrsTurbofishProbe<T> {}

/// A non-parametric `#[k::function]` production, which a `k::equations!`
/// header names.
///
/// This is a hidden proc-macro implementation seam: every equation of a
/// table takes its sort from [`Self::Result`], and each row's argument count
/// is checked against [`Self::Arguments`].
#[doc(hidden)]
#[diagnostic::on_unimplemented(
    message = "[krs::syntax::invalid-equation-table] `{Self}` is not a non-parametric `#[k::function]`",
    label = "a `k::equations!` header names the function its rows define",
    note = "the header names a function declared with `#[k::function]`; a parametric function names its instance in each equation, so it takes `#[k::equation]` fns instead"
)]
pub trait __KrsFunction {
    /// The function's result sort.
    type Result: ?Sized + 'static;
    /// The function's argument types, as a tuple.
    type Arguments;
}

/// A value of any type, for the arity check of a `k::equations!` row; it is
/// never called.
#[doc(hidden)]
#[must_use]
pub fn __krs_argument<T>() -> T {
    unreachable!("KRS arity checks are never evaluated")
}
