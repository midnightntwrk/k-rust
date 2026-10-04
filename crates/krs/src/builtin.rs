//! Intrinsic K sorts and operations used by the Rust authoring surface.
//!
//! Operation names are ordinary tuple-struct constructors. Consequently,
//! rustc checks operand types and arity before KRS collection, and ordinary
//! Rust module/import aliases retain the operation's exact type identity:
//!
//! ```
//! use krs as dialect;
//! use dialect::builtin::int as integer;
//! use integer::add as plus;
//!
//! let application: plus = plus(integer::Int, integer::Int);
//! let _: integer::add = application;
//! ```
//!
//! Wrong arity and wrong-sort operands are ordinary Rust errors:
//!
//! ```compile_fail
//! use krs::builtin::int::{Int, add};
//!
//! let _ = add(Int);
//! ```
//!
//! ```compile_fail
//! use krs::builtin::{bool::Bool, int};
//!
//! let _ = int::add(int::Int, Bool);
//! ```

/// Type-level spelling of K's computation sequence sort.
///
/// This is a zero-sized authoring token, not a host representation of a K
/// sequence. The compiler obtains meaning from descriptors emitted by
/// `k!`, never by evaluating this value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KSequence;

impl KSequence {
    /// Constructs the zero-sized result of a checked `k!` expansion.
    ///
    /// This is public only because procedural macro output in downstream
    /// crates must be able to name it.
    #[doc(hidden)]
    #[must_use]
    pub const fn __new() -> Self {
        Self
    }
}

/// Marker for K's lexical identifier sort from `ID-SYNTAX`.
///
/// This value is never used as a host identifier. Rust paths to the marker
/// let the collector resolve the closed builtin sort by `TypeId`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Id;

/// Type-shaped marker for K's finite-map sort.
///
/// `K` and `V` preserve useful Rust authoring information (for example
/// `Map<Id, Term<dyn Value>>`) while KRS resolves the outer `Map` marker to
/// K's unparameterized semantic `Map` sort. The value is zero-sized and is
/// never evaluated as a Rust collection.
///
/// The hidden constructor is the expansion target for a checked `map!`
/// island. It remains public so an expansion in a renamed downstream
/// dependency can construct the authoring shell:
///
/// ```
/// use krs as language;
/// use language::{Term, builtin::{Id, Map}};
///
/// trait Value {}
/// let _: Map<Id, Term<dyn Value>> = Map::__new();
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Map<K = Id, V = ()> {
    marker: std::marker::PhantomData<fn() -> (K, V)>,
}

/// Ordinary finite-map term operations.
pub mod map {
    use super::{Id, Map};

    /// Persistent update of one typed map entry.
    ///
    /// The generic defaults provide one stable marker identity for KRS's
    /// `TypeId` registry, while the tuple constructor retains a genuine
    /// three-operand Rust shape for direct authoring checks.
    ///
    /// ```compile_fail
    /// use krs::builtin::{Id, Map, map::update};
    ///
    /// let _ = update(Map::<Id, ()>::__new(), Id);
    /// ```
    ///
    /// ```compile_fail
    /// use krs::builtin::{Id, map::update};
    ///
    /// let _ = update(Id, Id, ());
    /// ```
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Update<K = Id, V = ()>(pub Map<K, V>, pub K, pub V);

    /// Partial lookup of one typed map entry.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Get<K = Id, V = ()>(pub Map<K, V>, pub K);

    /// Boolean key-membership test.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct InKeys<K = Id, V = ()>(pub K, pub Map<K, V>);

    pub use Get as get;
    pub use InKeys as in_keys;
    /// Readable function-shaped spelling of a persistent update.
    ///
    /// Re-exporting the tuple struct, instead of defining a wrapper
    /// function, preserves the same identity in Rust's type and value
    /// namespaces. Module, facade, and local aliases therefore remain
    /// exact KRS application heads.
    pub use Update as update;
}

impl<K, V> Map<K, V> {
    /// Constructs the zero-sized result of a checked `map!` expansion.
    ///
    /// This is public only so downstream procedural-macro output can name
    /// it; author code does not construct or execute host maps directly.
    #[doc(hidden)]
    #[must_use]
    pub const fn __new() -> Self {
        Self {
            marker: std::marker::PhantomData,
        }
    }
}

/// Type-shaped marker for K's associative builtin-list sort.
///
/// `T` retains useful Rust authoring information while KRS resolves the
/// outer marker to K's unparameterized semantic `List` sort.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct List<T = ()> {
    marker: std::marker::PhantomData<fn() -> T>,
}

impl<T> List<T> {
    /// Constructs the zero-sized authoring shell.
    #[doc(hidden)]
    #[must_use]
    pub const fn __new() -> Self {
        Self {
            marker: std::marker::PhantomData,
        }
    }
}

/// Ordinary operations from K's pinned `LIST` module.
pub mod list {
    use super::{List, int::Int};

    /// Marker for `.List`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Empty;

    /// Marker for `ListItem(K)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Item<T = ()>(pub T);

    /// Marker for associative list concatenation.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Concat<T = ()>(pub List<T>, pub List<T>);

    /// Marker for indexed lookup.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Get<T = ()>(pub List<T>, pub Int);

    /// Marker for persistent indexed update.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Update<T = ()>(pub List<T>, pub Int, pub T);

    /// Marker for `size(List)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Size<T = ()>(pub List<T>);

    /// Marker for `makeList(length, value)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Make<T = ()>(pub Int, pub T);

    /// Marker for `range(List, fromFront, fromBack)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Range<T = ()>(pub List<T>, pub Int, pub Int);

    /// Marker for `updateList(List, index, replacement)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct UpdateAll<T = ()>(pub List<T>, pub Int, pub List<T>);

    pub use Concat as concat;
    pub use Empty as empty;
    pub use Get as get;
    pub use Item as item;
    pub use Make as make;
    pub use Range as range;
    pub use Size as size;
    pub use Update as update;
    pub use UpdateAll as update_all;
}

/// Type-shaped marker for K's associative builtin-set sort.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Set<T = ()> {
    marker: std::marker::PhantomData<fn() -> T>,
}

impl<T> Set<T> {
    /// Constructs the zero-sized authoring shell.
    #[doc(hidden)]
    #[must_use]
    pub const fn __new() -> Self {
        Self {
            marker: std::marker::PhantomData,
        }
    }
}

/// Ordinary operations from K's pinned `SET` module.
pub mod set {
    use super::Set;

    /// Marker for `.Set`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Empty;

    /// Marker for `SetItem(K)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Item<T = ()>(pub T);

    /// Marker for associative set concatenation.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Concat<T = ()>(pub Set<T>, pub Set<T>);

    /// Marker for set union, including overlapping elements.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Union<T = ()>(pub Set<T>, pub Set<T>);

    /// Marker for set membership.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Contains<T = ()>(pub T, pub Set<T>);

    pub use Concat as concat;
    pub use Contains as contains;
    pub use Empty as empty;
    pub use Item as item;
    pub use Union as union;
}

/// Builtin operations and sort marker from K's pinned `INT` domain.
pub mod int {
    /// Host marker for K's arbitrary-precision `Int` sort.
    ///
    /// This is an authoring token, not a host integer value. Integer
    /// literals and symbolic bindings are interpreted by KRS term
    /// expansion and are never evaluated through this type.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Int;

    /// Marker for integer addition, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Add(pub Int, pub Int);

    /// Marker for integer subtraction, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Sub(pub Int, pub Int);

    /// Marker for integer multiplication, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Mul(pub Int, pub Int);

    /// Marker for truncating integer division, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Div(pub Int, pub Int);

    /// Marker for Euclidean integer modulus, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Mod(pub Int, pub Int);

    /// Marker for modular integer exponentiation.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PowMod(pub Int, pub Int, pub Int);

    /// Marker for the integer base-two logarithm.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Log2(pub Int);

    /// Marker for arithmetic integer right shift.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ShiftRight(pub Int, pub Int);

    /// Marker for integer left shift.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ShiftLeft(pub Int, pub Int);

    /// Marker for two's-complement integer bitwise conjunction.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BitAnd(pub Int, pub Int);

    /// Marker for two's-complement integer bitwise exclusive disjunction.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BitXor(pub Int, pub Int);

    /// Marker for two's-complement integer bitwise inclusive disjunction.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BitOr(pub Int, pub Int);

    /// Marker for integer greater-than-or-equal comparison.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ge(pub Int, pub Int);

    /// Marker for integer greater-than comparison.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Gt(pub Int, pub Int);

    /// Marker for integer less-than-or-equal comparison.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Le(pub Int, pub Int);

    /// Marker for integer less-than comparison.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Lt(pub Int, pub Int);

    /// Marker for integer equality.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Eq(pub Int, pub Int);

    /// Marker for integer inequality.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ne(pub Int, pub Int);

    // A `use` alias preserves both Rust namespaces. Each lowercase name is
    // therefore callable in value position and usable in
    // `TypeId::of::<...>()` in type position.
    pub use self::Eq as eq;
    pub use Add as add;
    pub use BitAnd as bit_and;
    pub use BitOr as bit_or;
    pub use BitXor as bit_xor;
    pub use Div as div;
    pub use Ge as ge;
    pub use Gt as gt;
    pub use Le as le;
    pub use Log2 as log2;
    pub use Lt as lt;
    pub use Mod as modulo;
    pub use Mul as mul;
    pub use Ne as ne;
    pub use PowMod as pow_mod;
    pub use ShiftLeft as shift_left;
    pub use ShiftRight as shift_right;
    pub use Sub as sub;
}

/// Builtin operations and sort marker from K's pinned `BOOL` domain.
pub mod bool {
    /// Host marker for K's `Bool` sort.
    ///
    /// This is an authoring token, not a host Boolean value. Boolean
    /// literals and symbolic bindings are interpreted by KRS term
    /// expansion and are never evaluated through this type.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Bool;

    /// Marker for Boolean negation, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Not(pub Bool);

    /// Marker for Boolean equality, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Eq(pub Bool, pub Bool);

    /// Marker for Boolean inequality, with its Rust-checked operand shape.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ne(pub Bool, pub Bool);

    /// Marker for object-language Boolean disjunction.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Or(pub Bool, pub Bool);

    /// Marker for object-language Boolean conjunction.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct And(pub Bool, pub Bool);

    // See the integer family: these aliases preserve constructor and type
    // identity while exposing the idiomatic authored spelling.
    pub use self::Eq as eq;
    pub use And as and;
    pub use Ne as ne;
    pub use Not as not;
    pub use Or as or;
}

/// Builtin operations and sort marker from K's pinned `BYTES` domain.
pub mod bytes {
    use super::int::Int;

    /// Host marker for K's `Bytes` sort.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Bytes;

    /// Marker for `lengthBytes`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Length(pub Bytes);

    /// Marker for byte lookup.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Get(pub Bytes, pub Int);

    /// Marker for `.Bytes`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Empty;

    /// Marker for byte update.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Update(pub Bytes, pub Int, pub Int);

    /// Marker for right padding.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PadRight(pub Bytes, pub Int, pub Int);

    /// Marker for byte substring extraction over a half-open range.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Substr(pub Bytes, pub Int, pub Int);

    pub use Empty as empty;
    pub use Get as get;
    pub use Length as length;
    pub use PadRight as pad_right;
    pub use Substr as substr;
    pub use Update as update;
}

/// Convenient root spelling of the builtin Boolean sort marker.
pub use bool::Bool;
/// Convenient root spelling of the builtin byte-string sort marker.
pub use bytes::Bytes;
/// Marker for K's string token sort from `STRING-SYNTAX`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct String;
/// Convenient root spelling of the builtin integer sort marker.
pub use int::Int;
