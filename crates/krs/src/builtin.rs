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
    use super::{Id, Map, Set};

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

    /// Removal of one key, `M [ K <- undef ]`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Remove<K = Id, V = ()>(pub Map<K, V>, pub K);

    /// Removal of every key of a set, `removeAll(M, S)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct RemoveAll<K = Id, V = ()>(pub Map<K, V>, pub Set<K>);

    /// The set of keys, `keys(M)`, typed `Set<K>`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Keys<K = Id, V = ()>(pub Map<K, V>);

    /// The keys as a list, `keys_list(M)`, typed `List<K>`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct KeysList<K = Id, V = ()>(pub Map<K, V>);

    /// The values as a list, `values(M)`, typed `List<V>`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Values<K = Id, V = ()>(pub Map<K, V>);

    /// The number of entries, `size(M)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Size<K = Id, V = ()>(pub Map<K, V>);

    /// Update with every entry of a second map, `updateMap(M1, M2)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct UpdateAll<K = Id, V = ()>(pub Map<K, V>, pub Map<K, V>);

    /// Total lookup with a default, `M [ K ] orDefault D`.
    ///
    /// Like [`get`], this is K's lookup, not `HashMap::get` returning an
    /// `Option`: the result is the value itself, projected to the sort expected
    /// where the application occurs.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct GetOrDefault<K = Id, V = ()>(pub Map<K, V>, pub K, pub V);

    pub use Get as get;
    pub use GetOrDefault as get_or_default;
    pub use InKeys as in_keys;
    pub use Keys as keys;
    pub use KeysList as keys_list;
    pub use Remove as remove;
    pub use RemoveAll as remove_all;
    pub use Size as size;
    /// Readable function-shaped spelling of a persistent update.
    ///
    /// Re-exporting the tuple struct, instead of defining a wrapper
    /// function, preserves the same identity in Rust's type and value
    /// namespaces. Module, facade, and local aliases therefore remain
    /// exact KRS application heads.
    pub use Update as update;
    pub use UpdateAll as update_all;
    pub use Values as values;
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

    /// Marker for list membership, `K in L` (K's `_inList_`).
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Contains<T = ()>(pub T, pub List<T>);

    pub use Concat as concat;
    pub use Contains as contains;
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
    use super::{List, Set};

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

    /// Marker for set difference, `S1 -Set S2`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Difference<T = ()>(pub Set<T>, pub Set<T>);

    /// Marker for set intersection, `intersectSet(S1, S2)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Intersect<T = ()>(pub Set<T>, pub Set<T>);

    /// Marker for `size(Set)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Size<T = ()>(pub Set<T>);

    /// Marker for set inclusion, `S1 <=Set S2`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct IsSubset<T = ()>(pub Set<T>, pub Set<T>);

    /// Marker for `Set2List(S)` from K's `COLLECTIONS` module.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ToList<T = ()>(pub Set<T>);

    /// Marker for `List2Set(L)` from K's `COLLECTIONS` module.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FromList<T = ()>(pub List<T>);

    pub use Concat as concat;
    pub use Contains as contains;
    pub use Difference as difference;
    pub use Empty as empty;
    pub use FromList as from_list;
    pub use Intersect as intersect;
    pub use IsSubset as is_subset;
    pub use Item as item;
    pub use Size as size;
    pub use ToList as to_list;
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

    /// Marker for the Euclidean remainder `modInt`, which is never negative,
    /// exactly like `i64::rem_euclid`.
    #[doc(alias = "modulo")]
    #[doc(alias = "modInt")]
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct RemEuclid(pub Int, pub Int);

    /// Marker for the truncating remainder `%Int`, which takes the dividend's
    /// sign, exactly like Rust's `%`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Rem(pub Int, pub Int);

    /// Marker for the Euclidean quotient `divInt`, exactly like `i64::div_euclid`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct DivEuclid(pub Int, pub Int);

    /// Marker for exponentiation `^Int`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Pow(pub Int, pub Int);

    /// Marker for the two's-complement bitwise complement `~Int`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BitNot(pub Int);

    /// Marker for `minInt`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Min(pub Int, pub Int);

    /// Marker for `maxInt`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Max(pub Int, pub Int);

    /// Marker for `absInt`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Abs(pub Int);

    /// Marker for `dividesInt`: whether the first operand divides the second.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Divides(pub Int, pub Int);

    /// Marker for `bitRangeInt(value, index, length)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BitRange(pub Int, pub Int, pub Int);

    /// Marker for `signExtendBitRangeInt(value, index, length)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SignExtendBitRange(pub Int, pub Int, pub Int);

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
    pub use Abs as abs;
    pub use Add as add;
    pub use BitAnd as bit_and;
    pub use BitNot as bit_not;
    pub use BitOr as bit_or;
    pub use BitRange as bit_range;
    pub use BitXor as bit_xor;
    pub use Div as div;
    pub use DivEuclid as div_euclid;
    pub use Divides as divides;
    pub use Ge as ge;
    pub use Gt as gt;
    pub use Le as le;
    pub use Log2 as log2;
    pub use Lt as lt;
    pub use Max as max;
    pub use Min as min;
    pub use Mul as mul;
    pub use Ne as ne;
    pub use Pow as pow;
    pub use PowMod as pow_mod;
    pub use Rem as rem;
    pub use RemEuclid as rem_euclid;
    pub use ShiftLeft as shift_left;
    pub use ShiftRight as shift_right;
    pub use SignExtendBitRange as sign_extend_bit_range;
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
    /// Marker for `xorBool`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Xor(pub Bool, pub Bool);

    /// Marker for `impliesBool`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Implies(pub Bool, pub Bool);

    /// Marker for `andThenBool`, a conjunction concrete backends may
    /// short-circuit. It is K's operator, not `Option::and_then`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct AndThen(pub Bool, pub Bool);

    /// Marker for `orElseBool`, a disjunction concrete backends may
    /// short-circuit.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct OrElse(pub Bool, pub Bool);

    pub use self::Eq as eq;
    pub use And as and;
    pub use AndThen as and_then;
    pub use Implies as implies;
    pub use Ne as ne;
    pub use Not as not;
    pub use Or as or;
    pub use OrElse as or_else;
    pub use Xor as xor;
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

    /// Marker for concatenation `+Bytes`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Concat(pub Bytes, pub Bytes);

    /// Marker for left padding.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PadLeft(pub Bytes, pub Int, pub Int);

    /// Marker for `reverseBytes`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Reverse(pub Bytes);

    /// Marker for `replaceAtBytes(dest, index, src)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ReplaceAt(pub Bytes, pub Int, pub Bytes);

    /// Marker for K's `Endianness` sort (`LE` or `BE`).
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Endianness;

    /// Marker for K's `Signedness` sort (`Signed` or `Unsigned`).
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Signedness;

    /// Marker for `LE`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct LittleEndian;

    /// Marker for `BE`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BigEndian;

    /// Marker for `Signed`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Signed;

    /// Marker for `Unsigned`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Unsigned;

    /// Marker for `Int2Bytes(length, value, endianness)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FromInt(pub Int, pub Int, pub Endianness);

    /// Marker for `Int2Bytes(value, endianness, signedness)`, the shortest
    /// encoding of the value.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FromIntNoLen(pub Int, pub Endianness, pub Signedness);

    /// Marker for `Bytes2Int(bytes, endianness, signedness)`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ToInt(pub Bytes, pub Endianness, pub Signedness);

    /// Marker for `String2Bytes`, the Latin-1 bytes of a string.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct StringToBytes(pub super::string::String);

    /// Marker for `Bytes2String`, the Latin-1 string of bytes.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BytesToString(pub Bytes);

    pub use BigEndian as big_endian;
    pub use BytesToString as to_string;
    pub use Concat as concat;
    pub use Empty as empty;
    pub use FromInt as from_int;
    pub use FromIntNoLen as from_int_no_len;
    pub use Get as get;
    pub use Length as length;
    pub use LittleEndian as little_endian;
    pub use PadLeft as pad_left;
    pub use PadRight as pad_right;
    pub use ReplaceAt as replace_at;
    pub use Reverse as reverse;
    pub use Signed as signed;
    pub use StringToBytes as from_string;
    pub use Substr as substr;
    pub use ToInt as to_int;
    pub use Unsigned as unsigned;
    pub use Update as update;
}

/// Operations from K's pinned `K-EQUAL` module, on terms of any sort.
pub mod kequal {
    use super::bool::Bool;

    /// Marker for `==K`: syntactic equality of two terms of any sort, like a
    /// derived `PartialEq` on a closed enum of terms. It differs from `int::eq`
    /// only on symbolic terms.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Eq<A = (), B = ()>(pub A, pub B);

    /// Marker for `=/=K`, the negation of `==K`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ne<A = (), B = ()>(pub A, pub B);

    /// Marker for K's sort-parametric function `#if c #then t #else e #fi`.
    ///
    /// It is a function, not control flow: k-rust and the Haskell backend
    /// evaluate both branches, while Java K's LLVM backend evaluates only the
    /// taken one, so keep both branches defined. Its sort is the least sort of
    /// the two branches that fits where it occurs.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ite<T = ()>(pub Bool, pub T, pub T);

    pub use self::Eq as eq;
    pub use Ite as ite;
    pub use Ne as ne;
}

/// Convenient root spelling of the builtin Boolean sort marker.
pub use bool::Bool;
/// Convenient root spelling of the builtin byte-string sort marker.
pub use bytes::Bytes;
/// Root spelling of the builtin byte-order sort marker.
pub use bytes::Endianness;
/// Root spelling of the builtin integer-interpretation sort marker.
pub use bytes::Signedness;
/// Root spelling of the builtin string sort marker, kept for compatibility.
///
/// Prefer `use k::builtin::string;` and `string::String`, which leaves
/// `std::string::String` unshadowed.
pub use string::String;

/// Builtin operations and sort marker from K's pinned `STRING` domain.
///
/// Import the module, not the marker: `use k::builtin::string;` and then
/// `string::String`, so the standard `String` stays in scope.
pub mod string {
    use super::{bool::Bool, int::Int};

    /// Host marker for K's `String` sort: a sequence of code points in
    /// U+0000..=U+00FF (Latin-1).
    ///
    /// A Rust string literal in a term is a String token; this marker is never
    /// a host string value.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct String;

    /// Marker for concatenation `+String`, linear in the operands' length.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Concat(pub String, pub String);

    /// Marker for `==String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Eq(pub String, pub String);

    /// Marker for `=/=String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ne(pub String, pub String);

    /// Marker for `<String`, lexicographic by code point.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Lt(pub String, pub String);

    /// Marker for `<=String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Le(pub String, pub String);

    /// Marker for `>String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Gt(pub String, pub String);

    /// Marker for `>=String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ge(pub String, pub String);

    /// Marker for `lengthString`, the number of code points.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Length(pub String);

    /// Marker for `substrString(s, start, end)` over a half-open range.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Substr(pub String, pub Int, pub Int);

    /// Marker for `findString(haystack, needle, from)`, `-1` when absent.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Find(pub String, pub String, pub Int);

    /// Marker for `chrChar`, the one-character string of a code point.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Chr(pub Int);

    /// Marker for `ordChar`, the code point of a one-character string.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Ord(pub String);

    /// Marker for `Int2String`, decimal.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FromInt(pub Int);

    /// Marker for `String2Int`: partial, undefined on text that is not a
    /// decimal integer (the analogue of `str::parse` returning `Err`).
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ToInt(pub String);

    /// Marker for `Bool2String`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FromBool(pub Bool);

    /// Marker for `String2Bool`, partial on text other than `"true"` and `"false"`.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ToBool(pub String);

    pub use self::Eq as eq;
    pub use self::Ord as ord;
    pub use Chr as chr;
    pub use Concat as concat;
    pub use Find as find;
    pub use FromBool as from_bool;
    pub use FromInt as from_int;
    pub use Ge as ge;
    pub use Gt as gt;
    pub use Le as le;
    pub use Length as length;
    pub use Lt as lt;
    pub use Ne as ne;
    pub use Substr as substr;
    pub use ToBool as to_bool;
    pub use ToInt as to_int;
}
/// Convenient root spelling of the builtin integer sort marker.
pub use int::Int;
