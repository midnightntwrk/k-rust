//! Matching-logic predicates (KF-039).
//!
//! K has two kinds of truth. `int::eq(a, b)` is an object-language `Bool`, a
//! value a rule can compute and store. `ml::equals(a, b)` is a statement
//! about what two patterns denote, K's `{ A #Equals B }`, which only the
//! prover reads. The connectives here build such statements, of type
//! [`Predicate`]; an object `Bool` enters them only as
//! `ml::equals(true, b)`, K's `{ true #Equals B }`.
//!
//! ```text
//! ml::top()            #Top            ml::bottom()        #Bottom
//! ml::not(p)           #Not ( P )      set complement, not bool::not
//! ml::and(p, q)        P #And Q        ml::or(p, q)        P #Or Q
//! ml::implies(p, q)    P #Implies Q
//! ml::equals(t, u)     { T #Equals U } ml::ceil(t)         #Ceil ( T ): t is defined
//! ml::exists(|x: S| p) #Exists X:S . P, a quantifier, not a callback
//! ```
//!
//! Predicates are written in claim `requires` and `ensures` conditions, in
//! the `requires` condition of a simplification, and on both sides of a
//! predicate simplification, whose subject and result have type
//! [`Predicate`]:
//!
//! ```ignore
//! #[k::simplification]
//! fn pf_defined(k::term![ml::ceil(Pf(x))]: Predicate) -> Predicate {
//!     ml::equals(true, int::gt(x, 0))
//! }
//! ```
//!
//! A simplification is an unchecked axiom, not a match arm: the prover
//! trusts it. Like the builtin operations, the connectives are function
//! shaped and have no operator or method sugar.

/// The type of a matching-logic predicate: the subject and result type of a
/// predicate simplification. It is a distinct type, not `Term<Bool>`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Predicate;

/// Marker for `ml::top()`, K's `#Top`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Top();

/// Marker for `ml::bottom()`, K's `#Bottom`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bottom();

/// Marker for `ml::not(p)`, K's `#Not ( P )`: set complement, not `bool::not`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Not(pub Predicate);

/// Marker for `ml::and(p, q)`, K's `P #And Q`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct And(pub Predicate, pub Predicate);

/// Marker for `ml::or(p, q)`, K's `P #Or Q`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Or(pub Predicate, pub Predicate);

/// Marker for `ml::implies(p, q)`, K's `P #Implies Q`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Implies(pub Predicate, pub Predicate);

/// Marker for `ml::equals(t, u)`, K's `{ T #Equals U }`: the two operands,
/// of one sort, denote the same value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Equals<A = (), B = ()>(pub A, pub B);

/// Marker for `ml::ceil(t)`, K's `#Ceil ( T )`: `t` is defined.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ceil<T = ()>(pub T);

/// Marker for `ml::exists(|x: S| p)`, K's `#Exists X:S . P`. Its one
/// argument is a closure with one typed parameter, which introduces the
/// quantified binder; it is a quantifier, not a callback.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Exists<F = ()>(pub F);

pub use And as and;
pub use Bottom as bottom;
pub use Ceil as ceil;
pub use Equals as equals;
pub use Exists as exists;
pub use Implies as implies;
pub use Not as not;
pub use Or as or;
pub use Top as top;
