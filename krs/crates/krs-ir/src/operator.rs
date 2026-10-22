//! Rust's operators as notation for builtin operations.
//!
//! `a + b`, `!a`, `a < b`, and the other operators of [`BuiltinOperator`]
//! name an operation but not its domain: `+` is `int::add`, `float::add`, or
//! `string::concat`. Each builtin domain defines its operations on that domain
//! only, so the sorts of the operands select at most one well-sorted reading;
//! semantic analysis chooses it after sort inference ([`OperatorDomain`]) and
//! every later phase sees the builtin application.

use serde::{Deserialize, Serialize};

use crate::{BuiltinOperation, BuiltinSort, FacadeMarker};

/// A builtin domain whose operations an operator can denote.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperatorDomain {
    /// K's unbounded `Int`.
    Int,
    /// K's `Bool`.
    Bool,
    /// K's `String`.
    String,
    /// K's `Float`.
    Float,
}

impl OperatorDomain {
    /// Every domain, in the order diagnostics list them.
    pub const ALL: [Self; 4] = [Self::Int, Self::Bool, Self::String, Self::Float];

    /// The domain's builtin sort.
    #[must_use]
    pub const fn sort(self) -> BuiltinSort {
        match self {
            Self::Int => BuiltinSort::Int,
            Self::Bool => BuiltinSort::Bool,
            Self::String => BuiltinSort::String,
            Self::Float => BuiltinSort::Float,
        }
    }

    /// The domain of a builtin sort, if operators read in it.
    #[must_use]
    pub const fn of_sort(sort: BuiltinSort) -> Option<Self> {
        match sort {
            BuiltinSort::Int => Some(Self::Int),
            BuiltinSort::Bool => Some(Self::Bool),
            BuiltinSort::String => Some(Self::String),
            BuiltinSort::Float => Some(Self::Float),
            _ => None,
        }
    }

    /// The domain's name in a method turbofish (`Int` in `add::<Int>`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Int => "Int",
            Self::Bool => "Bool",
            Self::String => "String",
            Self::Float => "Float",
        }
    }
}

/// What an operator denotes in one domain.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperatorReading {
    /// The operation applied to the operands, in order.
    Operation(BuiltinOperation),
    /// `-x` on `Int`, which is `int::sub(0, x)`: K has no unary minus on
    /// `Int`, and `0 - x` is the negation of every unbounded integer.
    IntNegation,
}

impl OperatorReading {
    /// The operation the reading applies.
    #[must_use]
    pub const fn operation(self) -> BuiltinOperation {
        match self {
            Self::Operation(operation) => operation,
            Self::IntNegation => BuiltinOperation::IntSub,
        }
    }
}

macro_rules! builtin_operators {
    ($(
        $(#[$meta:meta])*
        $variant:ident {
            rust_name: $name:ident,
            symbol: $symbol:literal,
            arity: $arity:literal,
            int: $int:expr,
            bool: $bool:expr,
            string: $string:expr,
            float: $float:expr $(,)?
        }
    )*) => {
        /// A Rust operator that denotes a builtin operation once sort
        /// inference has chosen its domain.
        ///
        /// Precedence and associativity are Rust's, so an operator tree is
        /// the tree rustc parses.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum BuiltinOperator {
            $($(#[$meta])* $variant,)*
        }

        impl BuiltinOperator {
            /// Every operator, in stable semantic order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// The operator as written (`+`, `<=`, `!`).
            #[must_use]
            pub const fn symbol(self) -> &'static str {
                match self {
                    $(Self::$variant => $symbol,)*
                }
            }

            /// The number of operands.
            #[must_use]
            pub const fn arity(self) -> usize {
                match self {
                    $(Self::$variant => $arity,)*
                }
            }

            /// The facade marker an operator application names before its
            /// domain is chosen (`builtin::__operator::add`).
            #[must_use]
            pub const fn facade_marker(self) -> FacadeMarker {
                match self {
                    $(Self::$variant => FacadeMarker {
                        module: "__operator",
                        name: stringify!($name),
                    },)*
                }
            }

            /// What the operator denotes in `domain`, or `None` when the
            /// domain defines no such operation.
            #[must_use]
            pub const fn reading(self, domain: OperatorDomain) -> Option<OperatorReading> {
                match (self, domain) {
                    $(
                        (Self::$variant, OperatorDomain::Int) => $int,
                        (Self::$variant, OperatorDomain::Bool) => $bool,
                        (Self::$variant, OperatorDomain::String) => $string,
                        (Self::$variant, OperatorDomain::Float) => $float,
                    )*
                }
            }
        }
    };
}

/// The reading that applies `operation` to the operands in order.
const fn operation(operation: BuiltinOperation) -> OperatorReading {
    OperatorReading::Operation(operation)
}

/// The closed operator catalog, in stable semantic order, passed to
/// `$callback`. Each row names its facade marker (`rust_name`), the operator as
/// written, its arity, and its reading in each [`OperatorDomain`].
#[doc(hidden)]
#[macro_export]
macro_rules! __krs_builtin_operator_catalog {
    ($callback:path) => {
        $callback! {
            /// `a + b`: `+Int`, `+Float`, and `+String` (concatenation).
            Add {
                rust_name: add,
                symbol: "+",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntAdd)),
                bool: None,
                string: Some(operation(BuiltinOperation::StringConcat)),
                float: Some(operation(BuiltinOperation::FloatAdd)),
            }
            /// `a - b`.
            Sub {
                rust_name: sub,
                symbol: "-",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntSub)),
                bool: None,
                string: None,
                float: Some(operation(BuiltinOperation::FloatSub)),
            }
            /// `a * b`.
            Mul {
                rust_name: mul,
                symbol: "*",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntMul)),
                bool: None,
                string: None,
                float: Some(operation(BuiltinOperation::FloatMul)),
            }
            /// `a / b`: on `Int` the quotient truncated toward zero (`/Int`), as
            /// Rust's integer `/` is.
            Div {
                rust_name: div,
                symbol: "/",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntTDiv)),
                bool: None,
                string: None,
                float: Some(operation(BuiltinOperation::FloatDiv)),
            }
            /// `a % b`: on `Int` the remainder with the dividend's sign (`%Int`), as
            /// Rust's integer `%` is. The catalog has no `Float` remainder.
            Rem {
                rust_name: rem,
                symbol: "%",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntTMod)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a << b`.
            ShiftLeft {
                rust_name: shl,
                symbol: "<<",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntShiftLeft)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a >> b`: the arithmetic shift, as Rust's on a signed integer.
            ShiftRight {
                rust_name: shr,
                symbol: ">>",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntShiftRight)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a & b`: bitwise conjunction on `Int`. It is not a `Bool` connective:
            /// `&&` is.
            BitAnd {
                rust_name: bit_and,
                symbol: "&",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntBitAnd)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a | b`: bitwise disjunction on `Int`. It is not a `Bool` connective:
            /// `||` is.
            BitOr {
                rust_name: bit_or,
                symbol: "|",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntBitOr)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a ^ b`: bitwise exclusive disjunction on `Int`.
            BitXor {
                rust_name: bit_xor,
                symbol: "^",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntBitXor)),
                bool: None,
                string: None,
                float: None,
            }
            /// `a == b`: the domain's equality (`==Float` is IEEE equality).
            Eq {
                rust_name: eq,
                symbol: "==",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntEqual)),
                bool: Some(operation(BuiltinOperation::BoolEqual)),
                string: Some(operation(BuiltinOperation::StringEqual)),
                float: Some(operation(BuiltinOperation::FloatEqual)),
            }
            /// `a != b`.
            Ne {
                rust_name: ne,
                symbol: "!=",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntNotEqual)),
                bool: Some(operation(BuiltinOperation::BoolNotEqual)),
                string: Some(operation(BuiltinOperation::StringNotEqual)),
                float: Some(operation(BuiltinOperation::FloatNotEqual)),
            }
            /// `a < b`.
            Lt {
                rust_name: lt,
                symbol: "<",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntLess)),
                bool: None,
                string: Some(operation(BuiltinOperation::StringLess)),
                float: Some(operation(BuiltinOperation::FloatLess)),
            }
            /// `a <= b`.
            Le {
                rust_name: le,
                symbol: "<=",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntLessEqual)),
                bool: None,
                string: Some(operation(BuiltinOperation::StringLessEqual)),
                float: Some(operation(BuiltinOperation::FloatLessEqual)),
            }
            /// `a > b`.
            Gt {
                rust_name: gt,
                symbol: ">",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntGreater)),
                bool: None,
                string: Some(operation(BuiltinOperation::StringGreater)),
                float: Some(operation(BuiltinOperation::FloatGreater)),
            }
            /// `a >= b`.
            Ge {
                rust_name: ge,
                symbol: ">=",
                arity: 2,
                int: Some(operation(BuiltinOperation::IntGreaterEqual)),
                bool: None,
                string: Some(operation(BuiltinOperation::StringGreaterEqual)),
                float: Some(operation(BuiltinOperation::FloatGreaterEqual)),
            }
            /// `!a`: `notBool`, and on `Int` the bitwise complement `~Int`, as
            /// Rust's `!` on an integer is.
            Not {
                rust_name: not,
                symbol: "!",
                arity: 1,
                int: Some(operation(BuiltinOperation::IntBitNot)),
                bool: Some(operation(BuiltinOperation::BoolNot)),
                string: None,
                float: None,
            }
            /// `-a` on anything but a literal: `int::sub(0, a)` and `--Float`.
            Neg {
                rust_name: neg,
                symbol: "-",
                arity: 1,
                int: Some(OperatorReading::IntNegation),
                bool: None,
                string: None,
                float: Some(operation(BuiltinOperation::FloatNeg)),
            }
        }
    };
}

__krs_builtin_operator_catalog!(builtin_operators);

impl BuiltinOperator {
    /// The result sort of every reading, when the readings agree on one: a
    /// comparison is a `Bool` in every domain.
    #[must_use]
    pub const fn uniform_result(self) -> Option<BuiltinSort> {
        match self {
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => {
                Some(BuiltinSort::Bool)
            }
            _ => None,
        }
    }

    /// The domains that define the operator, in [`OperatorDomain::ALL`] order.
    #[must_use]
    pub fn domains(self) -> Vec<OperatorDomain> {
        OperatorDomain::ALL
            .into_iter()
            .filter(|domain| self.reading(*domain).is_some())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_reading_takes_the_operator_arity_and_stays_in_its_domain() {
        for operator in BuiltinOperator::ALL {
            for domain in operator.domains() {
                let reading = operator.reading(domain).expect("a listed domain reads");
                let spec = reading.operation().spec();
                let operands = match reading {
                    OperatorReading::Operation(_) => spec.argument_sorts.len(),
                    // `int::sub(0, x)` applies the binary subtraction to one operand.
                    OperatorReading::IntNegation => spec.argument_sorts.len() - 1,
                };
                assert_eq!(operands, operator.arity(), "{operator:?} in {domain:?}");
                for sort in spec.argument_sorts {
                    assert_eq!(
                        *sort,
                        crate::OperationSort::Builtin(domain.sort()),
                        "{operator:?} in {domain:?}"
                    );
                }
                let result = spec.result_sort.builtin();
                match operator.uniform_result() {
                    Some(uniform) => assert_eq!(result, Some(uniform)),
                    None => assert_eq!(result, Some(domain.sort())),
                }
            }
        }
    }

    #[test]
    fn bool_has_only_equality_and_negation() {
        let bool_operators = BuiltinOperator::ALL
            .into_iter()
            .filter(|operator| operator.reading(OperatorDomain::Bool).is_some())
            .collect::<Vec<_>>();
        assert_eq!(
            bool_operators,
            [
                BuiltinOperator::Eq,
                BuiltinOperator::Ne,
                BuiltinOperator::Not
            ]
        );
    }
}
