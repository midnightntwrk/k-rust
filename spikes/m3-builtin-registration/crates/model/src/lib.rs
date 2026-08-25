//! Closed, target-neutral semantic identities used by the builtin spike.

/// Sorts admitted by the deliberately tiny builtin catalog.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BuiltinSort {
    /// Mathematical integers.
    Int,
}

/// Closed semantic operation identity. Rust type identity never escapes into
/// this enum or deterministic collector output.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BuiltinOp {
    /// Integer addition.
    IntAdd,
    /// Integer subtraction.
    IntSub,
}

impl BuiltinOp {
    /// Stable target-neutral name.
    #[must_use]
    pub const fn stable_name(self) -> &'static str {
        match self {
            Self::IntAdd => "INT.add",
            Self::IntSub => "INT.sub",
        }
    }
}

/// Closed signature attached to a semantic builtin operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BuiltinSignature {
    /// Operand sorts in authored order.
    pub operands: &'static [BuiltinSort],
    /// Result sort.
    pub result: BuiltinSort,
}

