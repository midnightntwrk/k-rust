//! Conservative identity checks for variables printed in decoded KORE states.

use k_rust::kore::ast::Pattern;
use k_rust_backend::term::names::VariableProvenance;

/// Whether `name`, read in a decoded (externalized) state, can only be the external name of the
/// backend variable of that very name (README 6.2).
///
/// k-rust's `external_variable_name` prints a provenance marker `Rule#`, `Ex#` or `Eq#` without
/// its `#`, appends a fresh counter `!N` as the bare digits `N`, and writes every other
/// character outside `[a-zA-Z0-9'-]` as an apostrophe-delimited word; it is not injective
/// (`Ex#VarI1!0` and `Ex#VarI!10` both print as `ExVarI10`, and `Ex#VarI!0` prints as the
/// user name `ExVarI0`). A non-empty name of letters, digits and `-` that ends in no digit and
/// starts with none of `Rule`, `Ex` and `Eq` is printed only by the variable of the same name:
/// a marked name prints with the marker's letters first, a counted name ends in a digit, and a
/// name with any other character prints with an apostrophe. Any other name may stand for
/// several backend variables.
pub(crate) fn identifies_one_variable(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        && !name.ends_with(|character: char| character.is_ascii_digit())
        && !VariableProvenance::ALL
            .iter()
            .any(|provenance| name.starts_with(provenance.external_prefix()))
}

/// Every variable occurrence, including binders, has an unambiguous decoded identity.
pub(crate) fn names_exact(pattern: &Pattern) -> bool {
    pattern
        .variables()
        .iter()
        .all(|variable| identifies_one_variable(&variable.name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::support;

    #[test]
    fn exact_names_exclude_counter_and_provenance_spellings() {
        for name in ["X", "Path-Var", "Alpha"] {
            assert!(names_exact(&support::var(name, "SortNat")), "{name}");
        }
        for name in ["X1", "RuleX", "ExVarI", "EqV", "X!0", ""] {
            assert!(!names_exact(&support::var(name, "SortNat")), "{name}");
        }
    }
}
