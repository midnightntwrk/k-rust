//! Lesson policy version 2 (normative).
//!
//! Version 2 is [version 1](crate::v1) with the changes below; every rule,
//! range, and table of version 1 that this module does not change applies
//! unchanged. A lesson selects version 2 with `[policy] version = 2`.
//!
//! Version 2 is frozen. Changing a table or a rule below requires a new
//! version.
//!
//! # Added rules
//!
//! | Code | Rejects | Authored range |
//! |---|---|---|
//! | `krs::policy::attribute-order` | an attribute in [`ORDER_SENSITIVE_ATTRIBUTES`] that precedes the first KRS attribute invocation on the same item, impl item, or trait item | the preceding attribute |
//! | `krs::policy::reserved-name` | an item, associated item, foreign item, or `use` binding whose name, compared in ASCII lowercase, starts with [`RESERVED_NAME_PREFIX`] | the item's name, or the `use` subtree |
//!
//! `krs::policy::attribute-order` exists because rustc expands `#[derive]`
//! before an attribute macro that follows it, handing the KRS attribute an
//! item that it did not author, and the path-C expander rejects that order
//! (`krs::expand::attribute-order`) instead of emulating it. A derive that
//! follows the KRS attribute is accepted.
//!
//! `krs::policy::reserved-name` exists because the path-C expander appends
//! generated items to the crate root, the registration table
//! `__KRS_REGISTRATIONS` and its function `__krs_register_descriptors`, which
//! a native inventory build does not have. An authored crate-root item with
//! either name compiles natively and fails in the browser with E0428 in
//! generated-only text. Every other name KRS expansion generates
//! (`__krs_sort_descriptor_…`, `__KrsEnumVariant_…`, and the other
//! `__krs_…` names) is in the same namespace, so the whole namespace is
//! reserved rather than the two table names. Names that only bind locally,
//! such as `let` patterns, fields, and variants, are not checked, and names
//! inside macro token trees are not checked.
//!
//! # Changed allowlists
//!
//! - Tool attributes: [`TOOL_ATTRIBUTES`] are accepted as bare two-segment
//!   paths without arguments, in every position where an inert attribute is
//!   accepted. rustc does not expand tool attributes, and the path-C
//!   expander skips them when it chooses the attribute to expand, so their
//!   order relative to a KRS attribute does not matter.
//! - Variant attributes: [`VARIANT_ATTRIBUTES`] are accepted as bare
//!   single-segment paths on enum variants only; elsewhere, or with
//!   arguments, they are `krs::policy::non-krs-proc-macro`. `#[default]` is
//!   the helper of the built-in `Default` derive, which rustc resolves and
//!   checks; the policy does not require the derive.
//!
//! Every other table equals version 1's: [`ATTRIBUTE_ENTRIES`],
//! [`FUNCTION_ENTRIES`], the helper tables, [`INERT_ATTRIBUTES`],
//! [`BUILTIN_DERIVES`], [`DERIVE_CRATES`], [`STANDARD_MACROS`], and
//! [`STANDARD_MACRO_CRATES`].

use crate::engine::{self, RuleSet};
use crate::{LessonPolicy, PolicyDiagnostic, v1};

pub use crate::v1::{
    CFG, EDITABLE_FILE, ENV, EXTERN_CRATE, INCLUDE, KRS_IMPORT, KRS_ITEM_SCOPE, MACRO_DEFINITION,
    NON_KRS_PROC_MACRO, OUT_OF_LINE_MODULE, PARSE, PATH_ATTRIBUTE, RESERVED_FACADE_ITEM,
};

/// Rejects an order-sensitive attribute before a KRS attribute.
pub const ATTRIBUTE_ORDER: &str = "krs::policy::attribute-order";
/// Rejects an authored name in the generated-name namespace.
pub const RESERVED_NAME: &str = "krs::policy::reserved-name";

/// Every diagnostic code of version 2, including the request-level ones.
pub const CODES: &[&str] = &[
    EDITABLE_FILE,
    PARSE,
    OUT_OF_LINE_MODULE,
    PATH_ATTRIBUTE,
    EXTERN_CRATE,
    INCLUDE,
    ENV,
    MACRO_DEFINITION,
    NON_KRS_PROC_MACRO,
    KRS_IMPORT,
    RESERVED_FACADE_ITEM,
    CFG,
    KRS_ITEM_SCOPE,
    ATTRIBUTE_ORDER,
    RESERVED_NAME,
];

/// The KRS attribute entries (version 1's).
pub const ATTRIBUTE_ENTRIES: &[&str] = v1::ATTRIBUTE_ENTRIES;
/// The KRS function-like entries (version 1's).
pub const FUNCTION_ENTRIES: &[&str] = v1::FUNCTION_ENTRIES;
/// Enum-level helpers (version 1's).
pub const ENUM_HELPERS: &[&str] = v1::ENUM_HELPERS;
/// Variant helpers (version 1's).
pub const VARIANT_HELPERS: &[&str] = v1::VARIANT_HELPERS;
/// Field helpers (version 1's).
pub const FIELD_HELPERS: &[&str] = v1::FIELD_HELPERS;
/// Parameter helpers (version 1's).
pub const PARAMETER_HELPERS: &[&str] = v1::PARAMETER_HELPERS;
/// Single-segment inert attributes (version 1's).
pub const INERT_ATTRIBUTES: &[&str] = v1::INERT_ATTRIBUTES;
/// Built-in derives (version 1's).
pub const BUILTIN_DERIVES: &[(&str, &str)] = v1::BUILTIN_DERIVES;
/// Crates under which a built-in derive may be named (version 1's).
pub const DERIVE_CRATES: &[&str] = v1::DERIVE_CRATES;
/// Standard macros (version 1's).
pub const STANDARD_MACROS: &[&str] = v1::STANDARD_MACROS;
/// Crates under which a standard macro may be named (version 1's).
pub const STANDARD_MACRO_CRATES: &[&str] = v1::STANDARD_MACRO_CRATES;

/// Tool attributes accepted without arguments, as `(tool, name)`.
pub const TOOL_ATTRIBUTES: &[(&str, &str)] = &[("rustfmt", "skip")];

/// Single-segment attributes accepted without arguments on enum variants.
pub const VARIANT_ATTRIBUTES: &[&str] = &["default"];

/// Accepted attributes that rustc expands before a KRS attribute that
/// follows them. `cfg` and `cfg_attr` also are, but every position rejects
/// them as `krs::policy::cfg`.
pub const ORDER_SENSITIVE_ATTRIBUTES: &[&str] = &["derive"];

/// ASCII-lowercase prefix of the names KRS expansion generates.
pub const RESERVED_NAME_PREFIX: &str = "__krs";

/// The version 2 rule set.
pub(crate) static RULES: RuleSet = RuleSet {
    version: 2,
    attribute_entries: ATTRIBUTE_ENTRIES,
    function_entries: FUNCTION_ENTRIES,
    enum_helpers: ENUM_HELPERS,
    variant_helpers: VARIANT_HELPERS,
    field_helpers: FIELD_HELPERS,
    parameter_helpers: PARAMETER_HELPERS,
    inert_attributes: INERT_ATTRIBUTES,
    tool_attributes: TOOL_ATTRIBUTES,
    variant_attributes: VARIANT_ATTRIBUTES,
    builtin_derives: BUILTIN_DERIVES,
    derive_crates: DERIVE_CRATES,
    standard_macros: STANDARD_MACROS,
    standard_macro_crates: STANDARD_MACRO_CRATES,
    order_sensitive_attributes: ORDER_SENSITIVE_ATTRIBUTES,
    reserved_name_prefix: Some(RESERVED_NAME_PREFIX),
};

pub(crate) fn check(
    source: &str,
    display_file: &str,
    policy: &LessonPolicy,
) -> Vec<PolicyDiagnostic> {
    engine::check(source, display_file, policy, &RULES)
}
