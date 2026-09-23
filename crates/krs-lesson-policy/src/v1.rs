//! Lesson policy version 1 (normative).
//!
//! Version 1 is a syntactic check of one authored file. It performs no name
//! resolution; it relies on every KRS macro being named as
//! `<facade_alias>::<entry>`, which it enforces. It runs before expansion
//! and before rustc, over the complete file parsed with `syn::parse_file` in
//! `proc_macro2` fallback mode, so every range is an exact UTF-8 byte range
//! in the authored file.
//!
//! Version 1 is frozen. Changing a table or a rule below requires a new
//! version.
//!
//! # Rules
//!
//! | Code | Rejects | Authored range |
//! |---|---|---|
//! | `krs::policy::editable-file` | a compile request containing a file not in `editable_files` | none (request level) |
//! | `krs::policy::parse` | a file that `syn::parse_file` does not accept | the span of the first parse error |
//! | `krs::policy::out-of-line-module` | `mod name;` without a body, unless `<dir>/name.rs` or `<dir>/name/mod.rs` is in `editable_files` | the `mod` item without its outer attributes |
//! | `krs::policy::path-attribute` | `#[path = …]` anywhere | the attribute |
//! | `krs::policy::extern-crate` | any `extern crate` item | the item without its outer attributes |
//! | `krs::policy::include` | `include!`, `include_str!`, `include_bytes!` under any path | the macro path through the closing delimiter |
//! | `krs::policy::env` | `env!` and `option_env!` under any path | the macro path through the closing delimiter |
//! | `krs::policy::macro-definition` | `macro_rules!` definitions and `macro` items | the item without its outer attributes |
//! | `krs::policy::non-krs-proc-macro` | an attribute that is neither an accepted KRS attribute nor an inert attribute; a `derive` path outside the built-in derives; a function-like macro that is neither a KRS function-like entry nor a standard macro | the attribute path, derive path, or macro path |
//! | `krs::policy::krs-import` | a `use` tree that imports a KRS entry from the facade, renames the facade, glob-imports the facade, or binds the facade alias to another item; a `mod` named like the facade alias; a KRS entry named without the facade prefix | the `use` subtree, the module name, or the attribute or macro path |
//! | `krs::policy::reserved-facade-item` | a facade path with a segment starting with `__`, in an attribute, a macro invocation, or a `use` tree | the attribute or macro path, or the `use` segment |
//! | `krs::policy::cfg` | `#[cfg]` and `#[cfg_attr]` anywhere | the attribute |
//! | `krs::policy::krs-item-scope` | a KRS invocation inside an inline `mod` or in a file that is not the crate root; a KRS attribute invocation, or a KRS macro in item or statement position, inside a block that no KRS invocation consumes | the attribute, or the macro path through the closing delimiter |
//!
//! `<dir>` is the directory that owns `display_file`'s child modules, joined
//! with the enclosing inline modules: the file's directory for `lib.rs`,
//! `main.rs`, and `mod.rs`, and `<dir>/<stem>/` for any other `<stem>.rs`.
//! The crate root is `src/lib.rs` or `src/main.rs`.
//!
//! `krs::policy::krs-item-scope` exists because explicit descriptor
//! registration (IR-07) names each generated factory from the crate root and
//! the factories are private to the scope that defines them. A KRS macro in
//! expression, pattern, or type position inside a block defines no factory
//! and is accepted there, for example `k::term![…]` in a helper function.
//!
//! A KRS invocation is an attribute `<alias>::<entry>` on an item, impl
//! item, or trait item with `entry` in [`ATTRIBUTE_ENTRIES`], or a macro
//! `<alias>::<entry>!` with `entry` in [`FUNCTION_ENTRIES`]. The path has
//! exactly two segments, no leading `::`, and no generic arguments.
//!
//! # Where the check looks
//!
//! The check walks every item, attribute, statement, expression, pattern,
//! and type of the file. It also scans the token trees of every accepted
//! macro invocation, including KRS invocations whose bodies the KRS
//! renderers re-emit as Rust, and of accepted KRS attribute arguments. In
//! token trees it recognizes a path followed by `!` and a delimited group as
//! a macro invocation (a single keyword is never a macro name),
//! `macro_rules! name { … }` as a definition, `extern crate` as an
//! `extern crate` item, `mod name;` as an out-of-line module, and `#[…]` or
//! `#![…]` that parses as an attribute as an attribute. A token-tree
//! attribute may be any KRS attribute entry or helper, because the
//! enclosing KRS renderer decides its position. `use` trees in token trees
//! are not checked.
//!
//! # KRS helper positions
//!
//! A helper is accepted as `<alias>::<helper>` only in these positions,
//! which are the ones the KRS renderers consume:
//!
//! | Position | Required outer attribute | Helpers |
//! |---|---|---|
//! | enum, after the outer attribute | `constructors` | [`ENUM_HELPERS`] |
//! | enum variant | `constructors` on the enum | [`VARIANT_HELPERS`] |
//! | struct field | `configuration` or `cell` on the struct | [`FIELD_HELPERS`] |
//! | function parameter | `init` on the function | [`PARAMETER_HELPERS`] |
//!
//! # Allowlists
//!
//! - KRS entries: [`ATTRIBUTE_ENTRIES`] and [`FUNCTION_ENTRIES`], exactly the
//!   `#[proc_macro_attribute]` and `#[proc_macro]` functions of
//!   `crates/krs-macros/src/lib.rs` whose names do not start with `__`. A
//!   `__`-prefixed entry point, such as `__framework_sorts`, is
//!   facade-internal and is rejected as `krs::policy::reserved-facade-item`.
//! - Inert attributes: [`INERT_ATTRIBUTES`], as single-segment paths.
//! - Built-in derives: [`BUILTIN_DERIVES`], bare or as
//!   `[::]core::<module>::<Name>` or `[::]std::<module>::<Name>`.
//! - Standard macros: [`STANDARD_MACROS`], bare or as
//!   `[::]core::<name>`, `[::]std::<name>`, or `[::]alloc::<name>`.

use crate::engine::{self, RuleSet};
use crate::{LessonPolicy, PolicyDiagnostic};

/// Rejects a request file outside `editable_files`.
pub const EDITABLE_FILE: &str = "krs::policy::editable-file";
/// Rejects a file that does not parse.
pub const PARSE: &str = "krs::policy::parse";
/// Rejects `mod name;` that resolves outside `editable_files`.
pub const OUT_OF_LINE_MODULE: &str = "krs::policy::out-of-line-module";
/// Rejects `#[path]`.
pub const PATH_ATTRIBUTE: &str = "krs::policy::path-attribute";
/// Rejects `extern crate`.
pub const EXTERN_CRATE: &str = "krs::policy::extern-crate";
/// Rejects `include!`, `include_str!`, and `include_bytes!`.
pub const INCLUDE: &str = "krs::policy::include";
/// Rejects `env!` and `option_env!`.
pub const ENV: &str = "krs::policy::env";
/// Rejects `macro_rules!` and `macro` definitions.
pub const MACRO_DEFINITION: &str = "krs::policy::macro-definition";
/// Rejects any procedural macro that is not a KRS facade macro.
pub const NON_KRS_PROC_MACRO: &str = "krs::policy::non-krs-proc-macro";
/// Rejects KRS imports and unprefixed KRS names.
pub const KRS_IMPORT: &str = "krs::policy::krs-import";
/// Rejects facade items whose name starts with `__`.
pub const RESERVED_FACADE_ITEM: &str = "krs::policy::reserved-facade-item";
/// Rejects `#[cfg]` and `#[cfg_attr]`.
pub const CFG: &str = "krs::policy::cfg";
/// Rejects KRS invocations outside the crate root's module level.
pub const KRS_ITEM_SCOPE: &str = "krs::policy::krs-item-scope";

/// Every diagnostic code of version 1, including the request-level ones.
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
];

/// The `#[proc_macro_attribute]` functions of `krs-macros`, in source order.
pub const ATTRIBUTE_ENTRIES: &[&str] = &[
    "sort",
    "symbol",
    "constructor",
    "function",
    "constructors",
    "token",
    "bracket",
    "subsort",
    "strict",
    "seqstrict",
    "configuration",
    "cell",
    "init",
    "rule",
    "equation",
    "simplification",
    "claim",
    "alias",
    "context_alias",
    "priority",
    "requires",
    "exists",
    "ensures",
];

/// The `#[proc_macro]` functions of `krs-macros` not starting with `__`, in
/// source order.
pub const FUNCTION_ENTRIES: &[&str] = &[
    "sorts",
    "rules",
    "term",
    "id",
    "bytes",
    "anonymous",
    "or_bool",
    "fragment",
    "k",
    "map",
    "cells",
    "precedence",
    "associativity",
];

/// Enum-level helpers consumed by a preceding `constructors` attribute
/// (`krs-syntax/src/enum_constructor.rs`, `take_enum_precedence`).
pub const ENUM_HELPERS: &[&str] = &["precedence"];

/// Variant helpers consumed by `constructors`
/// (`krs-syntax/src/enum_constructor.rs`, variant attribute loop).
pub const VARIANT_HELPERS: &[&str] = &["syntax", "format", "strict", "seqstrict", "alias"];

/// Field helpers consumed by `configuration` and `cell`
/// (`krs-syntax/src/configuration.rs`, `is_cell_attribute`).
pub const FIELD_HELPERS: &[&str] = &["cell"];

/// Parameter helpers consumed by `init`
/// (`krs-syntax/src/initializer.rs`, `is_config_var_attribute`).
pub const PARAMETER_HELPERS: &[&str] = &["config_var"];

/// Attributes with no expansion effect that lessons may use.
///
/// `no_mangle`, `export_name`, `link_section`, `used`, `link`, `feature`,
/// and `test` are excluded because they can collide with collector symbols
/// or enable unstable features on the compiler fork's `-dev` channel.
pub const INERT_ATTRIBUTES: &[&str] = &[
    "doc",
    "allow",
    "warn",
    "deny",
    "forbid",
    "expect",
    "must_use",
    "inline",
    "derive",
    "non_exhaustive",
    "repr",
];

/// Built-in derives with the `core`/`std` module that defines each.
pub const BUILTIN_DERIVES: &[(&str, &str)] = &[
    ("Clone", "clone"),
    ("Copy", "marker"),
    ("Debug", "fmt"),
    ("Default", "default"),
    ("Eq", "cmp"),
    ("Hash", "hash"),
    ("Ord", "cmp"),
    ("PartialEq", "cmp"),
    ("PartialOrd", "cmp"),
];

/// Crates under which a built-in derive may be named.
pub const DERIVE_CRATES: &[&str] = &["core", "std"];

/// Declarative standard macros that lessons may invoke.
pub const STANDARD_MACROS: &[&str] = &[
    "assert",
    "assert_eq",
    "assert_ne",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "format",
    "format_args",
    "matches",
    "panic",
    "todo",
    "unimplemented",
    "unreachable",
    "vec",
    "write",
    "writeln",
    "concat",
    "stringify",
];

/// Crates under which a standard macro may be named.
pub const STANDARD_MACRO_CRATES: &[&str] = &["core", "std", "alloc"];
/// The version 1 rule set: the tables above, and no rule that a later
/// version added.
pub(crate) static RULES: RuleSet = RuleSet {
    version: 1,
    attribute_entries: ATTRIBUTE_ENTRIES,
    function_entries: FUNCTION_ENTRIES,
    enum_helpers: ENUM_HELPERS,
    variant_helpers: VARIANT_HELPERS,
    field_helpers: FIELD_HELPERS,
    parameter_helpers: PARAMETER_HELPERS,
    inert_attributes: INERT_ATTRIBUTES,
    tool_attributes: &[],
    variant_attributes: &[],
    builtin_derives: BUILTIN_DERIVES,
    derive_crates: DERIVE_CRATES,
    standard_macros: STANDARD_MACROS,
    standard_macro_crates: STANDARD_MACRO_CRATES,
    order_sensitive_attributes: &[],
    reserved_name_prefix: None,
};

pub(crate) fn check(
    source: &str,
    display_file: &str,
    policy: &LessonPolicy,
) -> Vec<PolicyDiagnostic> {
    engine::check(source, display_file, policy, &RULES)
}
