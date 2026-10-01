//! The lesson policy (normative).
//!
//! The policy is a syntactic check of one authored file. It performs no name
//! resolution; it relies on every KRS macro being named as
//! `<facade_alias>::<entry>`, which it enforces. It runs before expansion
//! and before rustc, over the complete file parsed with `syn::parse_file` in
//! `proc_macro2` fallback mode, so every range is an exact UTF-8 byte range
//! in the authored file.
//!
//! The KRS entry points, the helpers each item kind accepts, and the inert
//! attributes come from the surface catalogue [`krs_syntax::surface`]. The
//! tables of this module state what a lesson may write on top of that
//! catalogue.
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
//! | `krs::policy::non-krs-proc-macro` | an attribute that is neither an accepted KRS attribute nor an accepted inert, tool, or variant attribute; a `derive` path outside the built-in derives; a function-like macro that is neither a KRS function-like entry nor a standard macro | the attribute path, derive path, or macro path |
//! | `krs::policy::krs-import` | a `use` tree that imports a KRS entry from the facade, renames the facade, glob-imports the facade, or binds the facade alias to another item; a `mod` named like the facade alias; a KRS entry named without the facade prefix | the `use` subtree, the module name, or the attribute or macro path |
//! | `krs::policy::reserved-facade-item` | a facade path with a segment starting with `__`, in an attribute, a macro invocation, or a `use` tree | the attribute or macro path, or the `use` segment |
//! | `krs::policy::cfg` | `#[cfg]` and `#[cfg_attr]` anywhere | the attribute |
//! | `krs::policy::krs-item-scope` | a KRS invocation inside an inline `mod` or in a file that is not the crate root; a KRS attribute invocation, or a KRS macro in item or statement position, inside a block that no KRS invocation consumes | the attribute, or the macro path through the closing delimiter |
//! | `krs::policy::attribute-order` | an attribute in [`ORDER_SENSITIVE_ATTRIBUTES`] that precedes the first KRS attribute invocation on the same item, impl item, or trait item | the preceding attribute |
//! | `krs::policy::reserved-name` | an item, associated item, foreign item, or `use` binding whose name, compared in ASCII lowercase, starts with [`RESERVED_NAME_PREFIX`] | the item's name, or the `use` subtree |
//!
//! `<dir>` is the directory that owns `display_file`'s child modules, joined
//! with the enclosing inline modules: the file's directory for `lib.rs`,
//! `main.rs`, and `mod.rs`, and `<dir>/<stem>/` for any other `<stem>.rs`.
//! The crate root is `src/lib.rs` or `src/main.rs`.
//!
//! `krs::policy::krs-item-scope` exists because explicit descriptor
//! registration names each generated factory from the crate root and
//! the factories are private to the scope that defines them. A KRS macro in
//! expression, pattern, or type position inside a block defines no factory
//! and is accepted there, for example `k::term![…]` in a helper function.
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
//! A KRS invocation is an attribute `<alias>::<entry>` on an item, impl
//! item, or trait item with `entry` an
//! [`AttributeMacro`](krs_syntax::surface::AttributeMacro), or a macro
//! `<alias>::<entry>!` with `entry` a
//! [`FunctionMacro`](krs_syntax::surface::FunctionMacro), as
//! [`krs_syntax::surface::resolve`] decides: the path has exactly two
//! segments, no leading `::`, and no generic arguments.
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
//! | enum, after the outer attribute | `constructors` | [`ENUM_HELPERS`](krs_syntax::surface::ENUM_HELPERS) |
//! | enum variant | `constructors` on the enum | [`VARIANT_HELPERS`](krs_syntax::surface::VARIANT_HELPERS) |
//! | struct field | `configuration` or `cell` on the struct | [`FIELD_HELPERS`](krs_syntax::surface::FIELD_HELPERS) |
//! | function parameter | `init` on the function | [`PARAMETER_HELPERS`](krs_syntax::surface::PARAMETER_HELPERS) |
//!
//! # Allowlists
//!
//! - KRS entries: every [`Entry`](krs_syntax::surface::Entry) that is not
//!   reserved. A reserved (`__`-prefixed) entry point, such as
//!   `__framework_sorts`, is facade-internal and is rejected as
//!   `krs::policy::reserved-facade-item`.
//! - Inert attributes: [`INERT_ATTRIBUTES`], as single-segment paths; a
//!   subset of [`krs_syntax::surface::INERT_ATTRIBUTES`].
//! - `derive`, listing only built-in derives: [`BUILTIN_DERIVES`], bare or as
//!   `[::]core::<module>::<Name>` or `[::]std::<module>::<Name>`.
//! - Tool attributes: [`TOOL_ATTRIBUTES`], as bare two-segment paths without
//!   arguments, in every position where an inert attribute is accepted.
//!   rustc does not expand tool attributes, and the path-C expander skips
//!   them when it chooses the attribute to expand, so their order relative
//!   to a KRS attribute does not matter.
//! - Variant attributes: [`VARIANT_ATTRIBUTES`], as bare single-segment
//!   paths on enum variants only; elsewhere, or with arguments, they are
//!   `krs::policy::non-krs-proc-macro`. `#[default]` is the helper of the
//!   built-in `Default` derive, which rustc resolves and checks; the policy
//!   does not require the derive.
//! - Standard macros: [`STANDARD_MACROS`], bare or as `[::]core::<name>`,
//!   `[::]std::<name>`, or `[::]alloc::<name>`.

/// Rejects a request file outside `editable_files`.
pub const EDITABLE_FILE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::EDITABLE_FILE;
    CODE.as_str()
};
/// Rejects a file that does not parse.
pub const PARSE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::PARSE;
    CODE.as_str()
};
/// Rejects `mod name;` that resolves outside `editable_files`.
pub const OUT_OF_LINE_MODULE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::OUT_OF_LINE_MODULE;
    CODE.as_str()
};
/// Rejects `#[path]`.
pub const PATH_ATTRIBUTE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::PATH_ATTRIBUTE;
    CODE.as_str()
};
/// Rejects `extern crate`.
pub const EXTERN_CRATE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::EXTERN_CRATE;
    CODE.as_str()
};
/// Rejects `include!`, `include_str!`, and `include_bytes!`.
pub const INCLUDE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::INCLUDE;
    CODE.as_str()
};
/// Rejects `env!` and `option_env!`.
pub const ENV: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::ENV;
    CODE.as_str()
};
/// Rejects `macro_rules!` and `macro` definitions.
pub const MACRO_DEFINITION: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::MACRO_DEFINITION;
    CODE.as_str()
};
/// Rejects any procedural macro that is not a KRS facade macro.
pub const NON_KRS_PROC_MACRO: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::NON_KRS_PROC_MACRO;
    CODE.as_str()
};
/// Rejects KRS imports and unprefixed KRS names.
pub const KRS_IMPORT: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::KRS_IMPORT;
    CODE.as_str()
};
/// Rejects facade items whose name starts with `__`.
pub const RESERVED_FACADE_ITEM: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::RESERVED_FACADE_ITEM;
    CODE.as_str()
};
/// Rejects `#[cfg]` and `#[cfg_attr]`.
pub const CFG: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::CFG;
    CODE.as_str()
};
/// Rejects KRS invocations outside the crate root's module level.
pub const KRS_ITEM_SCOPE: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::KRS_ITEM_SCOPE;
    CODE.as_str()
};
/// Rejects an order-sensitive attribute before a KRS attribute.
pub const ATTRIBUTE_ORDER: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::ATTRIBUTE_ORDER;
    CODE.as_str()
};
/// Rejects an authored name in the generated-name namespace.
pub const RESERVED_NAME: &str = {
    const CODE: &krs_diagnostic::Code = &krs_diagnostic::codes::policy::RESERVED_NAME;
    CODE.as_str()
};

/// Rule diagnostic codes, including the request-level editable-file rejection.
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

/// The inert attributes lessons may use: a subset of
/// [`krs_syntax::surface::INERT_ATTRIBUTES`].
///
/// An attribute the catalogue adds is not accepted in lessons until it is
/// listed here. `no_mangle` is excluded because it can collide with
/// collector symbols.
pub const INERT_ATTRIBUTES: &[&str] = &[
    "doc",
    "allow",
    "warn",
    "deny",
    "forbid",
    "expect",
    "must_use",
    "inline",
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

/// Tool attributes accepted without arguments, as `(tool, name)`; each tool
/// is a namespace of [`krs_syntax::surface::TOOL_ATTRIBUTES`].
pub const TOOL_ATTRIBUTES: &[(&str, &str)] = &[("rustfmt", "skip")];

/// Single-segment attributes accepted without arguments on enum variants.
pub const VARIANT_ATTRIBUTES: &[&str] = &["default"];

/// Accepted attributes that rustc expands before a KRS attribute that
/// follows them. `cfg` and `cfg_attr` also are, but every position rejects
/// them as `krs::policy::cfg`.
pub const ORDER_SENSITIVE_ATTRIBUTES: &[&str] = &["derive"];

/// ASCII-lowercase prefix of the names KRS expansion generates.
pub const RESERVED_NAME_PREFIX: &str = "__krs";

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
