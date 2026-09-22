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
//!   `crates/krs-macros/src/lib.rs`.
//! - Inert attributes: [`INERT_ATTRIBUTES`], as single-segment paths.
//! - Built-in derives: [`BUILTIN_DERIVES`], bare or as
//!   `[::]core::<module>::<Name>` or `[::]std::<module>::<Name>`.
//! - Standard macros: [`STANDARD_MACROS`], bare or as
//!   `[::]core::<name>`, `[::]std::<name>`, or `[::]alloc::<name>`.

use std::ops::Range;

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Attribute, FnArg, ImplItem, Item, ItemEnum, ItemExternCrate, ItemMacro, ItemMod, ItemStruct,
    ItemUse, Macro, Meta, Path, TraitItem, UseTree, Variant,
};

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

/// The `#[proc_macro]` functions of `krs-macros`, in source order.
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

const INCLUDE_MACROS: &[&str] = &["include", "include_str", "include_bytes"];
const ENV_MACROS: &[&str] = &["env", "option_env"];

/// Rust keywords, which never name a macro in a token-tree scan.
const KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut",
    "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "try",
    "type", "unsafe", "use", "where", "while", "yield", "abstract", "become", "box", "do", "final",
    "macro", "override", "priv", "typeof", "unsized", "virtual",
];

pub(crate) fn check(
    source: &str,
    display_file: &str,
    policy: &LessonPolicy,
) -> Vec<PolicyDiagnostic> {
    let bom = if source.starts_with('\u{feff}') { 3 } else { 0 };
    let parsed = syn::parse_file(source);
    let offset = match &parsed {
        Ok(file) => bom + file.shebang.as_ref().map_or(0, String::len),
        Err(_) => bom + shebang_len(&source[bom..]),
    };
    let mut checker = Checker {
        offset,
        file: display_file,
        policy,
        diagnostics: Vec::new(),
        contexts: Vec::new(),
        module_path: Vec::new(),
        module_scope: usize::from(!is_crate_root(display_file)),
        block_scope: 0,
        item_position: false,
        krs_depth: 0,
        helpers: PendingHelpers::default(),
    };
    match &parsed {
        Ok(file) => checker.visit_file(file),
        Err(error) => {
            let range = checker.range(error.span());
            checker.report(
                PARSE,
                format!("the lesson source does not parse: {error}"),
                range,
            );
        }
    }
    let mut diagnostics = checker.diagnostics;
    diagnostics.sort_by(|left, right| {
        let key = |diagnostic: &PolicyDiagnostic| {
            diagnostic
                .authored
                .as_ref()
                .map(|range| (range.start, range.end))
        };
        key(left).cmp(&key(right)).then(left.code.cmp(right.code))
    });
    diagnostics.dedup();
    diagnostics
}

/// Mirrors `syn::parse_file`'s shebang rule for the parse-error path.
fn shebang_len(content: &str) -> usize {
    if content.starts_with("#!") && !content[2..].trim_start().starts_with('[') {
        content.find('\n').unwrap_or(content.len())
    } else {
        0
    }
}

fn is_crate_root(display_file: &str) -> bool {
    matches!(display_file, "src/lib.rs" | "src/main.rs")
}

/// The directory, with a trailing `/` unless empty, that owns the child
/// modules of `display_file`.
fn module_directory(display_file: &str) -> String {
    let (parent, file) = display_file
        .rsplit_once('/')
        .map_or(("", display_file), |(parent, file)| (parent, file));
    let parent = if parent.is_empty() {
        String::new()
    } else {
        format!("{parent}/")
    };
    match file {
        "lib.rs" | "main.rs" | "mod.rs" => parent,
        other => format!("{parent}{}/", other.strip_suffix(".rs").unwrap_or(other)),
    }
}

fn unraw(name: String) -> String {
    match name.strip_prefix("r#") {
        Some(stripped) => stripped.to_owned(),
        None => name,
    }
}

/// Helpers that the next attributed child node of the current item accepts.
#[derive(Clone, Copy, Default)]
struct PendingHelpers {
    variant: &'static [&'static str],
    field: &'static [&'static str],
    parameter: &'static [&'static str],
}

/// The position of one attribute list.
struct AttributeContext<'ast> {
    attrs: &'ast [Attribute],
    /// KRS attribute entries are accepted (item, impl item, trait item).
    entries: bool,
    helpers: &'static [&'static str],
    /// Helpers are accepted only at this index and later.
    helpers_from: usize,
}

/// How an attribute's position constrains it.
#[derive(Clone, Copy)]
enum Position {
    /// A position of the syntax tree with the given entry and helper sets.
    Tree {
        entries: bool,
        helpers: &'static [&'static str],
    },
    /// An attribute inside a macro's token trees.
    TokenBody,
}

enum MacroClass {
    Krs,
    Standard,
    Include,
    Env,
    Definition,
    Reserved,
    Unprefixed,
    Other,
}

struct Checker<'a, 'ast> {
    offset: usize,
    file: &'a str,
    policy: &'a LessonPolicy,
    diagnostics: Vec<PolicyDiagnostic>,
    contexts: Vec<AttributeContext<'ast>>,
    /// Inline modules between the file root and the current node.
    module_path: Vec<String>,
    /// Enclosing inline modules, plus one for a file that is not the crate
    /// root.
    module_scope: usize,
    /// Enclosing blocks that no KRS invocation consumes.
    block_scope: usize,
    /// The macro being checked is in item or statement position.
    item_position: bool,
    /// Enclosing KRS invocations.
    krs_depth: usize,
    helpers: PendingHelpers,
}

impl<'ast> Checker<'_, 'ast> {
    fn alias(&self) -> &str {
        &self.policy.facade_alias
    }

    fn range(&self, span: Span) -> Range<usize> {
        let range = span.byte_range();
        range.start + self.offset..range.end + self.offset
    }

    fn span_range(&self, first: Span, last: Span) -> Range<usize> {
        self.range(first).start..self.range(last).end
    }

    fn report(&mut self, code: &'static str, message: String, range: Range<usize>) {
        self.diagnostics
            .push(PolicyDiagnostic::authored(code, message, self.file, range));
    }

    /// `Some(name)` when `path` is exactly `<alias>::<name>`.
    fn facade_member(&self, path: &Path) -> Option<String> {
        if path.leading_colon.is_some()
            || path.segments.len() != 2
            || path
                .segments
                .iter()
                .any(|segment| !segment.arguments.is_none())
            || path.segments[0].ident != self.alias()
        {
            return None;
        }
        Some(unraw(path.segments[1].ident.to_string()))
    }

    fn names_reserved_facade_item(&self, segments: &[String]) -> bool {
        segments.first().is_some_and(|first| first == self.alias())
            && segments[1..]
                .iter()
                .any(|segment| segment.starts_with("__"))
    }

    fn has_facade_attribute(&self, attrs: &[Attribute], names: &[&str]) -> bool {
        attrs.iter().any(|attribute| {
            self.facade_member(attribute.path())
                .is_some_and(|name| names.contains(&name.as_str()))
        })
    }

    fn is_krs_attribute_invocation(&self, attribute: &Attribute) -> bool {
        self.facade_member(attribute.path())
            .is_some_and(|name| ATTRIBUTE_ENTRIES.contains(&name.as_str()))
    }

    /// Records a KRS invocation and rejects it outside the crate root's
    /// module level. `item_position` is true for attribute invocations and
    /// for macros in item or statement position.
    fn krs_invocation(&mut self, name: &str, range: Range<usize>, item_position: bool) {
        if self.krs_depth == 0 && (self.module_scope > 0 || (self.block_scope > 0 && item_position))
        {
            let alias = self.alias().to_owned();
            self.report(
                KRS_ITEM_SCOPE,
                format!(
                    "`{alias}::{name}` must be invoked at the module level of the crate root; \
                     explicit descriptor registration cannot name a factory defined in a nested \
                     module or block"
                ),
                range,
            );
        }
    }

    fn position_of(&self, attribute: &Attribute) -> Position {
        for context in self.contexts.iter().rev() {
            if let Some(index) = context
                .attrs
                .iter()
                .position(|candidate| std::ptr::eq(candidate, attribute))
            {
                let helpers = if index >= context.helpers_from {
                    context.helpers
                } else {
                    &[]
                };
                return Position::Tree {
                    entries: context.entries,
                    helpers,
                };
            }
        }
        Position::Tree {
            entries: false,
            helpers: &[],
        }
    }

    /// Checks one attribute; returns whether its arguments belong to a KRS
    /// renderer and must be scanned as token trees.
    fn check_attribute(&mut self, attribute: &Attribute, position: Position) -> bool {
        let path = attribute.path();
        let attribute_range = self.range(attribute.span());
        let path_range = self.range(path.span());
        if let Some(ident) = path.get_ident() {
            let name = unraw(ident.to_string());
            match name.as_str() {
                "cfg" | "cfg_attr" => self.report(
                    CFG,
                    format!("`#[{name}]` is not accepted in lesson source (policy version 1)"),
                    attribute_range,
                ),
                "path" => self.report(
                    PATH_ATTRIBUTE,
                    "`#[path]` is not accepted in lesson source".to_owned(),
                    attribute_range,
                ),
                "derive" => self.check_derive(attribute, path_range),
                name if INERT_ATTRIBUTES.contains(&name) => {}
                name if ATTRIBUTE_ENTRIES.contains(&name) => {
                    let alias = self.alias().to_owned();
                    self.report(
                        KRS_IMPORT,
                        format!("KRS attribute `{name}` must be named `{alias}::{name}`"),
                        path_range,
                    );
                }
                name => self.report(
                    NON_KRS_PROC_MACRO,
                    format!("attribute `{name}` is neither a KRS attribute nor an inert attribute accepted in lessons"),
                    path_range,
                ),
            }
            return false;
        }
        if let Some(name) = self.facade_member(path) {
            let alias = self.alias().to_owned();
            if name.starts_with("__") {
                self.report(
                    RESERVED_FACADE_ITEM,
                    format!("`{alias}::{name}` is a hidden facade item and cannot be named in lesson source"),
                    path_range,
                );
                return false;
            }
            let entry = ATTRIBUTE_ENTRIES.contains(&name.as_str());
            let accepted = match position {
                Position::Tree { entries, helpers } => {
                    if entries && entry {
                        self.krs_invocation(&name, attribute_range, true);
                        true
                    } else {
                        helpers.contains(&name.as_str())
                    }
                }
                Position::TokenBody => {
                    entry
                        || [
                            ENUM_HELPERS,
                            VARIANT_HELPERS,
                            FIELD_HELPERS,
                            PARAMETER_HELPERS,
                        ]
                        .iter()
                        .any(|helpers| helpers.contains(&name.as_str()))
                }
            };
            if !accepted {
                self.report(
                    NON_KRS_PROC_MACRO,
                    format!(
                        "`#[{alias}::{name}]` is not a KRS attribute accepted in this position"
                    ),
                    path_range,
                );
            }
            return accepted;
        }
        let (leading, segments) = path_segments(path);
        if self.names_reserved_facade_item(&segments) {
            self.report(
                RESERVED_FACADE_ITEM,
                "hidden facade items cannot be named in lesson source".to_owned(),
                path_range,
            );
        } else {
            self.report(
                NON_KRS_PROC_MACRO,
                format!(
                    "attribute `{}` is neither a KRS attribute nor an inert attribute accepted in lessons",
                    display_path(leading, &segments)
                ),
                path_range,
            );
        }
        false
    }

    fn check_derive(&mut self, attribute: &Attribute, path_range: Range<usize>) {
        let parsed =
            attribute.parse_args_with(Punctuated::<Path, syn::Token![,]>::parse_terminated);
        let Ok(paths) = parsed else {
            self.report(
                NON_KRS_PROC_MACRO,
                "`derive` must list built-in derive paths".to_owned(),
                path_range,
            );
            return;
        };
        for path in &paths {
            if !is_builtin_derive(path) {
                let (leading, segments) = path_segments(path);
                let range = self.range(path.span());
                self.report(
                    NON_KRS_PROC_MACRO,
                    format!(
                        "derive `{}` is not a built-in derive; lessons cannot run external procedural macros",
                        display_path(leading, &segments)
                    ),
                    range,
                );
            }
        }
    }

    fn classify_macro(&self, leading: bool, segments: &[String]) -> MacroClass {
        let Some(last) = segments.last() else {
            return MacroClass::Other;
        };
        if INCLUDE_MACROS.contains(&last.as_str()) {
            return MacroClass::Include;
        }
        if ENV_MACROS.contains(&last.as_str()) {
            return MacroClass::Env;
        }
        if self.names_reserved_facade_item(segments) {
            return MacroClass::Reserved;
        }
        match (leading, segments) {
            (false, [name]) if name == "macro_rules" => MacroClass::Definition,
            (false, [name]) if FUNCTION_ENTRIES.contains(&name.as_str()) => MacroClass::Unprefixed,
            (false, [name]) if STANDARD_MACROS.contains(&name.as_str()) => MacroClass::Standard,
            (false, [alias, name])
                if alias == self.alias() && FUNCTION_ENTRIES.contains(&name.as_str()) =>
            {
                MacroClass::Krs
            }
            (_, [krate, name])
                if STANDARD_MACRO_CRATES.contains(&krate.as_str())
                    && STANDARD_MACROS.contains(&name.as_str()) =>
            {
                MacroClass::Standard
            }
            _ => MacroClass::Other,
        }
    }

    /// Checks one macro invocation and scans its tokens when it is accepted.
    fn check_macro(
        &mut self,
        leading: bool,
        segments: &[String],
        path_range: Range<usize>,
        close: Span,
        tokens: &TokenStream,
    ) {
        let whole = path_range.start..self.range(close).end;
        let shown = display_path(leading, segments);
        let item_position = std::mem::take(&mut self.item_position);
        match self.classify_macro(leading, segments) {
            MacroClass::Krs => {
                self.krs_invocation(&segments[1], whole, item_position);
                self.krs_depth += 1;
                self.scan_tokens(tokens);
                self.krs_depth -= 1;
            }
            MacroClass::Standard => self.scan_tokens(tokens),
            MacroClass::Include => self.report(
                INCLUDE,
                format!("`{shown}!` reads a file outside the lesson source"),
                whole,
            ),
            MacroClass::Env => self.report(
                ENV,
                format!("`{shown}!` reads the compiler environment"),
                whole,
            ),
            MacroClass::Definition => self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                whole,
            ),
            MacroClass::Reserved => self.report(
                RESERVED_FACADE_ITEM,
                format!("`{shown}!` is a hidden facade item and cannot be invoked in lesson source"),
                path_range,
            ),
            MacroClass::Unprefixed => {
                let alias = self.alias().to_owned();
                self.report(
                    KRS_IMPORT,
                    format!("KRS macro `{shown}!` must be named `{alias}::{shown}!`"),
                    path_range,
                );
            }
            MacroClass::Other => self.report(
                NON_KRS_PROC_MACRO,
                format!("macro `{shown}!` is neither a KRS macro nor a standard macro accepted in lessons"),
                path_range,
            ),
        }
    }

    fn check_out_of_line_module(&mut self, name: &str, range: Range<usize>) {
        let mut directory = module_directory(self.file);
        for module in &self.module_path {
            directory.push_str(module);
            directory.push('/');
        }
        let candidates = [
            format!("{directory}{name}.rs"),
            format!("{directory}{name}/mod.rs"),
        ];
        if !candidates
            .iter()
            .any(|candidate| self.policy.editable_files.contains(candidate))
        {
            self.report(
                OUT_OF_LINE_MODULE,
                format!(
                    "`mod {name};` resolves to `{}` or `{}`, which is not an editable file of this lesson",
                    candidates[0], candidates[1]
                ),
                range,
            );
        }
    }

    fn check_module_name(&mut self, ident: &syn::Ident) {
        if ident == self.alias() {
            let alias = self.alias().to_owned();
            let range = self.range(ident.span());
            self.report(
                KRS_IMPORT,
                format!("a module named `{alias}` shadows the KRS facade alias"),
                range,
            );
        }
    }

    fn check_use_tree(&mut self, tree: &UseTree, prefix: &mut Vec<String>) {
        let alias = self.alias().to_owned();
        let under_facade = prefix.first().is_some_and(|first| *first == alias);
        let direct_facade_child = prefix.len() == 1 && under_facade;
        match tree {
            UseTree::Path(path) => {
                let name = unraw(path.ident.to_string());
                if under_facade && name.starts_with("__") {
                    let range = self.range(path.ident.span());
                    self.report(
                        RESERVED_FACADE_ITEM,
                        format!("`{name}` is a hidden facade item and cannot be imported"),
                        range,
                    );
                    return;
                }
                prefix.push(name);
                self.check_use_tree(&path.tree, prefix);
                prefix.pop();
            }
            UseTree::Name(name) => {
                let ident = unraw(name.ident.to_string());
                let range = self.range(name.span());
                self.check_use_leaf(&ident, None, prefix, range);
            }
            UseTree::Rename(rename) => {
                let ident = unraw(rename.ident.to_string());
                let binding = unraw(rename.rename.to_string());
                let range = self.range(rename.span());
                self.check_use_leaf(&ident, Some(&binding), prefix, range);
            }
            UseTree::Glob(glob) => {
                if direct_facade_child {
                    let range = self.range(glob.span());
                    self.report(
                        KRS_IMPORT,
                        format!("`use {alias}::*` imports KRS macros without the facade prefix"),
                        range,
                    );
                }
            }
            UseTree::Group(group) => {
                for tree in &group.items {
                    self.check_use_tree(tree, prefix);
                }
            }
        }
    }

    fn check_use_leaf(
        &mut self,
        ident: &str,
        rename: Option<&str>,
        prefix: &[String],
        range: Range<usize>,
    ) {
        let alias = self.alias().to_owned();
        let under_facade = prefix.first().is_some_and(|first| *first == alias);
        let names_facade =
            (prefix.is_empty() && ident == alias) || (prefix == [alias.clone()] && ident == "self");
        if under_facade && ident.starts_with("__") {
            self.report(
                RESERVED_FACADE_ITEM,
                format!("`{ident}` is a hidden facade item and cannot be imported"),
                range,
            );
            return;
        }
        if names_facade {
            if rename.is_some_and(|binding| binding != alias) {
                self.report(
                    KRS_IMPORT,
                    format!("the KRS facade must be named `{alias}`; renaming it hides KRS macros from the lesson policy"),
                    range,
                );
            }
            return;
        }
        if prefix.len() == 1
            && under_facade
            && (ATTRIBUTE_ENTRIES.contains(&ident) || FUNCTION_ENTRIES.contains(&ident))
        {
            self.report(
                KRS_IMPORT,
                format!(
                    "KRS macro `{ident}` must be named `{alias}::{ident}` at each use, not imported"
                ),
                range,
            );
            return;
        }
        let binding = match rename {
            Some(binding) => binding,
            None if ident == "self" => prefix.last().map_or("", String::as_str),
            None => ident,
        };
        if binding == alias {
            self.report(
                KRS_IMPORT,
                format!("this import binds `{alias}`, which shadows the KRS facade alias"),
                range,
            );
        }
    }

    /// Scans macro or attribute token trees for nested constructs.
    fn scan_tokens(&mut self, stream: &TokenStream) {
        let tokens: Vec<TokenTree> = stream.clone().into_iter().collect();
        let mut index = 0;
        while index < tokens.len() {
            index = self.scan_token(&tokens, index);
        }
    }

    /// Scans the construct starting at `index` and returns the next index.
    fn scan_token(&mut self, tokens: &[TokenTree], index: usize) -> usize {
        match &tokens[index] {
            TokenTree::Group(group) => {
                self.scan_tokens(&group.stream());
                index + 1
            }
            TokenTree::Punct(punct) if punct.as_char() == '#' => {
                self.scan_attribute(tokens, index).unwrap_or(index + 1)
            }
            TokenTree::Ident(ident)
                if ident == "extern" && is_ident(tokens.get(index + 1), "crate") =>
            {
                let end = tokens[index + 2..]
                    .iter()
                    .position(|token| is_punct(Some(token), ';'))
                    .map_or((index + 2).min(tokens.len() - 1), |offset| {
                        index + 2 + offset
                    });
                let range = self.span_range(ident.span(), tokens[end].span());
                self.report(
                    EXTERN_CRATE,
                    "lesson source cannot declare `extern crate`".to_owned(),
                    range,
                );
                end + 1
            }
            TokenTree::Ident(ident)
                if ident == "mod"
                    && matches!(tokens.get(index + 1), Some(TokenTree::Ident(_)))
                    && is_punct(tokens.get(index + 2), ';') =>
            {
                let name = unraw(tokens[index + 1].to_string());
                let range = self.span_range(ident.span(), tokens[index + 2].span());
                self.check_out_of_line_module(&name, range);
                index + 3
            }
            TokenTree::Ident(_) | TokenTree::Punct(_) => self.scan_macro_path(tokens, index),
            TokenTree::Literal(_) => index + 1,
        }
    }

    /// Recognizes `#[…]` or `#![…]` at `index`.
    fn scan_attribute(&mut self, tokens: &[TokenTree], index: usize) -> Option<usize> {
        let inner = is_punct(tokens.get(index + 1), '!');
        let group_index = index + 1 + usize::from(inner);
        let Some(TokenTree::Group(group)) = tokens.get(group_index) else {
            return None;
        };
        if group.delimiter() != Delimiter::Bracket {
            return None;
        }
        let stream: TokenStream = tokens[index..=group_index].iter().cloned().collect();
        let parser = if inner {
            Attribute::parse_inner
        } else {
            Attribute::parse_outer
        };
        let attributes = parser.parse2(stream).ok()?;
        let [attribute] = attributes.as_slice() else {
            return None;
        };
        if self.check_attribute(attribute, Position::TokenBody) || is_inert(attribute) {
            self.scan_tokens(&group.stream());
        }
        Some(group_index + 1)
    }

    /// Recognizes `[::]a::b…! (…)` at `index`.
    fn scan_macro_path(&mut self, tokens: &[TokenTree], index: usize) -> usize {
        let mut cursor = index;
        let leading = is_path_separator(tokens, cursor);
        if leading {
            cursor += 2;
        }
        let mut segments = Vec::new();
        let first = cursor;
        while let Some(TokenTree::Ident(ident)) = tokens.get(cursor) {
            segments.push(unraw(ident.to_string()));
            cursor += 1;
            if is_path_separator(tokens, cursor) {
                cursor += 2;
            } else {
                break;
            }
        }
        if segments.is_empty() {
            return index + 1;
        }
        let single_keyword =
            !leading && segments.len() == 1 && KEYWORDS.contains(&segments[0].as_str());
        if single_keyword || !is_punct(tokens.get(cursor), '!') {
            return cursor.max(index + 1);
        }
        let path_start = tokens[if leading { index } else { first }].span();
        let path_end = tokens[cursor - 1].span();
        let path_range = self.span_range(path_start, path_end);
        match tokens.get(cursor + 1) {
            Some(TokenTree::Group(group)) => {
                self.check_macro(
                    leading,
                    &segments,
                    path_range,
                    group.span_close(),
                    &group.stream(),
                );
                cursor + 2
            }
            Some(TokenTree::Ident(_))
                if !leading && segments.len() == 1 && segments[0] == "macro_rules" =>
            {
                let end = match tokens.get(cursor + 2) {
                    Some(TokenTree::Group(group)) => (
                        cursor + 2 + usize::from(is_punct(tokens.get(cursor + 3), ';')),
                        group.span_close(),
                    ),
                    _ => (cursor + 1, tokens[cursor + 1].span()),
                };
                let range = self.span_range(path_start, end.1);
                self.report(
                    MACRO_DEFINITION,
                    "lesson source cannot define macros".to_owned(),
                    range,
                );
                end.0 + 1
            }
            _ => cursor + 1,
        }
    }

    fn push_context(
        &mut self,
        attrs: &'ast [Attribute],
        entries: bool,
        helpers: &'static [&'static str],
        helpers_from: usize,
    ) {
        self.contexts.push(AttributeContext {
            attrs,
            entries,
            helpers,
            helpers_from,
        });
    }

    /// Visits an item-like node: pushes its attribute context, marks the
    /// node as consumed by KRS when it carries a KRS attribute invocation,
    /// and restores the state afterward.
    fn with_item(
        &mut self,
        attrs: &'ast [Attribute],
        helpers: &'static [&'static str],
        helpers_from: usize,
        pending: PendingHelpers,
        visit: impl FnOnce(&mut Self),
    ) {
        let krs = attrs
            .iter()
            .any(|attribute| self.is_krs_attribute_invocation(attribute));
        let saved = std::mem::replace(&mut self.helpers, pending);
        self.push_context(attrs, true, helpers, helpers_from);
        // Attributes are checked at the item's own scope; the body counts
        // as consumed by the KRS invocation.
        for attribute in attrs {
            self.visit_attribute(attribute);
        }
        self.contexts.pop();
        self.krs_depth += usize::from(krs);
        visit(self);
        self.krs_depth -= usize::from(krs);
        self.helpers = saved;
    }
}

fn is_inert(attribute: &Attribute) -> bool {
    attribute
        .path()
        .get_ident()
        .is_some_and(|ident| INERT_ATTRIBUTES.contains(&ident.to_string().as_str()))
}

fn is_builtin_derive(path: &Path) -> bool {
    if path
        .segments
        .iter()
        .any(|segment| !segment.arguments.is_none())
    {
        return false;
    }
    let (leading, segments) = path_segments(path);
    match segments.as_slice() {
        [name] if !leading => BUILTIN_DERIVES.iter().any(|(derive, _)| derive == name),
        [krate, module, name] => {
            DERIVE_CRATES.contains(&krate.as_str())
                && BUILTIN_DERIVES
                    .iter()
                    .any(|(derive, home)| derive == name && home == module)
        }
        _ => false,
    }
}

fn path_segments(path: &Path) -> (bool, Vec<String>) {
    (
        path.leading_colon.is_some(),
        path.segments
            .iter()
            .map(|segment| unraw(segment.ident.to_string()))
            .collect(),
    )
}

fn display_path(leading: bool, segments: &[String]) -> String {
    let joined = segments.join("::");
    if leading {
        format!("::{joined}")
    } else {
        joined
    }
}

fn is_punct(token: Option<&TokenTree>, character: char) -> bool {
    matches!(token, Some(TokenTree::Punct(punct)) if punct.as_char() == character)
}

fn is_ident(token: Option<&TokenTree>, name: &str) -> bool {
    matches!(token, Some(TokenTree::Ident(ident)) if ident == name)
}

fn is_path_separator(tokens: &[TokenTree], index: usize) -> bool {
    matches!(
        (tokens.get(index), tokens.get(index + 1)),
        (Some(TokenTree::Punct(first)), Some(TokenTree::Punct(second)))
            if first.as_char() == ':'
                && first.spacing() == proc_macro2::Spacing::Joint
                && second.as_char() == ':'
    )
}

impl<'ast> Visit<'ast> for Checker<'_, 'ast> {
    fn visit_attribute(&mut self, attribute: &'ast Attribute) {
        let position = self.position_of(attribute);
        if self.check_attribute(attribute, position) {
            if let Meta::List(list) = &attribute.meta {
                self.krs_depth += 1;
                self.scan_tokens(&list.tokens);
                self.krs_depth -= 1;
            }
            return;
        }
        if is_inert(attribute) {
            visit::visit_attribute(self, attribute);
        }
    }

    fn visit_item(&mut self, item: &'ast Item) {
        let (attrs, helpers, helpers_from, pending): (
            &'ast [Attribute],
            &'static [&'static str],
            usize,
            PendingHelpers,
        ) = match item {
            Item::Enum(ItemEnum { attrs, .. }) => {
                let constructors = attrs.iter().position(|attribute| {
                    self.facade_member(attribute.path())
                        .is_some_and(|name| name == "constructors")
                });
                match constructors {
                    Some(index) => (
                        attrs,
                        ENUM_HELPERS,
                        index + 1,
                        PendingHelpers {
                            variant: VARIANT_HELPERS,
                            ..PendingHelpers::default()
                        },
                    ),
                    None => (attrs, &[], 0, PendingHelpers::default()),
                }
            }
            Item::Struct(ItemStruct { attrs, .. }) => {
                let pending = if self.has_facade_attribute(attrs, &["configuration", "cell"]) {
                    PendingHelpers {
                        field: FIELD_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                };
                (attrs, &[], 0, pending)
            }
            Item::Fn(function) => {
                let pending = if self.has_facade_attribute(&function.attrs, &["init"]) {
                    PendingHelpers {
                        parameter: PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                };
                (&function.attrs, &[], 0, pending)
            }
            Item::Const(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::ExternCrate(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::ForeignMod(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Impl(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Macro(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Mod(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Static(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Trait(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::TraitAlias(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Type(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Union(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Use(item) => (&item.attrs, &[], 0, PendingHelpers::default()),
            Item::Verbatim(tokens) => {
                self.check_verbatim_item(tokens);
                return;
            }
            _ => (&[], &[], 0, PendingHelpers::default()),
        };
        self.with_item(attrs, helpers, helpers_from, pending, |checker| {
            checker.visit_item_body(item);
        });
    }

    fn visit_impl_item(&mut self, item: &'ast ImplItem) {
        let (attrs, pending): (&'ast [Attribute], PendingHelpers) = match item {
            ImplItem::Fn(function) => (
                &function.attrs,
                if self.has_facade_attribute(&function.attrs, &["init"]) {
                    PendingHelpers {
                        parameter: PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                },
            ),
            ImplItem::Const(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Type(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Macro(item) => (&item.attrs, PendingHelpers::default()),
            ImplItem::Verbatim(tokens) => {
                self.scan_tokens(tokens);
                return;
            }
            _ => (&[], PendingHelpers::default()),
        };
        self.with_item(attrs, &[], 0, pending, |checker| {
            checker.visit_impl_item_body(item);
        });
    }

    fn visit_trait_item(&mut self, item: &'ast TraitItem) {
        let (attrs, pending): (&'ast [Attribute], PendingHelpers) = match item {
            TraitItem::Fn(function) => (
                &function.attrs,
                if self.has_facade_attribute(&function.attrs, &["init"]) {
                    PendingHelpers {
                        parameter: PARAMETER_HELPERS,
                        ..PendingHelpers::default()
                    }
                } else {
                    PendingHelpers::default()
                },
            ),
            TraitItem::Const(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Type(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Macro(item) => (&item.attrs, PendingHelpers::default()),
            TraitItem::Verbatim(tokens) => {
                self.scan_tokens(tokens);
                return;
            }
            _ => (&[], PendingHelpers::default()),
        };
        self.with_item(attrs, &[], 0, pending, |checker| {
            checker.visit_trait_item_body(item);
        });
    }

    fn visit_variant(&mut self, variant: &'ast Variant) {
        let helpers = self.helpers.variant;
        let saved = std::mem::take(&mut self.helpers);
        self.push_context(&variant.attrs, false, helpers, 0);
        visit::visit_variant(self, variant);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_field(&mut self, field: &'ast syn::Field) {
        let helpers = self.helpers.field;
        let saved = std::mem::take(&mut self.helpers);
        self.push_context(&field.attrs, false, helpers, 0);
        visit::visit_field(self, field);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_fn_arg(&mut self, argument: &'ast FnArg) {
        let helpers = self.helpers.parameter;
        let saved = std::mem::take(&mut self.helpers);
        let attrs = match argument {
            FnArg::Receiver(receiver) => &receiver.attrs,
            FnArg::Typed(typed) => &typed.attrs,
        };
        self.push_context(attrs, false, helpers, 0);
        visit::visit_fn_arg(self, argument);
        self.contexts.pop();
        self.helpers = saved;
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        let nested = usize::from(self.krs_depth == 0);
        let saved = std::mem::take(&mut self.helpers);
        self.block_scope += nested;
        visit::visit_block(self, block);
        self.block_scope -= nested;
        self.helpers = saved;
    }

    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        self.check_module_name(&module.ident);
        match &module.content {
            None => {
                let mut bare = module.clone();
                bare.attrs.clear();
                let range = self.range(bare.span());
                let name = unraw(module.ident.to_string());
                self.check_out_of_line_module(&name, range);
            }
            Some((_, items)) => {
                self.module_path.push(unraw(module.ident.to_string()));
                self.module_scope += 1;
                for item in items {
                    self.visit_item(item);
                }
                self.module_scope -= 1;
                self.module_path.pop();
            }
        }
    }

    fn visit_item_extern_crate(&mut self, item: &'ast ItemExternCrate) {
        let mut bare = item.clone();
        bare.attrs.clear();
        let range = self.range(bare.span());
        self.report(
            EXTERN_CRATE,
            "lesson source cannot declare `extern crate`".to_owned(),
            range,
        );
    }

    fn visit_item_macro(&mut self, item: &'ast ItemMacro) {
        if item.mac.path.is_ident("macro_rules") {
            let mut bare = item.clone();
            bare.attrs.clear();
            let range = self.range(bare.span());
            self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                range,
            );
            return;
        }
        self.visit_item_position_macro(&item.mac);
    }

    fn visit_stmt_macro(&mut self, statement: &'ast syn::StmtMacro) {
        for attribute in &statement.attrs {
            self.visit_attribute(attribute);
        }
        self.visit_item_position_macro(&statement.mac);
    }

    fn visit_item_use(&mut self, item: &'ast ItemUse) {
        self.check_use_tree(&item.tree, &mut Vec::new());
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        let (leading, segments) = path_segments(&mac.path);
        let path_range = self.range(mac.path.span());
        self.check_macro(
            leading,
            &segments,
            path_range,
            mac.delimiter.span().close(),
            &mac.tokens,
        );
    }
}

impl<'ast> Checker<'_, 'ast> {
    fn visit_item_position_macro(&mut self, mac: &'ast Macro) {
        self.item_position = true;
        self.visit_macro(mac);
    }

    /// Visits an item's children other than its attributes, which
    /// [`Checker::with_item`] has already checked.
    fn visit_item_body(&mut self, item: &'ast Item) {
        match item {
            Item::Mod(module) => self.visit_item_mod(module),
            Item::ExternCrate(item) => self.visit_item_extern_crate(item),
            Item::Macro(item) => self.visit_item_macro(item),
            Item::Use(item) => self.visit_item_use(item),
            Item::Enum(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                for variant in &item.variants {
                    self.visit_variant(variant);
                }
            }
            Item::Struct(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                self.visit_fields(&item.fields);
            }
            Item::Fn(item) => {
                self.visit_visibility(&item.vis);
                self.visit_signature(&item.sig);
                self.visit_block(&item.block);
            }
            Item::Impl(item) => {
                self.visit_generics(&item.generics);
                if let Some((_, path, _)) = &item.trait_ {
                    self.visit_path(path);
                }
                self.visit_type(&item.self_ty);
                for item in &item.items {
                    self.visit_impl_item(item);
                }
            }
            Item::Trait(item) => {
                self.visit_visibility(&item.vis);
                self.visit_generics(&item.generics);
                for bound in &item.supertraits {
                    self.visit_type_param_bound(bound);
                }
                for item in &item.items {
                    self.visit_trait_item(item);
                }
            }
            Item::Const(item) => {
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            Item::Static(item) => {
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            Item::Type(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
            }
            Item::Union(item) => {
                self.visit_generics(&item.generics);
                self.visit_fields_named(&item.fields);
            }
            Item::TraitAlias(item) => {
                self.visit_generics(&item.generics);
                for bound in &item.bounds {
                    self.visit_type_param_bound(bound);
                }
            }
            Item::ForeignMod(item) => {
                for item in &item.items {
                    self.visit_foreign_item(item);
                }
            }
            _ => {}
        }
    }

    fn visit_impl_item_body(&mut self, item: &'ast ImplItem) {
        match item {
            ImplItem::Fn(function) => {
                self.visit_visibility(&function.vis);
                self.visit_signature(&function.sig);
                self.visit_block(&function.block);
            }
            ImplItem::Const(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
                self.visit_expr(&item.expr);
            }
            ImplItem::Type(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
            }
            ImplItem::Macro(item) => self.visit_item_position_macro(&item.mac),
            _ => {}
        }
    }

    fn visit_trait_item_body(&mut self, item: &'ast TraitItem) {
        match item {
            TraitItem::Fn(function) => {
                self.visit_signature(&function.sig);
                if let Some(block) = &function.default {
                    self.visit_block(block);
                }
            }
            TraitItem::Const(item) => {
                self.visit_generics(&item.generics);
                self.visit_type(&item.ty);
                if let Some((_, expr)) = &item.default {
                    self.visit_expr(expr);
                }
            }
            TraitItem::Type(item) => {
                self.visit_generics(&item.generics);
                for bound in &item.bounds {
                    self.visit_type_param_bound(bound);
                }
                if let Some((_, ty)) = &item.default {
                    self.visit_type(ty);
                }
            }
            TraitItem::Macro(item) => self.visit_item_position_macro(&item.mac),
            _ => {}
        }
    }

    /// A `macro` item or other syntax that `syn` keeps verbatim.
    fn check_verbatim_item(&mut self, tokens: &TokenStream) {
        let trees: Vec<TokenTree> = tokens.clone().into_iter().collect();
        let defines_macro = trees.iter().take_while(|token| !matches!(token, TokenTree::Group(group) if group.delimiter() == Delimiter::Brace)).any(|token| is_ident(Some(token), "macro"));
        if defines_macro {
            let range = self.range(tokens.span());
            self.report(
                MACRO_DEFINITION,
                "lesson source cannot define macros".to_owned(),
                range,
            );
        } else {
            self.scan_tokens(tokens);
        }
    }
}
