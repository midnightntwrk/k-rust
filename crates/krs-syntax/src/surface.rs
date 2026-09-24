//! The catalogue of the KRS macro surface.
//!
//! This module is the one place that names the KRS entry points, the helper
//! attributes each item kind accepts, and the attributes rustc never
//! expands, and it owns the one resolver that decides whether a path invokes
//! a KRS entry point. Expanders, the collector, and the lesson policy must
//! take these facts from here instead of spelling them again.
//!
//! Provenance roles are catalogued by [`ProvenanceRole`](crate::ProvenanceRole);
//! raw identifiers are compared through [`syn::ext::IdentExt::unraw`].
//!
//! # Resolution
//!
//! Authored code names an entry point as `<facade_alias>::<entry>`: exactly
//! two segments, no leading `::`, no generic arguments, where the first
//! segment is the facade alias and the second an entry-point name
//! ([`resolve`]). Generated code names it under the facade path that the
//! expansion host chose, such as `::k::<entry>` ([`resolve_under`]). Raw
//! identifiers compare by their unraw spelling, as rustc resolves them.
//!
//! A renderer receives an item whose invoking attribute rustc has already
//! removed and does not know the authored facade alias, so it recognises the
//! attributes it consumes from that item by their last path segment
//! ([`helper_entry`], [`last_segment_entry`]).

use syn::Path;
use syn::ext::IdentExt;

/// Declares a fieldless entry-point enum, its source-order `ALL` table, and
/// its `name`/`from_name` mapping to the `krs-macros` function names.
macro_rules! entry_points {
    ($(#[$meta:meta])* $enum:ident { $($(#[$variant_meta:meta])* $variant:ident = $name:literal,)* }) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum $enum {
            $($(#[$variant_meta])* $variant,)*
        }

        impl $enum {
            /// Every entry point, in `krs-macros` source order.
            pub const ALL: &'static [Self] = &[$(Self::$variant,)*];

            /// The `krs-macros` function name of this entry point.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self {
                    $(Self::$variant => $name,)*
                }
            }

            /// The entry point whose `krs-macros` function is named `name`.
            #[must_use]
            pub fn from_name(name: &str) -> Option<Self> {
                match name {
                    $($name => Some(Self::$variant),)*
                    _ => None,
                }
            }

            /// Whether the entry point is facade-internal: its name starts
            /// with `__`, and authored code must not name it.
            #[must_use]
            pub fn is_reserved(self) -> bool {
                self.name().starts_with("__")
            }
        }
    };
}

entry_points! {
    /// A `#[proc_macro_attribute]` entry point of `krs-macros`.
    AttributeMacro {
        /// `#[k::sort]`.
        Sort = "sort",
        /// `#[k::symbol]`.
        Symbol = "symbol",
        /// `#[k::constructor]`.
        Constructor = "constructor",
        /// `#[k::function]`.
        Function = "function",
        /// `#[k::constructors]`.
        Constructors = "constructors",
        /// `#[k::token]`.
        Token = "token",
        /// `#[k::bracket]`.
        Bracket = "bracket",
        /// `#[k::subsort]`.
        Subsort = "subsort",
        /// `#[k::strict]` outside a `#[k::constructor]` item.
        Strict = "strict",
        /// `#[k::seqstrict]` outside a `#[k::constructor]` item.
        Seqstrict = "seqstrict",
        /// `#[k::configuration]`.
        Configuration = "configuration",
        /// `#[k::cell]`.
        Cell = "cell",
        /// `#[k::init]`.
        Init = "init",
        /// `#[k::rule]`.
        Rule = "rule",
        /// `#[k::equation]`.
        Equation = "equation",
        /// `#[k::simplification]`.
        Simplification = "simplification",
        /// `#[k::claim]`.
        Claim = "claim",
        /// `#[k::alias]`.
        Alias = "alias",
        /// `#[k::context_alias]`.
        ContextAlias = "context_alias",
        /// `#[k::priority]`.
        Priority = "priority",
        /// `#[k::requires]` outside a `#[k::rule]` item.
        Requires = "requires",
        /// `#[k::exists]` outside a `#[k::claim]` item.
        Exists = "exists",
        /// `#[k::ensures]` outside a `#[k::claim]` item.
        Ensures = "ensures",
    }
}

entry_points! {
    /// A `#[proc_macro]` entry point of `krs-macros`.
    FunctionMacro {
        /// `k::sorts!`.
        Sorts = "sorts",
        /// The facade-internal `__framework_sorts!` block of `krs`.
        FrameworkSorts = "__framework_sorts",
        /// `k::rules!`.
        Rules = "rules",
        /// `k::term!`.
        Term = "term",
        /// `k::id!`.
        Id = "id",
        /// `k::bytes!`.
        Bytes = "bytes",
        /// `k::anonymous!`.
        Anonymous = "anonymous",
        /// `k::or_bool!`.
        OrBool = "or_bool",
        /// `k::fragment!`.
        Fragment = "fragment",
        /// `k::k!`.
        K = "k",
        /// `k::map!`.
        Map = "map",
        /// `k::cells!`.
        Cells = "cells",
        /// `k::precedence!`.
        Precedence = "precedence",
        /// `k::associativity!`.
        Associativity = "associativity",
    }
}

/// One entry point of `krs-macros`, attribute or function-like.
///
/// No attribute entry point shares its name with a function-like one, so a
/// name identifies at most one entry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Entry {
    /// A `#[proc_macro_attribute]` entry point.
    Attribute(AttributeMacro),
    /// A `#[proc_macro]` entry point.
    Function(FunctionMacro),
}

impl Entry {
    /// The `krs-macros` function name of this entry point.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Attribute(entry) => entry.name(),
            Self::Function(entry) => entry.name(),
        }
    }

    /// The entry point whose `krs-macros` function is named `name`.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        AttributeMacro::from_name(name)
            .map(Self::Attribute)
            .or_else(|| FunctionMacro::from_name(name).map(Self::Function))
    }

    /// Whether the entry point is facade-internal (its name starts with
    /// `__`).
    #[must_use]
    pub fn is_reserved(self) -> bool {
        self.name().starts_with("__")
    }
}

/// Helpers that `#[k::constructors]` consumes from the enum it annotates,
/// after the `constructors` attribute.
pub const ENUM_HELPERS: &[&str] = &["precedence"];

/// Helpers that `#[k::constructors]` consumes from each enum variant.
pub const VARIANT_HELPERS: &[&str] = &["syntax", "format", "strict", "seqstrict", "alias"];

/// Helpers that `#[k::configuration]` and `#[k::cell]` consume from struct
/// fields.
pub const FIELD_HELPERS: &[&str] = &["cell"];

/// Helpers that `#[k::init]` consumes from function parameters.
pub const PARAMETER_HELPERS: &[&str] = &["config_var"];

/// Single-segment attributes that rustc never expands: the built-in inert
/// attributes KRS recognises.
///
/// This is the one inert-attribute list of KRS. It is a fact about rustc, and
/// it excludes `derive`, `cfg`, and `cfg_attr`: rustc expands or evaluates
/// each of those before an attribute macro that follows it. What a lesson
/// may write is a separate, narrower policy decision that the lesson policy
/// states as its own allowlist.
pub const INERT_ATTRIBUTES: &[&str] = &[
    "allow",
    "automatically_derived",
    "cold",
    "deny",
    "deprecated",
    "doc",
    "expect",
    "forbid",
    "inline",
    "must_use",
    "no_mangle",
    "non_exhaustive",
    "repr",
    "track_caller",
    "warn",
];

/// Tool namespaces whose two-segment attributes rustc never expands.
pub const TOOL_ATTRIBUTES: &[&str] = &["clippy", "diagnostic", "rustdoc", "rustfmt"];

/// Whether rustc skips an attribute with this path when it chooses the
/// attribute to expand: a built-in inert attribute or a tool attribute.
#[must_use]
pub fn is_inert(path: &Path) -> bool {
    if path.leading_colon.is_some() {
        return false;
    }
    let names = match path.segments.len() {
        1 => INERT_ATTRIBUTES,
        2 => TOOL_ATTRIBUTES,
        _ => return false,
    };
    names
        .iter()
        .any(|name| path.segments[0].ident.unraw() == name)
}

/// The unraw name of `path` when it is exactly `<facade_alias>::<name>`,
/// whether or not `name` is an entry point.
#[must_use]
pub fn facade_member(path: &Path, facade_alias: &str) -> Option<String> {
    let [facade, member] = [path.segments.first()?, path.segments.last()?];
    (path.leading_colon.is_none()
        && path.segments.len() == 2
        && facade.arguments.is_none()
        && member.arguments.is_none()
        && facade.ident.unraw() == facade_alias)
        .then(|| member.ident.unraw().to_string())
}

/// The entry point that authored `path` invokes under `facade_alias`: `path`
/// is exactly `<facade_alias>::<entry>`.
#[must_use]
pub fn resolve(path: &Path, facade_alias: &str) -> Option<Entry> {
    Entry::from_name(&facade_member(path, facade_alias)?)
}

/// The entry point that generated `path` invokes under the facade path
/// `facade`: `path` is exactly `<facade>::<entry>`, with the same leading
/// `::`.
#[must_use]
pub fn resolve_under(path: &Path, facade: &Path) -> Option<Entry> {
    let segments = path.segments.iter().collect::<Vec<_>>();
    let (member, prefix) = segments.split_last()?;
    let matches = path.leading_colon.is_some() == facade.leading_colon.is_some()
        && member.arguments.is_none()
        && prefix.len() == facade.segments.len()
        && prefix
            .iter()
            .zip(&facade.segments)
            .all(|(segment, expected)| {
                segment.arguments.is_none()
                    && expected.arguments.is_none()
                    && segment.ident.unraw() == expected.ident.unraw()
            });
    matches
        .then(|| Entry::from_name(&member.ident.unraw().to_string()))
        .flatten()
}

/// The attribute entry point that a renderer consumes as a helper of the
/// item it received: a path of at least two segments whose last segment is
/// an attribute entry-point name.
#[must_use]
pub fn helper_entry(path: &Path) -> Option<AttributeMacro> {
    if path.segments.len() < 2 {
        return None;
    }
    last_segment_entry(path)
}

/// The attribute entry point named by the last segment of `path`, which may
/// be a single imported name such as `#[sort]`.
#[must_use]
pub fn last_segment_entry(path: &Path) -> Option<AttributeMacro> {
    AttributeMacro::from_name(&path.segments.last()?.ident.unraw().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(source: &str) -> Path {
        syn::parse_str(source).expect("a path")
    }

    #[test]
    fn entry_names_are_unique_across_kinds() {
        let mut names = AttributeMacro::ALL
            .iter()
            .map(|entry| entry.name())
            .chain(FunctionMacro::ALL.iter().map(|entry| entry.name()))
            .collect::<Vec<_>>();
        let count = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), count);
        for name in names {
            assert_eq!(Entry::from_name(name).map(Entry::name), Some(name));
        }
    }

    #[test]
    fn only_the_framework_block_is_reserved() {
        let reserved = AttributeMacro::ALL
            .iter()
            .copied()
            .map(Entry::Attribute)
            .chain(FunctionMacro::ALL.iter().copied().map(Entry::Function))
            .filter(|entry| entry.is_reserved())
            .collect::<Vec<_>>();
        assert_eq!(reserved, [Entry::Function(FunctionMacro::FrameworkSorts)]);
    }

    #[test]
    fn resolve_is_exact_and_alias_aware() {
        assert_eq!(
            resolve(&path("k::rule"), "k"),
            Some(Entry::Attribute(AttributeMacro::Rule))
        );
        assert_eq!(
            resolve(&path("krs::sorts"), "krs"),
            Some(Entry::Function(FunctionMacro::Sorts))
        );
        assert_eq!(
            resolve(&path("r#k::r#rule"), "k"),
            Some(Entry::Attribute(AttributeMacro::Rule))
        );
        for rejected in [
            "rule",
            "::k::rule",
            "other::rule",
            "k::rules::rule",
            "a::k::rule",
            "k::<u8>::rule",
            "k::rule::<u8>",
            "k::not_an_entry",
        ] {
            assert_eq!(resolve(&path(rejected), "k"), None, "{rejected}");
        }
        assert_eq!(resolve(&path("k::rule"), "krs"), None);
        assert_eq!(
            facade_member(&path("k::not_an_entry"), "k").as_deref(),
            Some("not_an_entry")
        );
    }

    #[test]
    fn resolve_under_matches_the_facade_path() {
        let facade = path("::k");
        assert_eq!(
            resolve_under(&path("::k::k"), &facade),
            Some(Entry::Function(FunctionMacro::K))
        );
        assert_eq!(resolve_under(&path("k::k"), &facade), None);
        assert_eq!(resolve_under(&path("::k::x::k"), &facade), None);
        assert_eq!(
            resolve_under(&path("crate::facade::map"), &path("crate::facade")),
            Some(Entry::Function(FunctionMacro::Map))
        );
    }

    #[test]
    fn renderer_helpers_match_the_last_segment() {
        assert_eq!(
            helper_entry(&path("k::strict")),
            Some(AttributeMacro::Strict)
        );
        assert_eq!(
            helper_entry(&path("anything::k::alias")),
            Some(AttributeMacro::Alias)
        );
        assert_eq!(helper_entry(&path("strict")), None);
        assert_eq!(
            last_segment_entry(&path("sort")),
            Some(AttributeMacro::Sort)
        );
        assert_eq!(last_segment_entry(&path("k::syntax")), None);
    }

    #[test]
    fn inert_attributes_exclude_expanded_builtins() {
        for name in ["derive", "cfg", "cfg_attr", "test"] {
            assert!(!is_inert(&path(name)), "{name}");
        }
        assert!(is_inert(&path("doc")));
        assert!(is_inert(&path("rustfmt::skip")));
        assert!(!is_inert(&path("::doc")));
        assert!(!is_inert(&path("k::doc")));
    }
}
