//! Registry of diagnostic codes owned by KRS.

use crate::Code;

/// A registered diagnostic code and its summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CodeInfo {
    /// Stable code supplied by the producer.
    pub code: Code,
    /// One-line explanation of the condition the code describes.
    pub summary: &'static str,
}

macro_rules! register_codes {
    ($($(#[$stage_doc:meta])* $stage:ident { $($name:ident: $spelling:literal => $summary:literal,)* })*) => {
        $(
            $(#[$stage_doc])*
            pub mod $stage {
                $(
                    #[doc = $summary]
                    pub const $name: crate::Code = crate::Code::registered($spelling);
                )*
            }
        )*

        /// Every diagnostic code owned by KRS and its summary.
        pub const REGISTRY: &[CodeInfo] = &[
            $($(CodeInfo { code: $stage::$name, summary: $summary },)*)*
        ];
    };
}

register_codes! {
    /// Diagnostics from whole-file expansion and its protocol.
    expand {
        PARSE: "krs::expand::parse" => "The authored file does not lex or parse as a Rust file.",
        UNSUPPORTED_SOURCE: "krs::expand::unsupported-source" => "The authored file starts with a byte order mark or a shebang line, which rustc strips and the fallback lexer does not.",
        ATTRIBUTE_ORDER: "krs::expand::attribute-order" => "A KRS attribute follows an attribute that rustc would expand first.",
        ATTRIBUTE_FORM: "krs::expand::attribute-form" => "A KRS attribute has a `key = value` form, which rustc rejects for attribute macros.",
        NOT_AN_ATTRIBUTE_MACRO: "krs::expand::not-an-attribute-macro" => "The first expandable attribute names a facade item that is not a KRS attribute macro.",
        NESTED_ATTRIBUTE: "krs::expand::nested-attribute" => "An expansion emitted a KRS attribute invocation, which this driver does not expand.",
        RECURSION: "krs::expand::recursion-limit" => "Rescanned invocations nest deeper than the expansion recursion limit.",
        REGISTRATION_SCOPE: "krs::expand::registration-scope" => "A descriptor factory is defined where the crate-root registration table cannot name it.",
        SELECTION: "krs::expand::selection" => "An explicitly selected invocation does not match a discovered one.",
        PRINT: "krs::expand::print" => "An expansion cannot be printed as text without changing its tokens.",
        PROTOCOL_ERROR: "krs::expand::protocol" => "The request was not a valid schema-1 request.",
    }
    /// Diagnostics from the editable-surface lesson policy and its protocol.
    policy {
        EDITABLE_FILE: "krs::policy::editable-file" => "Rejects a request file outside `editable_files`.",
        PARSE: "krs::policy::parse" => "Rejects a file that does not parse.",
        OUT_OF_LINE_MODULE: "krs::policy::out-of-line-module" => "Rejects `mod name;` that resolves outside `editable_files`.",
        PATH_ATTRIBUTE: "krs::policy::path-attribute" => "Rejects `#[path]`.",
        EXTERN_CRATE: "krs::policy::extern-crate" => "Rejects `extern crate`.",
        INCLUDE: "krs::policy::include" => "Rejects `include!`, `include_str!`, and `include_bytes!`.",
        ENV: "krs::policy::env" => "Rejects `env!` and `option_env!`.",
        MACRO_DEFINITION: "krs::policy::macro-definition" => "Rejects `macro_rules!` and `macro` definitions.",
        NON_KRS_PROC_MACRO: "krs::policy::non-krs-proc-macro" => "Rejects any procedural macro that is not a KRS facade macro.",
        KRS_IMPORT: "krs::policy::krs-import" => "Rejects KRS imports and unprefixed KRS names.",
        RESERVED_FACADE_ITEM: "krs::policy::reserved-facade-item" => "Rejects facade items whose name starts with `__`.",
        CFG: "krs::policy::cfg" => "Rejects `#[cfg]` and `#[cfg_attr]`.",
        KRS_ITEM_SCOPE: "krs::policy::krs-item-scope" => "Rejects KRS invocations outside the crate root's module level.",
        ATTRIBUTE_ORDER: "krs::policy::attribute-order" => "Rejects an order-sensitive attribute before a KRS attribute.",
        RESERVED_NAME: "krs::policy::reserved-name" => "Rejects an authored name in the generated-name namespace.",
        PROTOCOL_ERROR: "krs::policy::protocol" => "The request was not a valid schema-1 request.",
    }
}
