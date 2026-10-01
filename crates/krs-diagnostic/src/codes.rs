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
    /// Diagnostics from semantic analysis and definition lowering.
    analysis {
        OVERLAPPING_RULE_HEADS: "krs::analysis::overlapping-rule-heads" => "Two rules have overlapping application heads.",
        SYMBOL_NAME_COLLISION: "krs::analysis::symbol-name-collision" => "Two declarations have the same emitted symbol name.",
        NAME_COLLISION: "krs::analysis::name-collision" => "Two declarations have the same name in a lowering namespace.",
    }
    /// Diagnostics forwarded from Rust expansion without a rustc-owned code.
    rust_expansion {
        UNCODED_ERROR: "krs::rust-expansion::uncoded-error" => "Rust expansion reported an error without a diagnostic code.",
    }
    /// Diagnostics from Rust token parsing and KRS syntax validation.
    syntax {
        RUST_SYNTAX: "krs::syntax::rust-syntax" => "Rust token parsing failed before KRS shape validation could finish.",
        UNEXPECTED_ATTRIBUTE_PAYLOAD: "krs::syntax::unexpected-attribute-payload" => "An attribute which takes no arguments received a payload.",
        UNKNOWN_ARGUMENT: "krs::syntax::unknown-argument" => "A keyed attribute argument is not part of the attribute grammar.",
        DUPLICATE_ARGUMENT: "krs::syntax::duplicate-argument" => "A keyed attribute argument occurred more than once.",
        MISSING_ARGUMENT: "krs::syntax::missing-argument" => "A required keyed attribute argument was absent.",
        INVALID_ARGUMENT_VALUE: "krs::syntax::invalid-argument-value" => "A keyed argument had the wrong Rust AST shape.",
        UNSUPPORTED_PATH: "krs::syntax::unsupported-path" => "A Rust path uses generics or another form outside the plain-path subset.",
        UNSUPPORTED_SORT_DECLARATION: "krs::syntax::unsupported-sort-declaration" => "A `sort` trait was not a non-generic, safe, empty marker trait.",
        UNSUPPORTED_CONSTRUCTOR_DECLARATION: "krs::syntax::unsupported-constructor-declaration" => "A constructor item was not a nongeneric unit or named-field struct.",
        UNSUPPORTED_ENUM_CONSTRUCTOR_DECLARATION: "krs::syntax::unsupported-enum-constructor-declaration" => "A closed enum constructor family was outside the supported Rust enum shape.",
        UNSUPPORTED_TOKEN_DECLARATION: "krs::syntax::unsupported-token-declaration" => "A token newtype was outside the closed token declaration shape.",
        UNSUPPORTED_SUBSORT_DECLARATION: "krs::syntax::unsupported-subsort-declaration" => "A subsort implementation was outside the explicit subsort impl shape.",
        INVALID_SYNTAX_TEMPLATE: "krs::syntax::invalid-syntax-template" => "A checked syntax or bracket template was malformed.",
        UNKNOWN_TEMPLATE_FIELD: "krs::syntax::unknown-template-field" => "A checked syntax template named an unknown constructor field.",
        INVALID_TEMPLATE_FIELD_OCCURRENCE: "krs::syntax::invalid-template-field-occurrence" => "A checked syntax template omitted or repeated a constructor field.",
        INVALID_TOKEN_REGEX: "krs::syntax::invalid-token-regex" => "Token regular-expression text was malformed.",
        INVALID_FORMAT: "krs::syntax::invalid-format" => "Structured unparse format text was malformed for its production.",
        INVALID_STRICTNESS: "krs::syntax::invalid-strictness" => "Strictness metadata was empty, repeated a field, or named an unknown field.",
        INVALID_GRAMMAR_MACRO: "krs::syntax::invalid-grammar-macro" => "A precedence or associativity macro payload was malformed.",
        INVALID_ENUM_PRECEDENCE: "krs::syntax::invalid-enum-precedence" => "An enum-level readable-family precedence chain was invalid.",
        UNSUPPORTED_CONFIGURATION_DECLARATION: "krs::syntax::unsupported-configuration-declaration" => "A configuration item was not a fixed cell-tree shape.",
        UNSUPPORTED_CONFIGURATION_FIELD: "krs::syntax::unsupported-configuration-field" => "A configuration field was outside the fixed cell shape.",
        UNSUPPORTED_INITIALIZER_SIGNATURE: "krs::syntax::unsupported-initializer-signature" => "An initializer function used an unsupported signature feature.",
        UNSUPPORTED_CONFIGURATION_VARIABLE: "krs::syntax::unsupported-configuration-variable" => "A configuration-variable parameter was outside the fixed-state subset.",
        AMBIGUOUS_MAIN_CONFIGURATION_VARIABLE: "krs::syntax::ambiguous-main-configuration-variable" => "More than one initializer parameter claimed the main configuration input.",
        UNSUPPORTED_INITIALIZER_BODY: "krs::syntax::unsupported-initializer-body" => "An initializer body was outside the closed declarative grammar.",
        MISSING_CONFIGURATION_FIELD: "krs::syntax::missing-configuration-field" => "The one required initializer field was absent.",
        DUPLICATE_CONFIGURATION_FIELD: "krs::syntax::duplicate-configuration-field" => "An initializer field occurred more than once.",
        INVALID_CELL_ATTRIBUTE: "krs::syntax::invalid-cell-attribute" => "A `#[k::cell(...)]` payload was malformed.",
        INVALID_STATE_MACRO: "krs::syntax::invalid-state-macro" => "A compiler-owned configuration/state macro payload was malformed.",
        INVALID_TRIVIA: "krs::syntax::invalid-trivia" => "Source trivia could not be classified against the token byte ranges.",
        UNSUPPORTED_DSL_BLOCK_COMMENT: "krs::syntax::unsupported-dsl-block-comment" => "A non-documentation block comment occurred in a line-comment-only DSL body.",
        UNSUPPORTED_RULE_SIGNATURE: "krs::syntax::unsupported-rule-signature" => "A rule function used a signature feature outside the one-clause rule ABI.",
        UNSUPPORTED_RULE_PATTERN: "krs::syntax::unsupported-rule-pattern" => "A rule subject was not a supported named-constructor pattern.",
        INVALID_TERM_TYPE: "krs::syntax::invalid-term-type" => "A symbolic constructor field or rule type was not a supported `Term` sort.",
        UNSUPPORTED_RULE_BODY: "krs::syntax::unsupported-rule-body" => "A rule body was not exactly one unterminated term expression.",
        UNEXPECTED_MACRO: "krs::syntax::unexpected-macro" => "A macro in a rule subject or result was not the reserved `term!` form.",
        UNSUPPORTED_TERM_EXPRESSION: "krs::syntax::unsupported-term-expression" => "A Rust expression is outside the closed named-term grammar.",
        MISSING_TOKEN_ENDPOINT: "krs::syntax::missing-token-endpoint" => "A token-bearing semantic node unexpectedly emitted no token leaves.",
        TOO_MANY_PROVENANCE_OCCURRENCES: "krs::syntax::too-many-provenance-occurrences" => "A single invocation contained more same-role nodes than `u32` can key.",
    }
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
