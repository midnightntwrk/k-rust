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

                /// Every diagnostic code registered for this stage.
                pub const CODES: &[crate::Code] = &[$($name,)*];
            }
        )*

        /// Every diagnostic code owned by KRS and its summary.
        pub const REGISTRY: &[CodeInfo] = &[
            $($(CodeInfo { code: $stage::$name, summary: $summary },)*)*
        ];
    };
}

register_codes! {
    /// Diagnostics from host descriptor collection.
    collect {
        INVALID_PACKAGE_CONTEXT: "krs::collect::invalid-package-context" => "Caller-supplied package metadata was invalid.",
        HOST_IO: "krs::collect::host-io" => "A host path could not be canonicalized or read.",
        DUPLICATE_PACKAGE_CONTEXT: "krs::collect::duplicate-package-context" => "More than one context claimed the same host package lookup key.",
        DUPLICATE_KNAMESPACE: "krs::collect::duplicate-knamespace" => "More than one package claimed the same immutable K namespace.",
        UNSUPPORTED_SCHEMA_VERSION: "krs::collect::unsupported-schema-version" => "A descriptor carried a schema version other than the current one.",
        INVALID_BUILTIN_REGISTRY: "krs::collect::invalid-builtin-registry" => "The compiler-provided builtin marker catalog was incomplete or ambiguous.",
        PACKAGE_NOT_SELECTED: "krs::collect::package-not-selected" => "No selected Cargo package matched a descriptor's host lookup key.",
        CRATE_ROOT_MISMATCH: "krs::collect::crate-root-mismatch" => "The first `module_path!()` segment did not match the selected target.",
        INVALID_STABLE_IDENTITY: "krs::collect::invalid-stable-identity" => "A host item could not become a stable item identity.",
        DUPLICATE_ITEM_ID: "krs::collect::duplicate-item-id" => "Two declarations produced the same final stable identity.",
        ITEM_KIND_MISMATCH: "krs::collect::item-kind-mismatch" => "A descriptor payload did not agree with its declared item kind.",
        DUPLICATE_TYPE_DECLARATION: "krs::collect::duplicate-type-declaration" => "Two declarations exposed the same build-local Rust `TypeId`.",
        DECLARATION_BUILTIN_COLLISION: "krs::collect::declaration-builtin-collision" => "A Rust identity was assigned to both an authored declaration and a builtin.",
        MISSING_TYPE_DECLARATION: "krs::collect::missing-type-declaration" => "A sort or constructor declaration exposed no build-local Rust `TypeId`.",
        UNRESOLVED_TYPE_REFERENCE: "krs::collect::unresolved-type-reference" => "A Rust type reference had no declaration in the selected collection.",
        REFERENCE_KIND_MISMATCH: "krs::collect::reference-kind-mismatch" => "A resolved declaration had the wrong semantic item kind.",
        INVALID_CONFIGURATION: "krs::collect::invalid-configuration" => "A fixed configuration, cell, or configuration rule descriptor was malformed.",
        INVALID_DISPLAY_FILE: "krs::collect::invalid-display-file" => "A display filename was not a normalized relative source hint.",
        SOURCE_OUTSIDE_PACKAGE: "krs::collect::source-outside-package" => "A resolved source escaped its canonical package directory.",
        AMBIGUOUS_SOURCE_PATH: "krs::collect::ambiguous-source-path" => "A display hint resolved to multiple distinct files in the package.",
        SOURCE_POSITION_OUT_OF_BOUNDS: "krs::collect::source-position-out-of-bounds" => "A line or Unicode-scalar column was outside the exact source revision.",
        IMPRECISE_AUTHORED_ANCHOR: "krs::collect::imprecise-authored-anchor" => "A semantic node used an invocation-fallback rather than exact leaves.",
        SOURCE_SYNTAX: "krs::collect::source-syntax" => "The exact source no longer parses under the shared KRS parser.",
        UNRESOLVED_ATTRIBUTE: "krs::collect::unresolved-attribute" => "An authored attribute or item macro names a KRS entry point but does not invoke it under the package's facade alias.",
        STALE_ANCHOR: "krs::collect::stale-anchor" => "A host anchor did not match the corresponding reparsed semantic node.",
        AMBIGUOUS_ANCHOR: "krs::collect::ambiguous-anchor" => "More than one reparsed invocation matched a host descriptor.",
        PROVENANCE_MISMATCH: "krs::collect::provenance-mismatch" => "The macro and shared parser disagreed about the complete anchor set.",
    }
    /// Diagnostics from semantic analysis and definition lowering.
    analysis {
        DUPLICATE_ITEM_ID: "krs::analysis::duplicate-item-id" => "Two declarations use the same stable identity.",
        BUILTIN_SORT_NAME_COLLISION: "krs::analysis::builtin-sort-name-collision" => "An authored sort uses a compiler builtin sort name.",
        CONFIGURATION_COUNT: "krs::analysis::configuration-count" => "The selected descriptors do not contain exactly one configuration.",
        WRONG_ITEM_KIND: "krs::analysis::wrong-item-kind" => "A descriptor payload and its stable item kind disagree.",
        DANGLING_REFERENCE: "krs::analysis::dangling-reference" => "A descriptor reference names no selected declaration.",
        REFERENCE_KIND_MISMATCH: "krs::analysis::reference-kind-mismatch" => "A declaration reference uses the wrong namespace.",
        PARSER_REFERENCE_DISAGREEMENT: "krs::analysis::parser-reference-disagreement" => "Parser-owned origins or references disagree with a descriptor.",
        INVALID_TERM: "krs::analysis::invalid-term" => "A descriptor term cannot be represented structurally.",
        UNSUPPORTED_SHAPE: "krs::analysis::unsupported-shape" => "A semantic shape is outside the supported lowering subset.",
        INVALID_GENERATED_IDENTITY: "krs::analysis::invalid-generated-identity" => "A generated IR identity is invalid.",
        INVALID_SEMANTIC_THEORY: "krs::analysis::invalid-semantic-theory" => "Whole-theory semantic validation failed.",
        INVALID_PRODUCTION_TEMPLATE: "krs::analysis::invalid-production-template" => "Authored syntax cannot be represented by a production template.",
        INVALID_EMITTED_NAME: "krs::analysis::invalid-emitted-name" => "An emitted name is not canonical K syntax.",
        SOURCE_MAP_COLLISION: "krs::analysis::source-map-collision" => "Generated Definition nodes use the same source-map key.",
        INVALID_DEFINITION: "krs::analysis::invalid-definition" => "The lowered Definition IR failed validation.",
        INVALID_SIDECAR: "krs::analysis::invalid-sidecar" => "A sidecar cannot be derived from the lowered Definition IR.",
        UNRESOLVED_REFERENCE: "krs::analysis::unresolved-reference" => "An analysis reference names no declaration.",
        SORT_CYCLE: "krs::analysis::sort-cycle" => "The direct subsort relation contains a cycle.",
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
    /// Diagnostics from KRS rendering, whole-file expansion, and their protocol.
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
        DESCRIPTOR_CAPACITY: "krs::expand::descriptor-capacity" => "A descriptor count or ordinal exceeds its u32 representation.",
        HELPER_PAYLOAD_FORM: "krs::expand::helper-payload-form" => "A helper attribute requires a parenthesized payload.",
        CFG_REPRODUCTION: "krs::expand::cfg-reproduction" => "A cfg attribute could not be reproduced for generated tokens.",
        MISSING_COMPUTATION_CELL: "krs::expand::missing-computation-cell" => "A configuration-owned rule has no computation-cell field.",
        INITIALIZER_BODY_SHAPE: "krs::expand::initializer-body-shape" => "A fixed initializer does not contain exactly one struct expression.",
        MISSING_CHECKED_FIELD: "krs::expand::missing-checked-field" => "A field accepted by syntax validation is absent during rendering.",
        INITIALIZER_CELL_SHAPE: "krs::expand::initializer-cell-shape" => "A nested fixed-cell initializer is not a struct expression.",
        CELL_STATE_FAMILY_MISMATCH: "krs::expand::cell-state-family-mismatch" => "A cell wrapper disagrees with the state family of its initializer or rule.",
        INITIALIZER_RECORD_ARGUMENTS: "krs::expand::initializer-record-arguments" => "An initializer term uses named record arguments.",
        INITIALIZER_WILDCARD: "krs::expand::initializer-wildcard" => "An initializer term contains a wildcard.",
        CLAIM_ONLY_TERM: "krs::expand::claim-only-term" => "A claim-only term island occurs outside a claim.",
        INITIALIZER_FRAGMENT: "krs::expand::initializer-fragment" => "An initializer term uses a fragment instead of constructing nested cells directly.",
        EMPTY_GRAMMAR_DECLARATION: "krs::expand::empty-grammar-declaration" => "A precedence or associativity declaration contains no sentences.",
        UNSUPPORTED_SYMBOL_ITEM: "krs::expand::unsupported-symbol-item" => "A stable-symbol attribute is attached to an unsupported item kind.",
        DUPLICATE_SYMBOL: "krs::expand::duplicate-symbol" => "A declaration contains more than one explicit stable-symbol attribute.",
        SYMBOL_ATTRIBUTE_ORDER: "krs::expand::symbol-attribute-order" => "A stable-symbol attribute does not immediately precede one symbol-bearing declaration attribute.",
        UNKNOWN_HOOK: "krs::expand::unknown-hook" => "A hook path does not name a supported KRS hook operation.",
        FUNCTION_ALIAS_CONFLICT: "krs::expand::function-alias-conflict" => "A function production is also declared as a static alias.",
        INVALID_AVOID_METADATA: "krs::expand::invalid-avoid-metadata" => "An avoid argument explicitly supplies false instead of omitting the metadata.",
        DUPLICATE_STRICTNESS: "krs::expand::duplicate-strictness" => "A constructor declares more than one strictness strategy.",
        ALIAS_MARKER_FORM: "krs::expand::alias-marker-form" => "A constructor alias helper does not use marker syntax.",
        DUPLICATE_ALIAS: "krs::expand::duplicate-alias" => "A constructor declares its alias helper more than once.",
        ORPHAN_HELPER: "krs::expand::orphan-helper" => "A helper attribute is expanded without its required preceding declaration attribute.",
        SORT_PARENT_MISMATCH: "krs::expand::sort-parent-mismatch" => "A reference sort lacks one semantic parent path per Rust marker supertrait.",
        DUPLICATE_MEMBERSHIP_RELATION: "krs::expand::duplicate-membership-relation" => "A readable sort block declares a membership relation more than once.",
        EMPTY_SORT_REGISTRATION: "krs::expand::empty-sort-registration" => "A framework sort block registers no descriptors.",
        EMPTY_SORT_DECLARATION: "krs::expand::empty-sort-declaration" => "A sort declaration contains no descriptor-bearing tokens.",
        EMPTY_SORT_PATH: "krs::expand::empty-sort-path" => "A sort reference contains no path segments.",
        EMPTY_BRACKET: "krs::expand::empty-bracket" => "A bracket template contains no descriptor-bearing tokens.",
        ENUM_VARIANT_COLLISION: "krs::expand::enum-variant-collision" => "Two enum variants have the same readable rule resolution name.",
        RULE_RESULT_WILDCARD: "krs::expand::rule-result-wildcard" => "A rule result contains a wildcard.",
        CLAIM_SUBJECT_ONLY_TERM: "krs::expand::claim-subject-only-term" => "An anonymous term occurrence appears outside a claim subject.",
        CONFIGURATION_SHAPE: "krs::expand::configuration-shape" => "A fixed configuration is not a named-field struct.",
        FRAGMENT_SHAPE: "krs::expand::fragment-shape" => "A fragment payload is not a parent record with named fields.",
        CONTEXT_ALIAS_RESULT_SORT: "krs::expand::context-alias-result-sort" => "A named context alias has a result sort other than the unambiguous `KResult` sort.",
        UNDECLARED_STRICTNESS_FIELD: "krs::expand::undeclared-strictness-field" => "Strictness metadata names a field absent from the rendered declaration.",
        INVALID_ID_TOKEN: "krs::expand::invalid-id-token" => "A builtin Id token is not a dollar-prefixed nonempty ASCII identifier.",
        FACADE_DEPENDENCY: "krs::expand::facade-dependency" => "The invoking crate has no direct dependency on the KRS facade package.",
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
