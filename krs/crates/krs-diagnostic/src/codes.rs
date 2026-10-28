//! Registry of diagnostic codes owned by KRS.

use crate::Code;

/// Who can act on the condition a code describes.
///
/// A KRS code has exactly one kind. A site that reports an author's mistake under an internal code
/// is a bug in that site, fixed by re-coding the site, not by changing the code's kind. A forwarded
/// code's kind is stated where it is forwarded ([`Code::foreign`]): the same native spelling can
/// judge the author's `raw_k!` text or K that KRS lowered, so consumers read a diagnostic's kind,
/// never look its spelling up.
#[derive(
    Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "lowercase")]
pub enum CodeKind {
    /// A property of what the author wrote (source, manifest, command line): some program text,
    /// changed, removes it. KRS's limits and unsupported features are stated as author codes too,
    /// since the author is the one who can act.
    Author,
    /// A broken contract between two KRS components. An author program that reaches it has found
    /// a KRS bug: KRS should have refused the program earlier with an author code, or accepted it.
    Internal,
    /// The world around the program: files, Cargo, the toolchain, a stale build, pins, protocol
    /// versions.
    Environment,
}

/// A registered diagnostic code, its kind and its summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CodeInfo {
    /// Stable code supplied by the producer, with its kind.
    pub code: Code,
    /// One-line explanation of the condition the code describes.
    pub summary: &'static str,
}

/// The registry entry of a KRS code, by its spelling.
#[must_use]
pub fn info(spelling: &str) -> Option<&'static CodeInfo> {
    REGISTRY.iter().find(|info| info.code.as_str() == spelling)
}

macro_rules! code_kind {
    () => {
        crate::codes::CodeKind::Author
    };
    ($kind:ident) => {
        crate::codes::CodeKind::$kind
    };
}

/// Registers each stage's codes. A code is an author code unless its spelling is followed by
/// `[Internal]` or `[Environment]`.
macro_rules! register_codes {
    ($($(#[$stage_doc:meta])* $stage:ident { $($name:ident: $spelling:literal $([$kind:ident])? => $summary:literal,)* })*) => {
        $(
            $(#[$stage_doc])*
            pub mod $stage {
                $(
                    #[doc = $summary]
                    pub const $name: crate::Code =
                        crate::Code::registered($spelling, code_kind!($($kind)?));
                )*

                /// Every diagnostic code registered for this stage.
                pub const CODES: &[crate::Code] = &[$($name,)*];
            }
        )*

        /// Every diagnostic code owned by KRS, its kind and its summary.
        pub const REGISTRY: &[CodeInfo] = &[
            $($(CodeInfo { code: $stage::$name, summary: $summary },)*)*
        ];
    };
}

register_codes! {
    /// Diagnostics from collector planning.
    plan {
        INVALID_METADATA: "krs::plan::invalid-metadata" [Environment] => "Metadata has inconsistent package or resolve records.",
        MISSING_RESOLVE_GRAPH: "krs::plan::missing-resolve-graph" [Internal] => "Full dependency metadata was not supplied.",
        MISSING_PACKAGE: "krs::plan::missing-package" => "A package selector matched nothing.",
        AMBIGUOUS_PACKAGE: "krs::plan::ambiguous-package" => "A name selector matched multiple package IDs.",
        MISSING_KRS_METADATA: "krs::plan::missing-krs-metadata" => "A selected package has no KRS metadata table.",
        MISSING_NAMESPACE: "krs::plan::missing-namespace" => "A selected package has no immutable semantic namespace.",
        MISSING_DEFINITION: "krs::plan::missing-definition" => "A selected facet does not exist.",
        INVALID_DEFINITION: "krs::plan::invalid-definition" => "A selected facet has an invalid metadata shape.",
        MISSING_LIBRARY_TARGET: "krs::plan::missing-library-target" => "A selected semantics package has no linkable Rust library target.",
        AMBIGUOUS_LIBRARY_TARGET: "krs::plan::ambiguous-library-target" => "A selected semantics package has multiple linkable Rust library targets.",
        INVALID_PACKAGE_CONTEXT: "krs::plan::invalid-package-context" [Internal] => "Selected package identity, target, or manifest data is invalid.",
        DUPLICATE_NAMESPACE: "krs::plan::duplicate-namespace" => "Two selected packages declare the same semantic namespace.",
        UNREACHABLE_SELECTION: "krs::plan::unreachable-selection" => "A dependency facet is not in the root Cargo package closure.",
        UNREACHABLE_ENTRYPOINT: "krs::plan::unreachable-entrypoint" [Internal] => "The collector package is not in the root Cargo package closure.",
        DEPENDENCY_CYCLE: "krs::plan::dependency-cycle" [Environment] => "Cargo metadata contains a dependency cycle.",
        INVALID_HOST_TARGET: "krs::plan::invalid-host-target" => "The requested host target is malformed.",
        INVALID_CFG: "krs::plan::invalid-cfg" => "A KRS cfg input is not safe Rust cfg syntax.",
        INVALID_ENTRYPOINT: "krs::plan::invalid-entrypoint" [Internal] => "The collector function path is invalid.",
        INVALID_COLLECTOR_RUNTIME: "krs::plan::invalid-collector-runtime" [Internal] => "A collector runtime manifest path is malformed.",
        INVALID_REGISTRATION_MODE: "krs::plan::invalid-registration-mode" => "The registration mode does not apply to this plan.",
        INVENTORY_FEATURE_ACTIVE: "krs::plan::inventory-feature-active" => "Explicit registration conflicts with the inventory feature.",
        UNREGISTERED_KRS_DEPENDENT: "krs::plan::unregistered-krs-dependent" => "Explicit registration would omit a KRS dependent.",
        REMOVED_FACET_KEY: "krs::plan::removed-facet-key" => "A definition facet uses the removed `root` or `syntax-root` key.",
        INVALID_INT_LITERALS: "krs::plan::invalid-int-literals" => "The package `int-literals` metadata is not \"signed\" or \"unsigned\".",
        INVALID_RAW_K_METADATA: "krs::plan::invalid-raw-k-metadata" => "The package `allow-raw-k` metadata is not a boolean, or `profile` is not \"standard\" or \"strict\".",
    }
    /// Diagnostics from canonical K emission.
    emit {
        UNSUPPORTED_SHAPE: "krs::emit::unsupported-shape" [Internal] => "Canonical-source emission does not support a Definition IR shape.",
        INVALID_REFERENCE: "krs::emit::invalid-reference" [Internal] => "A Definition symbol reference was absent or had the wrong role.",
        DUPLICATE_GENERATED_RANGE: "krs::emit::duplicate-generated-range" [Internal] => "Rendered nodes attempted to own the same generated source range.",
        INVALID_SIDECAR: "krs::emit::invalid-sidecar" [Internal] => "An emitted sidecar invariant failed.",
        TRUSTED_CLAIM: "krs::emit::trusted-claim" => "A `trusted` claim is assumed without proof; every Haskell build and every prove run reports it.",
        SMT_ONLY_FUNCTION: "krs::emit::smt-only-function" => "A function with an `smt_hook` has no equation: Z3 evaluates it on symbolic paths, and concrete execution cannot.",
    }
    /// Diagnostics from collector package generation.
    generate {
        INVALID_PLAN: "krs::generate::invalid-plan" [Internal] => "The collector plan contains an unusable Cargo manifest path.",
        SERIALIZATION: "krs::generate::serialization" [Internal] => "Canonical selection serialization failed.",
        UNSAFE_OUTPUT: "krs::generate::unsafe-output" => "The output directory does not belong to KRS.",
        IO: "krs::generate::io" [Environment] => "A generated collector filesystem operation failed.",
    }
    /// Diagnostics from reference Rust projection.
    reference {
        SOURCE_SELECTION: "krs::reference::source-selection" => "The package descriptors do not select exactly one source file.",
        SOURCE_MODULES: "krs::reference::source-modules" => "The selected source contains descriptors from multiple Rust modules.",
        SOURCE_MANIFEST_DIRECTORY: "krs::reference::source-manifest-directory" [Environment] => "The package manifest has no parent directory.",
        SOURCE_READ: "krs::reference::source-read" [Environment] => "The selected source file could not be read.",
        SOURCE_CHANGED: "krs::reference::source-changed" [Environment] => "The selected source changed after collection.",
        SOURCE_ENCODING: "krs::reference::source-encoding" => "The selected source file is not UTF-8.",
        RUST_SYNTAX: "krs::reference::rust-syntax" => "The selected source is not valid Rust.",
        GENERATED_RUST: "krs::reference::generated-rust" [Internal] => "The generated reference Rust failed to parse.",
        DUPLICATE_RULE: "krs::reference::duplicate-rule" => "A rule name occurs in multiple readable tables.",
        RULE_COVERAGE: "krs::reference::rule-coverage" [Internal] => "A readable rule does not map to exactly one collected head rule.",
        CONSTRUCTOR_COVERAGE: "krs::reference::constructor-coverage" [Internal] => "An enum variant does not map to exactly one constructor.",
        CONSTRUCTOR_FIELD_COVERAGE: "krs::reference::constructor-field-coverage" [Internal] => "Projected fields do not cover the collected constructor.",
        MISSING_CONSTRUCTOR_FIELD: "krs::reference::missing-constructor-field" [Internal] => "A projected field is absent from the collected constructor.",
        MISSING_SEMANTIC_RULE: "krs::reference::missing-semantic-rule" [Internal] => "Semantic lowering omitted a collected rule.",
        MISSING_BINDING_SORT: "krs::reference::missing-binding-sort" [Internal] => "Inference produced no sort for a readable binder.",
        EXTERNAL_DECLARATION: "krs::reference::external-declaration" => "A dependency alias cannot be reconstructed.",
        EXTERNAL_REFERENCE_SORT: "krs::reference::external-reference-sort" => "A constructor field marker path is external.",
        MIXED_APPLICATION_ARGUMENTS: "krs::reference::mixed-application-arguments" => "An application mixes positional and named arguments.",
        NAMED_BUILTIN_APPLICATION: "krs::reference::named-builtin-application" => "A builtin operation uses named arguments.",
        MISSING_DECLARATION: "krs::reference::missing-declaration" [Internal] => "A referenced declaration is absent from the collected bundle.",
        NAMED_NON_CONSTRUCTOR: "krs::reference::named-non-constructor" => "A named application does not reference a constructor.",
        DUPLICATE_APPLICATION_FIELD: "krs::reference::duplicate-application-field" => "A named constructor field occurs more than once.",
        MISSING_APPLICATION_FIELD: "krs::reference::missing-application-field" => "A constructor result omits a required named field.",
        UNKNOWN_APPLICATION_FIELD: "krs::reference::unknown-application-field" => "A named argument does not belong to its constructor.",
        INVALID_LITERAL: "krs::reference::invalid-literal" [Internal] => "A canonical integer payload is not valid Rust tokens.",
        UNSUPPORTED_BUILTIN_TOKEN: "krs::reference::unsupported-builtin-token" => "A builtin token sort has no reference spelling.",
        UNSUPPORTED_STATE: "krs::reference::unsupported-state" => "A readable optional or collection entry has a shape with no reference spelling.",
        UNRESOLVED_OPERATOR: "krs::reference::unresolved-operator" [Internal] => "Semantic lowering recorded no builtin operation for an operator the reference projection renders.",
        UNRESOLVED_LIST_NOTATION: "krs::reference::unresolved-list-notation" [Internal] => "Semantic lowering recorded no constructor for bracket list notation the reference projection renders.",
    }
    /// Diagnostics from native Definition compilation.
    native {
        ADAPTER_MISSING_SYMBOL: "krs::native::adapter-missing-symbol" [Internal] => "A symbol is absent from the native adapter index.",
        ADAPTER_MISSING_REFERENCE: "krs::native::adapter-missing-reference" [Internal] => "A nominal reference is absent from the native adapter index.",
        ADAPTER_EMPTY_GROUP: "krs::native::adapter-empty-group" [Internal] => "A precedence or associativity sentence names a production group with no labelled member.",
        ADAPTER_TOKEN_GUARD: "krs::native::adapter-token-guard" => "A token regex carries a precede or follow guard, which k-rust does not read.",
        DUPLICATE_SENTENCE_MAPPING: "krs::native::duplicate-sentence-mapping" [Internal] => "Native provenance maps a sentence more than once.",
        MISSING_SENTENCE_MAPPING: "krs::native::missing-sentence-mapping" [Internal] => "Native provenance has no mapping for an input address.",
        LOSSY_COMPILE_ADDRESS: "krs::native::lossy-compile-address" [Internal] => "A compile address cannot map to a KRS sentence.",
        INDEX_OUT_OF_RANGE: "krs::native::index-out-of-range" [Internal] => "A native input address is outside its module.",
        KIND_MISMATCH: "krs::native::kind-mismatch" [Internal] => "The native source kind differs from the IR sentence.",
        MISSING_KIND: "krs::native::missing-kind" [Internal] => "Native provenance lacks a kind for an input address.",
        INVALID_IDENTITY: "krs::native::invalid-identity" [Internal] => "A native identity has an invalid author relation.",
        MISSING_PRELUDE: "krs::native::missing-prelude" [Internal] => "The pinned structured-loader prelude is unavailable.",
        PREPARATION: "krs::native::preparation" => "The native loader rejected the definition.",
        COMPILE: "krs::native::compile" => "A native frontend stage rejected the definition.",
        KORE_REPARSE: "krs::native::kore-reparse" [Internal] => "A produced KORE artifact failed to reparse under the pin.",
        RAW_K_PARSE: "krs::native::raw-k-parse" => "The pinned K parser rejected the text of a `raw_k!` sentence.",
    }
    /// Diagnostics from host descriptor collection.
    collect {
        INVALID_PACKAGE_CONTEXT: "krs::collect::invalid-package-context" [Internal] => "Caller-supplied package metadata was invalid.",
        HOST_IO: "krs::collect::host-io" [Environment] => "A host path could not be canonicalized or read.",
        DUPLICATE_PACKAGE_CONTEXT: "krs::collect::duplicate-package-context" [Internal] => "More than one context claimed the same host package lookup key.",
        DUPLICATE_KNAMESPACE: "krs::collect::duplicate-knamespace" => "More than one package claimed the same immutable K namespace.",
        UNSUPPORTED_SCHEMA_VERSION: "krs::collect::unsupported-schema-version" [Environment] => "A descriptor carried a schema version other than the current one.",
        INVALID_BUILTIN_REGISTRY: "krs::collect::invalid-builtin-registry" [Internal] => "The compiler-provided builtin marker catalog was incomplete or ambiguous.",
        PACKAGE_NOT_SELECTED: "krs::collect::package-not-selected" => "No selected Cargo package matched a descriptor's host lookup key.",
        CRATE_ROOT_MISMATCH: "krs::collect::crate-root-mismatch" [Internal] => "The first `module_path!()` segment did not match the selected target.",
        INVALID_STABLE_IDENTITY: "krs::collect::invalid-stable-identity" [Internal] => "A host item could not become a stable item identity.",
        DUPLICATE_ITEM_ID: "krs::collect::duplicate-item-id" => "Two declarations produced the same final stable identity.",
        ITEM_KIND_MISMATCH: "krs::collect::item-kind-mismatch" [Internal] => "A descriptor payload did not agree with its declared item kind.",
        DUPLICATE_TYPE_DECLARATION: "krs::collect::duplicate-type-declaration" [Internal] => "Two declarations exposed the same build-local Rust `TypeId`.",
        DECLARATION_BUILTIN_COLLISION: "krs::collect::declaration-builtin-collision" [Internal] => "A Rust identity was assigned to both an authored declaration and a builtin.",
        MISSING_TYPE_DECLARATION: "krs::collect::missing-type-declaration" [Internal] => "A sort or constructor declaration exposed no build-local Rust `TypeId`.",
        UNRESOLVED_TYPE_REFERENCE: "krs::collect::unresolved-type-reference" => "A Rust type reference had no declaration in the selected collection.",
        REFERENCE_KIND_MISMATCH: "krs::collect::reference-kind-mismatch" => "A resolved declaration had the wrong semantic item kind.",
        INVALID_CONFIGURATION: "krs::collect::invalid-configuration" => "A configuration, cell, or configuration-rule entry is not one its declaration admits.",
        INVALID_DISPLAY_FILE: "krs::collect::invalid-display-file" [Internal] => "A display filename was not a normalized relative source hint.",
        SOURCE_OUTSIDE_PACKAGE: "krs::collect::source-outside-package" => "A KRS item's source resolves outside its Cargo package directory, such as generated code included from `OUT_DIR`.",
        AMBIGUOUS_SOURCE_PATH: "krs::collect::ambiguous-source-path" [Environment] => "A display hint resolved to multiple distinct files in the package.",
        SOURCE_POSITION_OUT_OF_BOUNDS: "krs::collect::source-position-out-of-bounds" [Environment] => "A line or Unicode-scalar column was outside the exact source revision.",
        IMPRECISE_AUTHORED_ANCHOR: "krs::collect::imprecise-authored-anchor" [Internal] => "A semantic node used an invocation-fallback rather than exact leaves.",
        SOURCE_SYNTAX: "krs::collect::source-syntax" [Environment] => "The exact source no longer parses under the shared KRS parser.",
        UNRESOLVED_ATTRIBUTE: "krs::collect::unresolved-attribute" => "An authored attribute or item macro names a KRS entry point but does not invoke it under the package's facade alias.",
        FACADE_ATTRIBUTE_ON_MACRO: "krs::collect::facade-attribute-on-macro" => "A facade attribute annotates a macro instead of the item it names.",
        STALE_ANCHOR: "krs::collect::stale-anchor" [Environment] => "A host anchor did not match the corresponding reparsed semantic node.",
        AMBIGUOUS_ANCHOR: "krs::collect::ambiguous-anchor" [Internal] => "More than one reparsed invocation matched a host descriptor.",
        PROVENANCE_MISMATCH: "krs::collect::provenance-mismatch" [Internal] => "The macro and shared parser disagreed about the complete anchor set.",
    }
    /// Diagnostics from semantic analysis and definition lowering.
    analysis {
        BUILTIN_SORT_NAME_COLLISION: "krs::analysis::builtin-sort-name-collision" => "An authored sort uses a compiler builtin sort name.",
        CONFIGURATION_COUNT: "krs::analysis::configuration-count" => "The selected descriptors do not contain exactly one configuration.",
        DANGLING_REFERENCE: "krs::analysis::dangling-reference" [Internal] => "A descriptor reference names no selected declaration.",
        REFERENCE_KIND_MISMATCH: "krs::analysis::reference-kind-mismatch" [Internal] => "A declaration reference uses the wrong namespace.",
        PARSER_REFERENCE_DISAGREEMENT: "krs::analysis::parser-reference-disagreement" [Internal] => "Parser-owned origins or references disagree with a descriptor.",
        INVALID_TERM: "krs::analysis::invalid-term" => "A term does not fit its position: its sort, arity, or fields disagree with what the position admits.",
        UNSUPPORTED_SHAPE: "krs::analysis::unsupported-shape" [Internal] => "A semantic shape is outside the supported lowering subset.",
        INVALID_GENERATED_IDENTITY: "krs::analysis::invalid-generated-identity" [Internal] => "A generated IR identity is invalid.",
        INVALID_SEMANTIC_THEORY: "krs::analysis::invalid-semantic-theory" [Internal] => "Whole-theory semantic validation failed.",
        INVALID_PRODUCTION_TEMPLATE: "krs::analysis::invalid-production-template" => "Authored syntax cannot be represented by a production template.",
        INVALID_EMITTED_NAME: "krs::analysis::invalid-emitted-name" => "An emitted name is not canonical K syntax.",
        SOURCE_MAP_COLLISION: "krs::analysis::source-map-collision" [Internal] => "Generated Definition nodes use the same source-map key.",
        INVALID_DEFINITION: "krs::analysis::invalid-definition" [Internal] => "The lowered Definition IR failed validation.",
        INVALID_SIDECAR: "krs::analysis::invalid-sidecar" [Internal] => "A sidecar cannot be derived from the lowered Definition IR.",
        UNRESOLVED_REFERENCE: "krs::analysis::unresolved-reference" [Internal] => "An analysis reference names no declaration.",
        SORT_CYCLE: "krs::analysis::sort-cycle" => "The direct subsort relation contains a cycle.",
        OVERLAPPING_RULE_HEADS: "krs::analysis::overlapping-rule-heads" => "Two rules have overlapping application heads.",
        OVERLAPPING_EQUATIONS: "krs::analysis::overlapping-equations" => "Two equations of one function at one priority apply to one argument and give it different results, so the definition would state that the results are equal.",
        OVERLAPPING_MATCH_ARMS: "krs::analysis::overlapping-match-arms" => "Two arms of a function body's `match` apply to one argument and give it different results; each arm is an unordered equation, so the arms must not overlap.",
        AMBIGUOUS_OPERATOR: "krs::analysis::ambiguous-operator" => "The sorts of an operator's operands (`a + b`, `a == b`) choose no builtin domain, or choose two, so it denotes no one builtin operation.",
        INVALID_LIST_NOTATION: "krs::analysis::invalid-list-notation" => "Bracket list notation (`[a, ..rest]`, `[]`) stands at a position whose sort is neither the builtin `List` nor a cons list, takes a cons list's elements from its back (`[.., x]`), or a readable record's bracketed value names a cell that is neither the computation cell, a List collection, nor a cell of a list sort.",
        AMBIGUOUS_LIST_PATTERN: "krs::analysis::ambiguous-list-pattern" => "A builtin `List` pattern of a rule, equation, or simplification holds two or more parts that are not single elements (`Left ListItem(V) Right`), so it matches some lists in several ways.",
        INVALID_CONS_LIST: "krs::analysis::invalid-cons-list" => "A `#[k::cons_list]` enum's two-field constructor does not take the enum's own sort as its second field, or two cons-list declarations construct one sort.",
        AMBIGUOUS_OR_PATTERN: "krs::analysis::ambiguous-or-pattern" => "Two alternatives of one `A | B` or-pattern can match the same term with different bindings.",
        NONDET_GROUP: "krs::analysis::nondet-group" => "A `nondet` group has one rule, mixes priorities, or names a rule that overlaps no other rule of the group.",
        SYMBOL_NAME_COLLISION: "krs::analysis::symbol-name-collision" => "Two declarations have the same emitted symbol name, or a production's symbol is one K generates.",
        NAME_COLLISION: "krs::analysis::name-collision" => "Two declarations have the same name in a lowering namespace.",
        INVALID_OVERLOAD: "krs::analysis::invalid-overload" => "An `overload` key does not name a constructor production that its member specialises.",
        MISSING_PRECEDENCE_CHAIN: "krs::analysis::missing-precedence-chain" => "A constructor family without `#[k::precedence]` has a variant that can sit directly at the edge of another of its variants.",
        PRIVATE_PRODUCTION_IN_SPEC: "krs::analysis::private-production-in-spec" => "A claim or a spec-module sentence names a private production, which proof modules cannot see.",
        ALWAYS_ENABLED_RULE: "krs::analysis::always-enabled-rule" => "A rule without the computation cell matches every configuration, so execution never terminates.",
        RULE_CHANGES_NO_CELL: "krs::analysis::rule-changes-no-cell" => "A rule without the computation cell changes no cell.",
        GROUP_AND_DESCENDANT: "krs::analysis::group-and-descendant" => "A rule selects a nested cell together with a cell inside it.",
        AMBIGUOUS_CELL_SORT: "krs::analysis::ambiguous-cell-sort" => "One cell declaration is the content of two cell fields, so its K cell sort is ambiguous.",
        INVALID_TOKEN_SORT: "krs::analysis::invalid-token-sort" => "A token sort has constructors or a repeated token, a token alias names a sort that cannot take tokens, a program production needs a token sort whose tokens are all private, or `k::lexeme!` names a sort that is not a token sort.",
        TOKEN_COLLISION: "krs::analysis::token-collision" => "A token regex is one of K's own token regexes at another precedence, or at precedence high enough to lex a configuration cell name or cell property as its own token.",
        DUPLICATE_LEXICAL: "krs::analysis::duplicate-lexical" => "A `k::lexical!` name is declared more than once in the definition.",
        UNDEFINED_LEXICAL: "krs::analysis::undefined-lexical" => "A token, layout, or lexical regex refers to a `{Name}` that no `k::lexical!` declares.",
        RECURSIVE_LEXICAL: "krs::analysis::recursive-lexical" => "Lexicals refer to each other, directly or through other lexicals, in a cycle.",
        INVALID_SYNTAX_LIST: "krs::analysis::invalid-syntax-list" => "A `#[k::syntax_list]` sort has an element of its own sort, another constructor or subsort, or a terminator `.Sort` that another terminal already spells.",
        CONSOLE_CELL: "krs::analysis::console-cell" => "A stream or exit cell does not have the shape K requires.",
        FRESH_BINDER_POSITION: "krs::analysis::fresh-binder-position" => "A `#[k::fresh]` binder occurs in the pattern or `requires`, shadows a pattern binding, or is unused; a fresh value exists only once the step happens.",
        NO_FRESH_GENERATOR: "krs::analysis::no-fresh-generator" => "A `#[k::fresh]` binder has a sort without a `fresh_generator` function (Int and Id have K's own).",
        DUPLICATE_FRESH_GENERATOR: "krs::analysis::duplicate-fresh-generator" => "A sort has more than one `fresh_generator` function.",
        DUPLICATE_SMTLIB: "krs::analysis::duplicate-smtlib" => "Two functions declare the same `smtlib` symbol, so Z3 would identify them.",
        INVALID_MATCH_RESTRICTION: "krs::analysis::invalid-match-restriction" => "A `concrete` or `symbolic` key of an equation or simplification names no left-hand binder, restricts one binder both ways, is bare on both keys, or is on an equation whose function's other equations lack it.",
        INVALID_STATIC_CLAUSE: "krs::analysis::invalid-static-clause" => "An alias or desugar clause expands a production that is not marked with the same mode (`#[k::alias]` or `#[k::desugar]`), or an alias or desugar production has no clause that expands it.",
        INVALID_CONSTANT: "krs::analysis::invalid-constant" => "A `#[k::constant]` value applies a function or builtin operation, so it is no ground constructor term; constants refer to each other in a cycle; or a use of a constant passes it arguments.",
        SMT_LEMMA_UNTRANSLATABLE: "krs::analysis::smt-lemma-untranslatable" => "An `smt_lemma` equation or simplification mentions a function Z3 cannot see: a user function without `smtlib` or `smt_hook`, or a builtin without an SMT translation.",
        INVALID_FRESH_GENERATOR: "krs::analysis::invalid-fresh-generator" => "A `fresh_generator` function is not total, does not take exactly one Int argument, or does not return the sort it generates.",
        RAW_K: "krs::semantic::raw-k" => "A `raw_k!` sentence is unchecked K text: a warning in a package that allows raw K, otherwise an error.",
        FUNCTION_IN_PATTERN: "krs::analysis::function-in-pattern" => "A rule's or an equation's pattern applies a function where it matches a term, at a slot's root as below it, other than at the root of an equation's subject (the function it defines) or in a collection's key, value or element: the terms a rule or an equation applies to have their functions evaluated, so the pattern describes a term that never occurs.",
        SUBJECT_ROOT_NOT_FUNCTION: "krs::analysis::subject-root-not-function" => "An equation's subject is not the application of a function the definition declares, or a simplification's is not the application of a declared or builtin function: an equation states the value of the function it defines, and a simplification rewrites an unevaluated application, so a constructor, a literal, or another value at the root defines or simplifies nothing.",
        INVALID_SORT_TEST: "krs::analysis::invalid-sort-test" => "A `k::is!` or `k::project!` term occurs in a left-hand side or pattern, or projects into `K`.",
        BIT_TEMPLATE_SORT: "krs::analysis::bit-template-sort" => "A `k::bits!` template, which matches an `Int`, stands at a position whose sort is neither `Int` nor a sort above it.",
        TRIVIAL_SORT_TEST: "krs::analysis::trivial-sort-test" => "A `k::project!` term projects to a supersort of its operand's sort, or `k::is!(K, ..)` is always true.",
        INCOMPATIBLE_BINDER: "krs::analysis::incompatible-binder" => "A typed binder's declared sort is not a subsort of the sort one of its occurrences needs.",
        INVALID_SPEC_MODULE: "krs::analysis::invalid-spec-module" => "An author spec module breaks a K proof-module rule: it holds something other than claims, simplification lemmas, and tokens for existing sorts, holds an `smt_lemma` lemma, nests, has an import cycle or an import that resolves to no module, does not import the definition, reuses a module name, or names an `Id` its grammar cannot lex.",
        INVALID_RECORD_UPDATE: "krs::analysis::invalid-record-update" => "A record update `Ctor { f: e, ..t }` has a base that is not the alias `t @ Ctor { .. }` of one record of the same constructor or cell in the left-hand side, or stands where a reference `cells!` term must name every field.",
        INVALID_PATTERN_AS: "krs::analysis::invalid-pattern-as" => "A `name @ pattern`'s (K's `#as`) alias needs a sort its pattern does not have.",
        INVALID_PATTERN_OR: "krs::analysis::invalid-pattern-or" => "An `A | B` or-pattern (K's `#Or`) binds a name at different sorts in its alternatives, has no least common sort, stands in a simplification's left-hand side, which is matched as one term, joins whole group cells, which are placed by their labels, or joins whole equation subjects that no one equation matches: alternatives that apply different functions or differ in more than one argument.",
        INVALID_MATCHES: "krs::analysis::invalid-matches" => "A `k::matches!` (K's `:=K`) pattern name shadows a rule binder or is never read, or its pattern's sort cannot meet its subject's sort.",
        INVALID_LET: "krs::analysis::invalid-let" => "A `let` statement's (K's `#let`) pattern sort cannot meet its value's sort, or its names have no single sort.",
        INVALID_FUNCTION_CONTEXT: "krs::analysis::invalid-function-context" => "An equation's function context (K's `[[ .. ]]`) reads a whole nested cell, or declares a binder at a sort its cell does not have.",
        INVALID_PARAMETRIC_PRODUCTION: "krs::analysis::invalid-parametric-production" => "A parametric production (K's `syntax {S}`) names a parameter like a sort, carries strictness, an alias, a hook, a token, or a bracket, or is a constructor whose result parameter would be instantiated at a sort with domain values.",
        PARAMETRIC_INSTANCE: "krs::analysis::parametric-instance" => "A parametric production's instance is missing, disagrees with the head's declared sort or its arguments, or cannot be determined from the arguments and position.",
        NATIVE_INSTANCE: "krs::analysis::native-instance" => "The least instance K and k-rust solve from an equation or rule head's argument sorts differs from its turbofish, so the head would not be the equation the author wrote.",
        ML_PLACEMENT: "krs::analysis::ml-placement" => "A matching-logic predicate (`k::ml`) occurs in the condition of a transition or equation; predicates are allowed on claims and simplifications.",
        INVALID_ML_PREDICATE: "krs::analysis::invalid-ml-predicate" => "A matching-logic predicate (`k::ml`) is an operand of an object function, a Bool term stands where a predicate is expected, `ml::equals` operands share no sort, a predicate simplification's left side is not rooted at `ml::equals` or `ml::ceil`, a connective has the wrong arity, or an `ml::exists` binder shadows a rule binder.",
        INVALID_LOCAL_REWRITE: "krs::analysis::invalid-local-rewrite" => "A single-body rule (`k::rewrite!`) changes no cell, or a rewrite side has no sort both images admit.",
        INVALID_HEAT_COOL: "krs::analysis::invalid-heat-cool" => "A heat or cool rule's `hole = x` binder does not occur on its left side, or occurs there more than once.",
        INVALID_CONTEXT: "krs::analysis::invalid-context" => "A context's `hole = x` binder is absent, bound twice, or outside the computation cell, or its rewrite is not `HOLE => term-containing-HOLE`; or a context alias's HERE is outside the computation cell.",
        OPTIONAL_PRESENCE: "krs::analysis::optional-presence" => "An optional (`?`) cell is written without `Some`/`None`, a `Some`/`None` entry names a cell that is not optional, or a rule tests absence other than by creating the cell (`None => Some(..)`).",
        COMPUTATION_CELL: "krs::analysis::computation-cell" => "A rule completed at the head of the computation needs a configuration with exactly one top-level `KSequence` cell.",
        CELL_WRAPPER: "krs::analysis::cell-wrapper" => "A configuration entry's wrapper is not its cell's: `KCell(..)` or a bracketed sequence for the computation cell, `Cell(..)` for a leaf, none for a group, written on another kind of cell.",
        UNUSED_CONFIGURATION_VARIABLE: "krs::analysis::unused-configuration-variable" => "A `#[k::config_var]` initializer parameter is read by no cell's initial content, so its input would have nowhere to go.",
        UNKNOWN_INSTANCE_LABEL: "krs::analysis::unknown-instance-label" => "A result instance updates `..label` without a subject instance `label`, or two result instances update the same label.",
        MAP_COLLECTION_KEY: "krs::analysis::map-collection-key" => "A created instance of a Map cell collection does not state its key (the first child), or an update changes the key.",
        NO_CELL_DEFAULT: "krs::analysis::no-cell-default" => "A created instance's `..` defaults a child whose template reads a configuration variable, so K has no default for it.",
        IMPLICIT_AND_EXPLICIT_INSTANCES: "krs::analysis::implicit-and-explicit-instances" => "A rule names a cell collection's instances and also a cell inside it as the collection's implicit single instance.",
        COLLECTION_ENTRY: "krs::analysis::collection-entry" => "A collection entry is braced for a List collection or bracketed for a Set or Map collection, names a cell that is not a collection or a child its instance does not declare, or has a shape K cannot express.",
        UNCOVERED_TOTAL_FUNCTION: "krs::analysis::uncovered-total-function" => "A `total` function has arguments that no equation defines, so the function's value there is unconstrained.",
        STALE_UNDERSPECIFIED: "krs::analysis::stale-underspecified" => "A function states `underspecified`, but its equations define every argument.",
        COLLECTION_CONFIG_VAR_WITHOUT_INITIAL: "krs::analysis::collection-config-var-without-initial" => "An optional or collection cell's template reads a configuration variable, so the cell starts present, but the cell is not `initial`.",
        COLLECTION_ELEMENT_SORT: "krs::analysis::collection-element-sort" => "A term written into a typed collection (`Map<K, V>`, `List<T>`, `Set<T>`) has a key, value, or element of another sort, a typed collection flows into one whose element types it does not fit, a read asks for a sort the collection never holds, or a collection type has the wrong number of arguments.",
        UNTYPED_COLLECTION: "krs::analysis::untyped-collection" => "A collection whose element types nothing declares (a bare `Map`, `List`, or `Set` cell, constructor field, or function result, or a binder matched in one) is written into a typed collection, where nothing could check its elements.",
        COLLECTION_SIBLINGS: "krs::analysis::collection-siblings" => "A `multiplicity = \"*\"` collection cell shares its parent with other cells; K requires it to be the parent's only child.",
    }
    /// Diagnostics forwarded from Rust expansion without a rustc-owned code.
    rust_expansion {
        UNCODED_ERROR: "krs::rust-expansion::uncoded-error" => "Rust expansion reported an error without a diagnostic code.",
    }
    /// Diagnostics from the program-syntax partition of each package.
    partition {
        NOT_PROGRAM_SYNTAX: "krs::partition::not-program-syntax" => "A production marked `program` cannot be program syntax and is placed in the semantics module.",
        MIXED_GROUP: "krs::partition::mixed-group" => "A precedence or associativity group mixes `internal` and program-syntax productions.",
        SIGNED_INTEGER_LEAK: "krs::partition::signed-integer-leak" => "An unsigned package's program syntax imports a signed package's program syntax.",
        CONFIGURATION_VISIBILITY: "krs::partition::configuration-visibility" => "A dependency package's rules need the configuration, but the configuration names a symbol its own module cannot import.",
    }
    /// Diagnostics from the backend capability table (V8).
    capability {
        UNAVAILABLE: "krs::capability::unavailable" => "A backend route lacks a feature the definition needs; `build` and the run commands refuse the definition before compiling it, and `check` warns.",
        IGNORED_ENSURES: "krs::capability::ignored-ensures" => "A transition has an `ensures` condition, which concrete (LLVM) execution ignores.",
    }
    /// Diagnostics from Rust token parsing and KRS syntax validation.
    syntax {
        RESERVED_BINDER: "krs::syntax::reserved-binder" => "An authored binder contains the marker reserved for generated identifiers.",
        RUST_SYNTAX: "krs::syntax::rust-syntax" => "Rust token parsing failed before KRS shape validation could finish.",
        UNEXPECTED_ATTRIBUTE_PAYLOAD: "krs::syntax::unexpected-attribute-payload" => "An attribute which takes no arguments received a payload.",
        UNKNOWN_ARGUMENT: "krs::syntax::unknown-argument" => "A keyed attribute argument is not part of the attribute grammar.",
        DUPLICATE_ARGUMENT: "krs::syntax::duplicate-argument" => "A keyed attribute argument occurred more than once.",
        MISSING_ARGUMENT: "krs::syntax::missing-argument" => "A required keyed attribute argument was absent.",
        MISSING_FUNCTION_SYNTAX: "krs::syntax::missing-function-syntax" => "A `#[k::function]` that is program syntax (`pub` and not `internal`) omitted `syntax`; only a production that is not program syntax gets the default `symbol({field}, ..)`.",
        INVALID_FUNCTION_SHORTHAND: "krs::syntax::invalid-function-shorthand" => "A `#[k::function]` on a `fn` was malformed: its name is not in upper camel case, a parameter is not `name: k::Term<S>`, it is generic or async, has a `sort` key, a `hook` with a body, a body that is not one term, or `#[k::requires]` without a body.",
        INVALID_CONSTANT: "krs::syntax::invalid-constant" => "A `#[k::constant]` item was malformed: not a `const` item (a `static`, or generic), its type is not a KRS sort, or its value is not a ground constructor term (a literal, a constructor application of ground terms, or another constant).",
        INVALID_EQUATION_TABLE: "krs::syntax::invalid-equation-table" => "A `k::equations!` table was malformed: a missing `for Function;` header or one that names no non-parametric `#[k::function]`, no row, a repeated or missing row label, a row attribute other than `#[k::equation(..)]`, `#[k::requires(..)]`, or documentation, or arguments that are not one pattern or a parenthesized list.",
        DUPLICATE_EQUATION_ROW: "krs::syntax::duplicate-equation-row" => "Two unguarded rows of one `k::equations!` table at one priority have the same literal arguments: the definition would state one application equals both results, or one row is redundant.",
        CATCH_ALL_EQUATION_ROW: "krs::syntax::catch-all-equation-row" => "An unguarded `k::equations!` row whose arguments are all wildcards shares its priority with another row, so it overlaps every row; equations are unordered, so mark it `#[k::equation(owise)]`.",
        INVALID_BIT_TEMPLATE: "krs::syntax::invalid-bit-template" => "A `k::bits!` template was malformed: not one string literal, no bit, a character other than `0`, `1`, `_`, a lowercase field letter, or a space, more than 128 bits, or a field whose bits are not adjacent.",
        BIT_TEMPLATE_POSITION: "krs::syntax::bit-template-position" => "A `k::bits!` template was outside an `Int` argument of a rule's or equation's left-hand side: in a result, a guard, a cell pattern, a context, or an alternative of `|`, or it needs a name (`op @ k::bits!(..)`) to appear in a binder list.",
        BIT_FIELD_COLLISION: "krs::syntax::bit-field-collision" => "A `k::bits!` field letter is also a binder of its sentence, a field of another template, or a name a `let` or `k::matches!` binds again; a field names part of the matched value, so it needs its own name.",
        BIT_TEMPLATE_WIDTH_MISMATCH: "krs::syntax::bit-template-width-mismatch" => "Two rows of one `k::equations!` table match one argument with templates of different widths; a template's width is part of its meaning (it matches only `0 <= n < 2^width`), so a different width is most likely a missing or extra bit.",
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
        INVALID_COLOR: "krs::syntax::invalid-color" => "Production colour metadata was malformed or does not match the printed terminals.",
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
        INVALID_TRIVIA: "krs::syntax::invalid-trivia" [Internal] => "Source trivia could not be classified against the token byte ranges.",
        UNSUPPORTED_DSL_BLOCK_COMMENT: "krs::syntax::unsupported-dsl-block-comment" => "A non-documentation block comment occurred in a line-comment-only DSL body.",
        UNSUPPORTED_RULE_SIGNATURE: "krs::syntax::unsupported-rule-signature" => "A rule function used a signature feature outside the one-clause rule ABI.",
        UNSUPPORTED_RULE_PATTERN: "krs::syntax::unsupported-rule-pattern" => "A rule subject was not a supported named-constructor pattern.",
        INVALID_TERM_TYPE: "krs::syntax::invalid-term-type" => "A symbolic constructor field or rule type was not a supported `Term` sort.",
        PARAMETRIC_COLLECTION_SORT: "krs::syntax::parametric-collection-sort" => "A rule narrowing or a rule binder's, equation's, or constant's sort gave K's `List`, `Map`, or `Set` sort element types, which only a cell, a constructor field, or a function signature declares.",
        INVALID_COLLECTION_ARGUMENT: "krs::syntax::invalid-collection-argument" => "An element type of a typed collection in a constructor field or function signature was neither a sort nor a collection type.",
        UNSUPPORTED_RULE_BODY: "krs::syntax::unsupported-rule-body" => "A rule body was not exactly one unterminated term expression.",
        UNEXPECTED_MACRO: "krs::syntax::unexpected-macro" => "A macro in a rule subject or result was not the reserved `term!` form.",
        UNSUPPORTED_TERM_EXPRESSION: "krs::syntax::unsupported-term-expression" => "A Rust expression is outside the closed named-term grammar.",
        INVALID_RECORD_UPDATE: "krs::syntax::invalid-record-update" => "A record update `Ctor { f: e, ..t }` has a base that is not one binder, names a field twice, or stands in a pattern.",
        INVALID_PATTERN_AS: "krs::syntax::invalid-pattern-as" => "A `name @ pattern` (K's `#as`) is malformed or occurs outside a left-hand side.",
        INVALID_PATTERN_OR: "krs::syntax::invalid-pattern-or" => "An `A | B` or-pattern (K's `#Or`) is malformed, binds different names in its alternatives, or joins whole machine records or remainders.",
        INVALID_MATCHES: "krs::syntax::invalid-matches" => "A `k::matches!` (K's `:=K`) is malformed, has an `if` guard, or is written as std's bare `matches!`.",
        INVALID_LET: "krs::syntax::invalid-let" => "A term block is not `let pattern = term;` statements followed by one result term (K's `#let`), its sort ascription is not one binder at a plain sort, or its pattern has alternatives or an alias.",
        INVALID_FUNCTION_CONTEXT: "krs::syntax::invalid-function-context" => "A function context (K's `[[ .. ]]` configuration context) is not a final `k::cells! { .., .. }` parameter of an `#[k::equation]` typed by the configuration struct and framed by an anonymous `..`.",
        INVALID_LOCAL_REWRITE: "krs::syntax::invalid-local-rewrite" => "A `k::rewrite!` (K's local `=>`) occurs outside the subject of a single-body `#[k::rule]` fn, inside another rewrite, in a map key, or with a right-side name the left image does not bind, or a single-body rule has no rewrite.",
        MISSING_TOKEN_ENDPOINT: "krs::syntax::missing-token-endpoint" [Internal] => "A token-bearing semantic node unexpectedly emitted no token leaves.",
        TOO_MANY_PROVENANCE_OCCURRENCES: "krs::syntax::too-many-provenance-occurrences" => "A single invocation contained more same-role nodes than `u32` can key.",
        REPEATED_PROVENANCE_KEY: "krs::syntax::repeated-provenance-key" [Internal] => "A descriptor's pieces, or two nodes of one piece, held the same provenance key; the macro refuses the authored input that does this first.",
        INVALID_RULE_KEY: "krs::syntax::invalid-rule-key" => "A rule, equation, simplification, alias, or desugar attribute combines keys K does not accept together, or a desugar clause carries `recursive` or `#[k::requires]`.",
        RETIRED_ATTRIBUTE: "krs::syntax::retired-attribute" => "A retired KRS attribute was used; its replacement is named in the message.",
        INVALID_TOKEN_ATTRIBUTE: "krs::syntax::invalid-token-attribute" => "A token attribute or `k::lexeme!` term was malformed: a token attribute takes exactly one nonempty `regex` or single-terminal `terminal`, `prec` only with `regex`, and no stacked duplicate.",
        INVALID_LEXICAL_MACRO: "krs::syntax::invalid-lexical-macro" => "A `k::lexical!` or `k::layout!` block was malformed: it is empty, repeats a lexical name, names a lexical outside `[A-Z][A-Za-z0-9]*`, or has a malformed entry.",
        INVALID_SYNTAX_LIST_ATTRIBUTE: "krs::syntax::invalid-syntax-list" => "A `#[k::syntax_list]` enum was malformed: it needs exactly one two-field cons variant whose second field is the enum itself and one zero-field tuple terminator variant, a separator that is empty or one K terminal, no generics, and no `#[k::syntax]` on its variants.",
        RAW_K_SHAPE: "krs::syntax::raw-k-shape" => "A `raw_k!` text is not exactly one rule, claim, or context sentence.",
        INVALID_MATCH_RESTRICTION_KEY: "krs::syntax::invalid-match-restriction" => "A `concrete`, `symbolic`, or `smt_lemma` key was malformed: repeated, `concrete` or `symbolic` both bare and with a list, an empty list, or a key on `#[k::rule]`.",
        INVALID_SMT_METADATA: "krs::syntax::invalid-smt-metadata" => "A function's `smtlib` or `smt_hook` was malformed: both keys, an `smtlib` value that is not an SMT-LIB simple symbol, or an `smt_hook` template with a placeholder naming no field, unbalanced parentheses, a positional `#N`, or a `\"`.",
        INVALID_UNDERSPECIFIED: "krs::syntax::invalid-underspecified" => "A function's `underspecified` key was malformed or misplaced: not a nonempty string literal, repeated, or on a `partial` function.",
        INVALID_UNBOUND_VARIABLES: "krs::syntax::invalid-unbound-variables" => "An `unbound_variables = [..]` key was malformed or misplaced: outside a desugar clause's `#[k::desugar(..)]`, an empty or repeated list, a name the clause's pattern binds or its result does not use, or `_` with no `_` in the result.",
        INVALID_SPEC_MODULE: "krs::syntax::invalid-spec-module" => "A `#[k::spec_module]` was malformed: it is not on an inline `mod`, repeats or misspells a key, or names an invalid K module or one ending in the reserved `-SYNTAX` suffix.",
        INVALID_SORT_PARAMETER: "krs::syntax::invalid-sort-parameter" => "A production struct's generic parameter is not a K sort parameter `S: ?Sized` used by a field: a lifetime, const, default, other bound, or where clause.",
        INVALID_TURBOFISH: "krs::syntax::invalid-turbofish" => "A turbofish on a term head is not a list of sort markers (`Choose::<k::builtin::Int>`, `Choose::<dyn ExpSort>`): it has lifetimes, consts, or other types, or sits on a path segment other than the last.",
        INVALID_EXPRESSION_NOTATION: "krs::syntax::invalid-expression-notation" => "A domain method call (`recv.op::<Int>(..)`) has no domain turbofish, names a domain other than `Int`, `Bool`, `String`, `Float`, `Bytes`, or `K`, names an operation the domain's builtin module does not define or one with no operand; an operator is applied in a domain that does not define it (`&` on `Bool`); a Rust-only operator (`+=`, `as`, a range) occurs in a term; or a notation form (`&&`, `||`, an operator, or a method call) occurs in a pattern.",
        INVALID_ML_EXISTS: "krs::syntax::invalid-ml-exists" => "An `ml::exists` closure does not take exactly one typed parameter (`|x: Sort| predicate`), or a closure occurs anywhere but as the one argument of `ml::exists`.",
        INVALID_LIST_NOTATION: "krs::syntax::invalid-list-notation" => "Bracket list notation is malformed: it holds two rests, `[..]` or `[..rest]` names no element, a term result's rest `..` is anonymous outside a readable record cell, a pattern's rest is not `..` or `name @ ..`, or a readable record cell's anonymous rest is on one side only.",
        INVALID_CONS_LIST_ATTRIBUTE: "krs::syntax::invalid-cons-list" => "A `#[k::cons_list]` constructors enum does not have exactly one zero-field constructor and one two-field constructor, or carries an argument.",
    }
    /// Diagnostics from KRS rendering, whole-file expansion, and their protocol.
    expand {
        PARSE: "krs::expand::parse" => "The authored file does not lex or parse as a Rust file.",
        UNSUPPORTED_SOURCE: "krs::expand::unsupported-source" => "The authored file starts with a byte order mark or a shebang line, which rustc strips and the fallback lexer does not.",
        ATTRIBUTE_ORDER: "krs::expand::attribute-order" => "A KRS attribute follows an attribute that rustc would expand first.",
        ATTRIBUTE_FORM: "krs::expand::attribute-form" => "A KRS attribute has a `key = value` form, which rustc rejects for attribute macros.",
        NOT_AN_ATTRIBUTE_MACRO: "krs::expand::not-an-attribute-macro" => "The first expandable attribute names a facade item that is not a KRS attribute macro.",
        NESTED_ATTRIBUTE: "krs::expand::nested-attribute" [Internal] => "An expansion emitted a KRS attribute invocation, which this driver does not expand.",
        RECURSION: "krs::expand::recursion-limit" => "Rescanned invocations nest deeper than the expansion recursion limit.",
        REGISTRATION_SCOPE: "krs::expand::registration-scope" => "A descriptor factory is defined where the crate-root registration table cannot name it.",
SPEC_MODULE_ITEM: "krs::expand::spec-module-item" => "An item inside a `#[k::spec_module]` cannot be expanded there: a nested spec module, or an attribute on a KRS macro.",
                SELECTION: "krs::expand::selection" [Internal] => "An explicitly selected invocation does not match a discovered one.",
        PRINT: "krs::expand::print" [Internal] => "An expansion cannot be printed as text without changing its tokens.",
        DESCRIPTOR_CAPACITY: "krs::expand::descriptor-capacity" => "A descriptor count or ordinal exceeds its u32 representation.",
        DUPLICATE_PROVENANCE_KEY: "krs::expand::duplicate-provenance-key" [Internal] => "Two wire nodes of one descriptor took the provenance key of one authored node as their own; this is a bug in KRS, not in the definition.",
        UNCONSUMED_PROVENANCE_KEY: "krs::expand::unconsumed-provenance-key" [Internal] => "An authored node of a sentence was keyed at parse but no wire node of its descriptor takes its provenance key, so expansion would drop it; this is a bug in KRS, not in the definition.",
        UNANCHORED_PROVENANCE_KEY: "krs::expand::unanchored-provenance-key" [Internal] => "A wire node named a provenance key that no authored node of its sentence holds; this is a bug in KRS, not in the definition.",
        MISSING_PROVENANCE_KEY: "krs::expand::missing-provenance-key" [Internal] => "An authored node that expansion turns into a wire node holds no provenance key from its sentence's parse; this is a bug in KRS, not in the definition.",
        MISREAD_PROVENANCE_KEY: "krs::expand::misread-provenance-key" [Internal] => "Expansion read the provenance key of another term node than the one it turns into a wire node, which would carry that node's location; this is a bug in KRS, not in the definition.",
        HELPER_PAYLOAD_FORM: "krs::expand::helper-payload-form" => "A helper attribute requires a parenthesized payload.",
        CFG_REPRODUCTION: "krs::expand::cfg-reproduction" [Internal] => "A cfg attribute could not be reproduced for generated tokens.",
        MISSING_COMPUTATION_CELL: "krs::expand::missing-computation-cell" => "A configuration-owned rule has no computation-cell field.",
        INITIALIZER_BODY_SHAPE: "krs::expand::initializer-body-shape" => "A fixed initializer does not contain exactly one struct expression.",
        MISSING_CHECKED_FIELD: "krs::expand::missing-checked-field" [Internal] => "A field accepted by syntax validation is absent during rendering.",
        INITIALIZER_CELL_SHAPE: "krs::expand::initializer-cell-shape" => "A nested fixed-cell initializer is not a struct expression.",
        UNDECLARED_CELL: "krs::expand::undeclared-cell" => "A `cells!` entry or an initializer field names a cell its owner does not declare: a cell inside a group is written with the group (`Group::cell`).",
        CELL_STATE_FAMILY_MISMATCH: "krs::expand::cell-state-family-mismatch" => "A cell wrapper disagrees with the state family of its initializer or rule.",
        MISSING_INITIALIZER: "krs::expand::missing-initializer" => "A configuration has no inherent `#[k::init]` initializer, which gives each cell its initial content.",
        INITIALIZER_RECORD_UPDATE: "krs::expand::initializer-record-update" => "An initializer term is a record update `Ctor { f: e, ..t }` or an open record `Ctor { f: e, .. }`; an initializer term names every field.",
        CLAIM_ONLY_TERM: "krs::expand::claim-only-term" => "A claim-only term island occurs outside a claim.",
        INITIALIZER_FRAGMENT: "krs::expand::initializer-fragment" => "An initializer term uses a fragment instead of constructing nested cells directly.",
        EMPTY_GRAMMAR_DECLARATION: "krs::expand::empty-grammar-declaration" => "A precedence or associativity declaration contains no sentences.",
        UNSUPPORTED_SYMBOL_ITEM: "krs::expand::unsupported-symbol-item" => "A stable-symbol attribute is attached to an unsupported item kind.",
        DUPLICATE_SYMBOL: "krs::expand::duplicate-symbol" => "A declaration contains more than one explicit stable-symbol attribute.",
        SYMBOL_ATTRIBUTE_ORDER: "krs::expand::symbol-attribute-order" => "A stable-symbol attribute does not immediately precede one symbol-bearing declaration attribute.",
        UNKNOWN_HOOK: "krs::expand::unknown-hook" => "A hook path does not name a supported KRS hook operation.",
        INVALID_HOOK_STRING: "krs::expand::invalid-hook-string" => "A quoted hook is not of the form `NAMESPACE.name`.",
        UNKNOWN_HOOK_NAME: "krs::expand::unknown-hook-name" => "A quoted hook names no hook in the pinned hook registry.",
        CATALOGUED_RAW_HOOK: "krs::expand::catalogued-raw-hook" => "A quoted hook names a hook the typed catalog covers; the typed path is required.",
        RAW_HOOK_ARITY: "krs::expand::raw-hook-arity" => "A quoted crypto hook's production has a different argument count than the pinned registry.",
        RAW_HOOK: "krs::expand::raw-hook" => "A quoted hook's signature is unchecked: a warning in a package that allows raw K.",
        FUNCTION_ALIAS_CONFLICT: "krs::expand::function-alias-conflict" => "A function production is also declared as a static alias.",
        INVALID_AVOID_METADATA: "krs::expand::invalid-avoid-metadata" => "An avoid argument explicitly supplies false instead of omitting the metadata.",
        INVALID_PLACEMENT_FLAG: "krs::expand::invalid-placement-flag" => "An `internal` or `program` flag is false, repeated, combined with the other, or on a non-pub item.",
        DUPLICATE_STRICTNESS: "krs::expand::duplicate-strictness" => "A constructor declares more than one strictness strategy.",
        ALIAS_MARKER_FORM: "krs::expand::alias-marker-form" => "A constructor alias helper does not use marker syntax.",
        DUPLICATE_ALIAS: "krs::expand::duplicate-alias" => "A constructor declares its alias helper more than once.",
        ORPHAN_HELPER: "krs::expand::orphan-helper" => "A helper attribute is expanded without its required preceding declaration attribute.",
        SORT_PARENT_MISMATCH: "krs::expand::sort-parent-mismatch" => "A reference sort lacks one semantic parent path per Rust marker supertrait.",
        SORT_MEMBERSHIP: "krs::expand::sort-membership" => "A type stands where membership in a K sort is required (the parent of a sort it is declared in, a sort marker's bound) but no `k::sorts!` membership line or subsort impl places it below that sort: a membership line covers its sort's parents in the same block only.",
        DUPLICATE_MEMBERSHIP_RELATION: "krs::expand::duplicate-membership-relation" => "A readable sort block declares a membership relation more than once.",
        FRAMEWORK_SORT_ENTRY: "krs::expand::framework-sort-entry" => "A framework sort block contains a membership line or a bracket.",
        EMPTY_SORT_DECLARATION: "krs::expand::empty-sort-declaration" [Internal] => "A sort declaration contains no descriptor-bearing tokens.",
        EMPTY_SORT_PATH: "krs::expand::empty-sort-path" [Internal] => "A sort reference contains no path segments.",
        EMPTY_BRACKET: "krs::expand::empty-bracket" [Internal] => "A bracket template contains no descriptor-bearing tokens.",
        ENUM_VARIANT_COLLISION: "krs::expand::enum-variant-collision" => "Two enum variants have the same readable rule resolution name.",
        NOT_A_DECLARATION: "krs::expand::not-a-declaration" => "A term names, through an unqualified path, a Rust item that is no KRS declaration of that name (the prelude's `Some`, a variant under a renaming `use`): a term names a constructor, function, constant, cell group or builtin operation.",
        UNBOUND_NAME: "krs::expand::unbound-name" => "A bare snake-case name outside a pattern is not bound by the sentence: not by its pattern, an existential or fresh binder, a parameter, or an enclosing `let`; or a name a rule's or an equation's map key or set element reads only below a function application, which the key's or element's evaluation reads and does not bind.",
        INVALID_RECORD_UPDATE: "krs::expand::invalid-record-update" => "The base `t` of a record update `Ctor { f: e, ..t }` is not a binder of the rule.",
        MATCHES_OUTSIDE_CONDITION: "krs::expand::matches-outside-condition" => "A `k::matches!` (K's `:=K`) occurs in a left-hand side, an initializer, a `cells!` cell value, or a claim.",
        LET_OUTSIDE_TERM: "krs::expand::let-outside-term" => "A `let` block (K's `#let`) occurs in a left-hand side, an initializer, a `cells!` cell value, or a claim.",
        CLAIM_SUBJECT_ONLY_TERM: "krs::expand::claim-subject-only-term" => "An anonymous term occurrence appears outside a claim subject.",
        CONFIGURATION_SHAPE: "krs::expand::configuration-shape" => "A fixed configuration is not a named-field struct.",
        FRAGMENT_SHAPE: "krs::expand::fragment-shape" => "A fragment payload is not a parent record with named fields.",
        CONTEXT_ALIAS_RESULT_SORT: "krs::expand::context-alias-result-sort" => "A named context alias has a result sort other than the unambiguous `KResult` sort.",
        UNDECLARED_STRICTNESS_FIELD: "krs::expand::undeclared-strictness-field" [Internal] => "Strictness metadata names a field absent from the rendered declaration.",
        INVALID_ID_TOKEN: "krs::expand::invalid-id-token" => "A builtin Id token is not a dollar-prefixed nonempty ASCII identifier.",
        FACADE_DEPENDENCY: "krs::expand::facade-dependency" => "The invoking crate has no direct dependency on the KRS facade package.",
        PROTOCOL_ERROR: "krs::expand::protocol" [Environment] => "The request was not a valid schema-1 request.",
        EXISTENTIAL_PLACEMENT: "krs::expand::existential-placement" => "An `exists` or `ensures` helper is attached to an equation, simplification, or alias; existential results and ensures are allowed on claims and transition rules.",
        FRESH_PLACEMENT: "krs::expand::fresh-placement" => "A `fresh` helper is attached to an equation, simplification, alias, claim, context, context alias, anywhere rule, or heat or cool rule; fresh values are drawn only by a transition step of the configuration.",
        TURBOFISH_PLACEMENT: "krs::expand::turbofish-placement" => "A turbofish instance (`Choose::<k::builtin::Int> { .. }`) occurs in an initializer, which builds a concrete value.",
        ML_PLACEMENT: "krs::expand::ml-placement" => "An `ml::Predicate` subject or result is on a sentence other than a simplification, the subject and result types of a predicate simplification disagree, or an `ml::exists` closure occurs in an initializer.",
        UNKNOWN_ML_ITEM: "krs::expand::unknown-ml-item" => "A term names an `ml::` item outside the closed set of matching-logic connectives.",
        CELL_COLLECTION_PLACEMENT: "krs::expand::cell-collection-placement" => "An optional-cell `Some`/`None` entry or a cell-collection entry occurs in a context alias or an equation's function context, which read fixed cells only.",
        TURBOFISH_SPELLING: "krs::expand::turbofish-spelling" => "A turbofish argument is spelled for the other layer: a readable `k::rules!` clause writes a sort marker (`Choose::<dyn ExpSort>`), or reference code writes a sort's `k::Term<..>` alias (`Choose::<Exp>`); readable clauses name the sort and reference code the marker.",
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
        PROTOCOL_ERROR: "krs::policy::protocol" [Environment] => "The request was not a valid schema-1 request.",
        RAW_K_NOT_ALLOWED: "krs::policy::raw-k-not-allowed" => "A quoted hook or `raw_k!` occurs in a package without `allow-raw-k = true`, or under the strict profile.",
    }
    /// Diagnostics from `krs parse`, `krs run`, `krs search`, and `krs prove` (`krs-exec`).
    exec {
        BACKEND: "krs::exec::backend" [Environment] => "The native backend failed while loading or running the definition.",
        PROGRAM: "krs::exec::program" => "FILE was given without $PGM, or omitted with $PGM.",
        VARIABLE: "krs::exec::variable" => "A configuration variable is unknown, bound twice, or missing.",
        COLLECTION_ELEMENT_SORT: "krs::exec::collection-element-sort" => "A configuration variable's value has a part that does not fit the element types of the typed collection cell it fills.",
        PARSE: "krs::exec::parse" => "Program or configuration-variable text does not parse at its sort.",
        SORT: "krs::exec::sort" => "A requested parse sort is not a program sort.",
        CLAIM: "krs::exec::claim" => "A claim label matched no claim, several claims, or the definition has no claims.",
        STREAMS: "krs::exec::streams" => "Search was requested on a definition with stream cells.",
        UNAVAILABLE: "krs::exec::unavailable" [Environment] => "The requested operation is not available in this build.",
        RESULT: "krs::exec::result" [Internal] => "The backend returned a result KRS cannot read.",
        STAGE_CACHE: "krs::exec::stage-cache" [Environment] => "The compiled-stage cache directory lies inside the input's Cargo workspace, so it is not used.",
    }
}
