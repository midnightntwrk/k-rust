//! Narrow procedural-macro facade for the explicit KRS surface.
//!
//! Parsing belongs to `krs-syntax` and expansion to `krs-expand`; these entry
//! points only pass rustc's tokens and invocation environment to
//! `krs-expand` and render its diagnostics. Whole-definition name resolution
//! and K semantics remain collector/compiler responsibilities.

use proc_macro::TokenStream;

mod environment;

use environment::ProcMacroEnvironment;
use krs_expand::{AttributeMacro, FunctionMacro};

fn finish(result: syn::Result<proc_macro2::TokenStream>) -> TokenStream {
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

fn attribute_macro(
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> TokenStream {
    finish(krs_expand::expand_attribute(
        entry,
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

fn function_macro(entry: FunctionMacro, input: TokenStream) -> TokenStream {
    finish(krs_expand::expand_function(
        entry,
        &ProcMacroEnvironment,
        input.into(),
    ))
}

/// Declares an open K sort on an empty Rust marker trait.
#[proc_macro_attribute]
pub fn sort(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Sort, attributes, item)
}

/// Declares readable sort aliases, membership markers, and semantic edges.
#[proc_macro]
pub fn sorts(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Sorts, input)
}

/// Expands like [`sorts!`] and also emits the invocation's factory table.
///
/// This is the `krs` facade's framework `KItem`/`KResult` block. Authors use
/// [`sorts!`]; the extra `FRAMEWORK_FACTORIES` table serves collectors that
/// enumerate explicit registration tables instead of linker sections.
#[doc(hidden)]
#[proc_macro]
pub fn __framework_sorts(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::FrameworkSorts, input)
}

/// Pins the stable public identity of a symbol-bearing declaration.
///
/// This ordinary attribute must precede `#[k::sort]` or
/// `#[k::constructor]`; it delegates the declaration to that macro while
/// retaining the symbol literal's exact source span.
#[proc_macro_attribute]
pub fn symbol(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Symbol, attributes, item)
}

/// Declares a unit or named-record K constructor.
#[proc_macro_attribute]
pub fn constructor(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Constructor, attributes, item)
}

/// Declares one total K function production.
#[proc_macro_attribute]
pub fn function(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Function, attributes, item)
}

/// Declares a Rust enum as a family of K constructors.
///
/// Readable open families (`sort = ..., result = ...`) require a following
/// exhaustive enum-level precedence chain. `>` means “binds tighter than”;
/// `left`, `right`, and `non_assoc` prefix tiers with explicit associativity.
/// A bare tier carries no associativity constraint; `non_assoc` lowers to K's
/// explicit `syntax non-assoc` sentence. These three keywords are reserved in
/// group-name position. An optional name before a member list selects the
/// emitted production-group identity:
///
/// ```ignore
/// #[k::constructors(sort = Expr, result = KResult)]
/// #[k::precedence((Neg) > left additive (Add, Sub) > non_assoc equality (Eq))]
/// enum Op { /* ... */ }
/// ```
///
/// Every enum variant must occur exactly once. Variant declaration order has
/// no precedence meaning. Deterministic layer-2 output uses the internal
/// `reference` form with fully materialized fields and metadata.
#[proc_macro_attribute]
pub fn constructors(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Constructors, attributes, item)
}

/// Declares a nominal token sort and its checked regex production.
#[proc_macro_attribute]
pub fn token(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Token, attributes, item)
}

/// Adds one syntax-only bracket production to an attributed sort.
#[proc_macro_attribute]
pub fn bracket(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Bracket, attributes, item)
}

/// Adds one explicit after-the-fact subsort relation. Deterministic layer-2
/// output may name its semantic supersort alias with `sort = ...` while the
/// Rust impl targets the corresponding marker trait.
#[proc_macro_attribute]
pub fn subsort(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Subsort, attributes, item)
}

/// Constructor helper consumed by `#[k::constructor]`.
#[proc_macro_attribute]
pub fn strict(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Strict, attributes, item)
}

/// Constructor helper consumed by `#[k::constructor]`.
#[proc_macro_attribute]
pub fn seqstrict(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Seqstrict, attributes, item)
}

/// Declares a complete fixed-cell configuration and its paired initializer.
///
/// Plain fields marked `#[k::cell]` infer `KCell` for `KSequence` and `Cell`
/// for every other leaf sort. Explicit `Cell<T>`/`KCell<KSequence>` fields
/// remain supported as the reference surface.
#[proc_macro_attribute]
pub fn configuration(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Configuration, attributes, item)
}

/// Declares a nominal nested fixed-cell group.
#[proc_macro_attribute]
pub fn cell(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Cell, attributes, item)
}

/// Declares the restricted associated initializer paired to a configuration.
///
/// Plain parameters derive their external names by uppercasing the Rust
/// binding, and the parameter used in the computation cell is inferred as the
/// main input. `#[k::config_var(...)]` remains available as an override.
#[proc_macro_attribute]
pub fn init(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Init, attributes, item)
}

/// Declares an ordinary term rule or a simultaneous fixed-configuration rule.
#[proc_macro_attribute]
pub fn rule(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Rule, attributes, item)
}

/// Declares a readable family of independently named ordinary term rules.
///
/// A block-local `use Family::*;` selects one constructor family explicitly.
/// Without that line, an unqualified clause head follows ordinary Rust module
/// scope, including `use Family::*;` imports. Colliding module globs are
/// reported by rustc at the authored head instead of selecting one by order.
#[proc_macro]
pub fn rules(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Rules, input)
}

/// Declares one unconditional or `requires`-guarded function equation.
#[proc_macro_attribute]
pub fn equation(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Equation, attributes, item)
}

/// Declares one simplifier lemma, with an optional numeric ordering hint.
#[proc_macro_attribute]
pub fn simplification(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Simplification, attributes, item)
}

/// Declares one explicitly labeled reachability claim.
#[proc_macro_attribute]
pub fn claim(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Claim, attributes, item)
}

/// Declares a reversible static alias production helper or alias clause.
#[proc_macro_attribute]
pub fn alias(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Alias, attributes, item)
}

/// Declares one reusable one-sided fixed-configuration context template.
#[proc_macro_attribute]
pub fn context_alias(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::ContextAlias, attributes, item)
}

/// Attaches an exact numeric priority to an equation.
#[proc_macro_attribute]
pub fn priority(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Priority, attributes, item)
}

/// Rule helper consumed by an outer `#[k::rule]` expansion.
#[proc_macro_attribute]
pub fn requires(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Requires, attributes, item)
}

/// Claim helper consumed by an outer `#[k::claim]` expansion.
#[proc_macro_attribute]
pub fn exists(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Exists, attributes, item)
}

/// Claim postcondition helper consumed by an outer `#[k::claim]` expansion.
#[proc_macro_attribute]
pub fn ensures(attributes: TokenStream, item: TokenStream) -> TokenStream {
    attribute_macro(AttributeMacro::Ensures, attributes, item)
}

/// Parses the named-term subset as a Rust expression.
///
/// This is a type-checking placeholder, not a runtime term builder. Its
/// expansion validates authored Rust paths inside a never-called closure and
/// then panics if evaluated. Rule attributes consume their nested `term!`
/// payloads before this function-like macro is expanded.
#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Term, input)
}

/// Compiler-owned concrete builtin Id token island.
#[proc_macro]
pub fn id(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Id, input)
}

/// Compiler-owned concrete builtin Bytes token island.
#[proc_macro]
pub fn bytes(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Bytes, input)
}

/// Compiler-owned fresh anonymous object-language occurrence.
#[proc_macro]
pub fn anonymous(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Anonymous, input)
}

/// Compiler-owned associative object-Bool disjunction.
#[proc_macro]
pub fn or_bool(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::OrBool, input)
}

/// Checks a compiler-owned complete nested-cell term.
#[proc_macro]
pub fn fragment(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Fragment, input)
}

/// Checks a complete computation-sequence expression without evaluating it.
#[proc_macro]
pub fn k(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::K, input)
}

/// Checks a compiler-owned finite-map expression island.
#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Map, input)
}

/// Checks a compiler-owned simultaneous fixed-cell expression island.
#[proc_macro]
pub fn cells(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Cells, input)
}

/// Declares one or more precedence chains between production groups.
#[proc_macro]
pub fn precedence(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Precedence, input)
}

/// Declares typed associativity for production groups.
#[proc_macro]
pub fn associativity(input: TokenStream) -> TokenStream {
    function_macro(FunctionMacro::Associativity, input)
}
