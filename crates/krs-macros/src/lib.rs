//! Narrow procedural-macro facade for the explicit KRS surface.
//!
//! Parsing belongs to `krs-syntax`; these macros only preserve/check the Rust
//! surface and register current-protocol host descriptors. Whole-definition name
//! resolution and K semantics remain collector/compiler responsibilities.

use proc_macro::TokenStream;

mod environment;
mod expand;
mod provenance;

use environment::ProcMacroEnvironment;

fn finish(result: syn::Result<proc_macro2::TokenStream>) -> TokenStream {
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Declares an open K sort on an empty Rust marker trait.
#[proc_macro_attribute]
pub fn sort(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::sort(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares readable sort aliases, membership markers, and semantic edges.
#[proc_macro]
pub fn sorts(input: TokenStream) -> TokenStream {
    finish(expand::sorts(&ProcMacroEnvironment, input.into()))
}

/// Expands like [`sorts!`] and also emits the invocation's factory table.
///
/// This is the `krs` facade's framework `KItem`/`KResult` block. Authors use
/// [`sorts!`]; the extra `FRAMEWORK_FACTORIES` table serves collectors that
/// enumerate explicit registration tables instead of linker sections.
#[doc(hidden)]
#[proc_macro]
pub fn __framework_sorts(input: TokenStream) -> TokenStream {
    finish(expand::framework_sorts(input.into()))
}

/// Pins the stable public identity of a symbol-bearing declaration.
///
/// This ordinary attribute must precede `#[k::sort]` or
/// `#[k::constructor]`; it delegates the declaration to that macro while
/// retaining the symbol literal's exact source span.
#[proc_macro_attribute]
pub fn symbol(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::symbol(attributes.into(), item.into()))
}

/// Declares a unit or named-record K constructor.
#[proc_macro_attribute]
pub fn constructor(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::constructor(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares one total K function production.
#[proc_macro_attribute]
pub fn function(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::function(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
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
    finish(expand::constructors(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares a nominal token sort and its checked regex production.
#[proc_macro_attribute]
pub fn token(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::token(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Adds one syntax-only bracket production to an attributed sort.
#[proc_macro_attribute]
pub fn bracket(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::bracket(attributes.into(), item.into()))
}

/// Adds one explicit after-the-fact subsort relation. Deterministic layer-2
/// output may name its semantic supersort alias with `sort = ...` while the
/// Rust impl targets the corresponding marker trait.
#[proc_macro_attribute]
pub fn subsort(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::subsort(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Constructor helper consumed by `#[k::constructor]`.
#[proc_macro_attribute]
pub fn strict(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::orphan_strictness(
        "strict",
        attributes.into(),
        item.into(),
    ))
}

/// Constructor helper consumed by `#[k::constructor]`.
#[proc_macro_attribute]
pub fn seqstrict(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::orphan_strictness(
        "seqstrict",
        attributes.into(),
        item.into(),
    ))
}

/// Declares a complete fixed-cell configuration and its paired initializer.
///
/// Plain fields marked `#[k::cell]` infer `KCell` for `KSequence` and `Cell`
/// for every other leaf sort. Explicit `Cell<T>`/`KCell<KSequence>` fields
/// remain supported as the reference surface.
#[proc_macro_attribute]
pub fn configuration(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::configuration(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares a nominal nested fixed-cell group.
#[proc_macro_attribute]
pub fn cell(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::cell(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares the restricted associated initializer paired to a configuration.
///
/// Plain parameters derive their external names by uppercasing the Rust
/// binding, and the parameter used in the computation cell is inferred as the
/// main input. `#[k::config_var(...)]` remains available as an override.
#[proc_macro_attribute]
pub fn init(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::init(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares an ordinary term rule or a simultaneous fixed-configuration rule.
#[proc_macro_attribute]
pub fn rule(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::rule(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares a readable family of independently named ordinary term rules.
///
/// A block-local `use Family::*;` selects one constructor family explicitly.
/// Without that line, an unqualified clause head follows ordinary Rust module
/// scope, including `use Family::*;` imports. Colliding module globs are
/// reported by rustc at the authored head instead of selecting one by order.
#[proc_macro]
pub fn rules(input: TokenStream) -> TokenStream {
    finish(expand::rules(&ProcMacroEnvironment, input.into()))
}

/// Declares one unconditional or `requires`-guarded function equation.
#[proc_macro_attribute]
pub fn equation(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::equation(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares one simplifier lemma, with an optional numeric ordering hint.
#[proc_macro_attribute]
pub fn simplification(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::simplification(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares one explicitly labeled reachability claim.
#[proc_macro_attribute]
pub fn claim(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::claim(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares a reversible static alias production helper or alias clause.
#[proc_macro_attribute]
pub fn alias(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::alias(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Declares one reusable one-sided fixed-configuration context template.
#[proc_macro_attribute]
pub fn context_alias(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::context_alias(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Attaches an exact numeric priority to an equation.
#[proc_macro_attribute]
pub fn priority(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::priority(
        &ProcMacroEnvironment,
        attributes.into(),
        item.into(),
    ))
}

/// Rule helper consumed by an outer `#[k::rule]` expansion.
#[proc_macro_attribute]
pub fn requires(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::orphan_rule_helper(
        &ProcMacroEnvironment,
        "requires",
        attributes.into(),
        item.into(),
    ))
}

/// Claim helper consumed by an outer `#[k::claim]` expansion.
#[proc_macro_attribute]
pub fn exists(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::orphan_rule_helper(
        &ProcMacroEnvironment,
        "exists",
        attributes.into(),
        item.into(),
    ))
}

/// Claim postcondition helper consumed by an outer `#[k::claim]` expansion.
#[proc_macro_attribute]
pub fn ensures(attributes: TokenStream, item: TokenStream) -> TokenStream {
    finish(expand::orphan_rule_helper(
        &ProcMacroEnvironment,
        "ensures",
        attributes.into(),
        item.into(),
    ))
}

/// Parses the M1 named-term subset as a Rust expression.
///
/// At M1 this is a type-checking placeholder, not a runtime term builder. Its
/// expansion validates authored Rust paths inside a never-called closure and
/// then panics if evaluated. Rule attributes consume their nested `term!`
/// payloads before this function-like macro is expanded.
#[proc_macro]
pub fn term(input: TokenStream) -> TokenStream {
    finish(expand::term(input.into()))
}

/// Compiler-owned concrete builtin Id token island.
#[proc_macro]
pub fn id(input: TokenStream) -> TokenStream {
    let literal = syn::parse_macro_input!(input as syn::LitStr);
    let value = literal.value();
    if !value.strip_prefix('$').is_some_and(|tail| {
        !tail.is_empty()
            && tail
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    }) {
        return syn::Error::new(literal.span(), "invalid builtin `Id` token")
            .into_compile_error()
            .into();
    }
    quote::quote!(::core::panic!("id! has no runtime value")).into()
}

/// Compiler-owned concrete builtin Bytes token island.
#[proc_macro]
pub fn bytes(input: TokenStream) -> TokenStream {
    let _literal = syn::parse_macro_input!(input as syn::LitByteStr);
    quote::quote!(::core::panic!("bytes! has no runtime value")).into()
}

/// Compiler-owned fresh anonymous object-language occurrence.
#[proc_macro]
pub fn anonymous(_input: TokenStream) -> TokenStream {
    quote::quote!(::core::panic!("anonymous! has no runtime value")).into()
}

/// Compiler-owned associative object-Bool disjunction.
#[proc_macro]
pub fn or_bool(_input: TokenStream) -> TokenStream {
    quote::quote!(::core::panic!("or_bool! has no runtime value")).into()
}

/// Checks a compiler-owned complete nested-cell term.
#[proc_macro]
pub fn fragment(input: TokenStream) -> TokenStream {
    finish(expand::fragment(&ProcMacroEnvironment, &input.into()))
}

/// Checks a complete computation-sequence expression without evaluating it.
#[proc_macro]
pub fn k(input: TokenStream) -> TokenStream {
    finish(expand::k(&ProcMacroEnvironment, input.into()))
}

/// Checks a compiler-owned finite-map expression island.
#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    finish(expand::map(&ProcMacroEnvironment, input.into()))
}

/// Checks a compiler-owned simultaneous fixed-cell expression island.
#[proc_macro]
pub fn cells(input: TokenStream) -> TokenStream {
    finish(expand::cells(input.into()))
}

/// Declares one or more precedence chains between production groups.
#[proc_macro]
pub fn precedence(input: TokenStream) -> TokenStream {
    finish(expand::precedence(&ProcMacroEnvironment, input.into()))
}

/// Declares typed associativity for production groups.
#[proc_macro]
pub fn associativity(input: TokenStream) -> TokenStream {
    finish(expand::associativity(&ProcMacroEnvironment, input.into()))
}
