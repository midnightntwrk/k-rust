//! The value a token denotes, by which two spellings of one value are one term
//! ([`k_rust_domain::token_value`]), read for a frontend sort at the KORE sort it is emitted as.
//!
//! Program expansion compares tokens by [`token_value`] over the emitted definition's
//! declarations; a compiler that writes terms over K's prelude, whose declarations it does not
//! hold, compares them by [`k_rust_domain::prelude_token_value`], the same value under the
//! prelude's hooks.

pub use k_rust_domain::TokenValue;

use super::declaration_facts::backend_sort;
use crate::kast::Sort;

/// The value the token `text` of `sort` denotes in a definition that declares `sort`'s head with
/// the hook `hook` and with domain values exactly when `has_domain_values`
/// ([`k_rust_domain::token_value`] at the KORE sort `sort` is emitted as). `None` when the sort
/// has no domain values or the text names no value of it; the token then denotes its text.
pub fn token_value(
    sort: &Sort,
    hook: Option<&str>,
    has_domain_values: bool,
    text: &str,
) -> Option<TokenValue> {
    k_rust_domain::token_value(&backend_sort(sort), hook, has_domain_values, text)
}

#[cfg(test)]
mod tests {
    use k_rust_domain::prelude_hook;

    use crate::{
        builtin::embedded,
        definition::{AttributeKey, SortHead},
        kast::Sort,
        kompile::module_to_kore::encode_kore_sort,
        kore::ast::Sort as KoreSort,
        outer::{ResolvedSource, load_with_options},
    };

    /// The hooks [`prelude_hook`] states are those the embedded prelude declares.
    #[test]
    fn the_prelude_hooks_are_the_embedded_prelude_s() {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new(
                "probe.k",
                "requires \"domains.md\"\nmodule PROBE\n  imports DOMAINS\n  imports MINT\nendmodule\n",
            ),
            "PROBE",
            &mut resolver,
            &crate::kompile::CompilationBackend::Rust.load_options(),
        )
        .expect("the prelude loads");
        let resolved =
            crate::definition::ResolvedDefinition::resolve(loaded.definition()).expect("resolves");
        let module = resolved.module_id("PROBE").expect("PROBE");
        let views = resolved.views();
        let sorts = views.sort_catalog(module);
        for sort in [
            Sort::new("Int"),
            Sort::new("Bool"),
            Sort::new("Float"),
            Sort::new("String"),
            Sort::new("Bytes"),
            Sort::with_parameters("MInt", vec![Sort::new("Width")]),
        ] {
            let declared = sorts
                .attributes_for(&SortHead::from(&sort))
                .and_then(|attributes| attributes.string(AttributeKey::Hook));
            assert_eq!(
                declared,
                prelude_hook(&sort.name, sort.parameters.len()),
                "{sort}"
            );
        }
        assert_eq!(prelude_hook("Id", 0), None);
    }

    /// A nullary sort of the prelude whose tokens have values is emitted as `Sort` followed by
    /// its name, the KORE sort [`k_rust_domain::prelude_token_value`] reads its tokens at.
    #[test]
    fn the_prelude_sorts_are_emitted_as_sort_and_their_names() {
        for name in ["Int", "Bool", "Float", "String", "Bytes"] {
            assert_eq!(
                encode_kore_sort(&Sort::new(name)),
                KoreSort::Application {
                    name: format!("Sort{name}"),
                    arguments: Vec::new(),
                },
            );
        }
    }
}
