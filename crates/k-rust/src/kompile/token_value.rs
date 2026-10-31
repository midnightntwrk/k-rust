//! The value a token denotes, by which two spellings of one value are one term.
//!
//! A token of a sort with domain values denotes the domain value the emitted definition reads
//! from its text: an element of its hook's domain, which the backend stores as its canonical
//! text ([`DomainKind`]). So two spellings of one value are one term: the integers `1`, `+1` and
//! `01`; the strings `"a"` and `"\x61"`; the byte strings `b"ab"` and `b"\x61\x62"`; the floats
//! `1.5`, `1.50` and `15e-1`, which name one binary64 number. A float's format is part of its
//! value (`1.5f` is a binary32 number, another value than `1.5`), as is its sign at zero (`0.0`
//! and `-0.0` are two values, though `==Float` holds of them), and the literal syntax names one
//! NaN per format, which is equal to itself as a term. A token of a sort whose domain values are
//! their texts (an unhooked token sort), of a sort without domain values, or whose text names no
//! value of its sort, denotes its text.
//!
//! Program expansion compares tokens by [`token_value`] over the emitted definition's
//! declarations; a compiler that writes terms over K's prelude, whose declarations it does not
//! hold, compares them by [`prelude_token_value`], the same value under the prelude's hooks.

use k_rust_backend::{
    builtin::DeclarationFacts,
    term::{DomainKind, Sort as BackendSort, Term as BackendTerm, TermKind},
};

use super::{
    declaration_facts::backend_sort, module_to_kore::encode_kore_sort, term_to_kore::token_payload,
};
use crate::{kast::Sort, kore::string::LiteralEncoding};

/// The value a token denotes ([`token_value`]): two tokens of one sort are one term exactly when
/// their values are equal, or, when neither has one, their texts are.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TokenValue(BackendTerm);

impl TokenValue {
    /// A text that names this value and no other value of its sort: the payload of its
    /// canonical domain value, its bytes in hexadecimal. Two tokens of one sort have one key
    /// exactly when they denote one value. It is a key to compare or index by, not a token.
    pub fn key(&self) -> String {
        let TermKind::DomainValue { value, .. } = self.0.kind() else {
            unreachable!("a token value is a domain value")
        };
        value
            .as_bytes()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

/// The value the token `text` of `sort` denotes in a definition that declares `sort`'s head with
/// the hook `hook` and with domain values exactly when `has_domain_values`: the domain value the
/// emitted definition reads from the text, whose payload is its kind's canonical text. `None`
/// when the sort has no domain values or the text names no value of it; the token then denotes
/// its text.
///
/// The work is that of reading the value: for a float of a format other than binary32 and
/// binary64, exact big-integer arithmetic on its digits. A caller comparing many tokens keeps
/// each token's value rather than reading it per comparison.
pub fn token_value(
    sort: &Sort,
    hook: Option<&str>,
    has_domain_values: bool,
    text: &str,
) -> Option<TokenValue> {
    let backend = backend_sort(sort);
    let kind = DomainKind::of_declared_sort(&backend, has_domain_values, hook)?;
    let encoding = LiteralEncoding::of_domain_value(&encode_kore_sort(sort));
    let payload = token_payload(text, hook, encoding).ok()?;
    BackendTerm::domain_value_in(&OneKind(kind), backend, payload).map(TokenValue)
}

/// [`token_value`] for a sort of K's prelude (`domains.md`), under the hook the prelude declares
/// it with ([`prelude_hook`]); `None` for any other sort, whose tokens denote their texts.
pub fn prelude_token_value(sort: &Sort, text: &str) -> Option<TokenValue> {
    let hook = prelude_hook(sort)?;
    token_value(sort, Some(hook), true, text)
}

/// Whether the tokens `left` and `right` of `sort`, a sort of K's prelude, denote one value
/// ([`prelude_token_value`]): equal texts, or equal values.
pub fn same_prelude_token(sort: &Sort, left: &str, right: &str) -> bool {
    left == right
        || matches!(
            (prelude_token_value(sort, left), prelude_token_value(sort, right)),
            (Some(left), Some(right)) if left == right
        )
}

/// The hook K's prelude (`domains.md`) declares the sort `sort` with, for the sorts whose tokens
/// have values other than their texts: `Int`, `Bool`, `Float`, `String`, `Bytes` and `MInt{W}`.
pub fn prelude_hook(sort: &Sort) -> Option<&'static str> {
    Some(match (sort.name.as_str(), sort.parameters.len()) {
        ("Int", 0) => "INT.Int",
        ("Bool", 0) => "BOOL.Bool",
        ("Float", 0) => "FLOAT.Float",
        ("String", 0) => "STRING.String",
        ("Bytes", 0) => "BYTES.Bytes",
        ("MInt", 1) => "MINT.MInt",
        _ => return None,
    })
}

/// The declarations of one sort of the given kind, all a domain value's construction reads.
struct OneKind(DomainKind);

impl DeclarationFacts for OneKind {
    type Sort = BackendSort;

    fn domain_kind(&self, _: &BackendSort) -> Option<DomainKind> {
        Some(self.0)
    }

    fn has_domain_values(&self, _: &BackendSort) -> bool {
        true
    }

    fn check_subsort(&self, sub: &BackendSort, sup: &BackendSort) -> bool {
        sub == sup
    }
}

#[cfg(test)]
mod tests {
    use super::{prelude_hook, same_prelude_token};
    use crate::{
        builtin::embedded,
        definition::{AttributeKey, SortHead},
        kast::Sort,
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
            assert_eq!(declared, prelude_hook(&sort), "{sort}");
        }
        assert_eq!(prelude_hook(&Sort::new("Id")), None);
    }

    #[test]
    fn prelude_tokens_are_compared_by_value() {
        let float = Sort::new("Float");
        for (left, right, same) in [
            ("1.5", "1.50", true),
            ("1.5", "15e-1", true),
            ("1.5", "1.5d", true),
            ("1.5", "1.5f", false),
            ("1.5f", "1.50f", true),
            ("0.0", "-0.0", false),
            ("0.0", "0e10", true),
            ("1.0p11x5", "1.00p11x5", true),
            ("1.0p11x5", "1.0p11x6", false),
            ("NaN", "NaN", true),
            ("NaNf", "NaN", false),
        ] {
            assert_eq!(
                same_prelude_token(&float, left, right),
                same,
                "{left} {right}"
            );
        }
        assert!(same_prelude_token(&Sort::new("Int"), "01", "1"));
        assert!(same_prelude_token(&Sort::new("Int"), "-0", "0"));
        assert!(!same_prelude_token(&Sort::new("Int"), "1", "-1"));
        assert!(same_prelude_token(
            &Sort::new("String"),
            "\"\\x61\"",
            "\"a\""
        ));
        assert!(same_prelude_token(
            &Sort::new("Bytes"),
            "b\"\\x61\"",
            "b\"a\""
        ));
        assert!(!same_prelude_token(&Sort::new("Id"), "x", "y"));
    }
}
