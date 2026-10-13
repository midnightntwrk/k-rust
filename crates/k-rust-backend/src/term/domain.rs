//! The construction contract of domain values: a domain value's text is its identity, so every
//! value the backend holds is built by [`Term::domain_value_of`] with the kind of its sort, its
//! text validated for that kind and stored in the kind's canonical text.
//!
//! This module holds what the routes share: the validator of a text for a kind
//! ([`validate_text`]), and the checks that a construction's kind is the one the definition gives
//! the value's sort. Those checks are:
//! - the hook evaluation entry records the constructions a hook makes ([`BuiltDomainValues`]) and
//!   compares each kind with the definition's in every build, because a definition may declare a
//!   builtin hook at a sort whose hook gives another kind, and the hook's value is then no value
//!   of the application's sort;
//! - under a definition scope ([`DomainScope`]), opened by the backend's entry points, a debug
//!   build asserts at every other construction that the definition gives the sort no other kind,
//!   and that the text is a fixed point of the kind's canonicalizer.
//!
//! Neither check walks a term: each construction is checked where it happens.

use std::cell::{Cell, RefCell};
#[cfg(debug_assertions)]
use std::{collections::BTreeMap, sync::Arc};

use k_rust_kore::kore::ast::KoreString;
use k_rust_kore::names::BuiltinSort;

use super::{
    DomainKind, MIntLiteral, MIntWidth, Sort, Term, TermKind, mint_width_beyond_bound,
    mint_width_digits,
};
use crate::definition::{BackendDefinition, InvalidDomainValueReason};
#[cfg(debug_assertions)]
use crate::{definition::SortInfo, term::Name};

/// Why a text is no domain value of a kind at a sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TextRejection {
    /// The text names no element of the sort: it is outside the kind's literal syntax, a
    /// machine-integer suffix names another width or the sort names none, or a `Bytes` code
    /// point is above U+00FF.
    NamesNoElement(InvalidDomainValueReason),
    /// The text names an element whose canonical text k-rust declines to compute: a negative
    /// machine-integer literal of a width beyond `MAX_INT_RESULT_BITS`.
    BeyondBound,
}

/// Whether `value` is a domain value of `kind` at `sort`: the validator every construction route
/// with a text from outside the backend applies before [`Term::domain_value_of`] (definition load
/// and requests, `STRING.string2token`).
///
/// - `Int`: a decimal integer, with an optional sign.
/// - `Bool`: `true` or `false`.
/// - `MInt(W)`: a literal `[+-]?[0-9]+[pP][0-9]+` whose suffix names the sort's width; a sort
///   that names no width has no literal.
/// - `Bytes`: any payload at `SortBytes`, whose payload is one byte per code point; elsewhere the
///   UTF-8 of code points each at most U+00FF, since a larger code point names no byte.
/// - `String` and `Token`: every text.
pub(crate) fn validate_text(
    kind: DomainKind,
    sort: &Sort,
    value: &KoreString,
) -> Result<(), TextRejection> {
    let text = value.as_utf8().ok();
    let no_element = |reason| Err(TextRejection::NamesNoElement(reason));
    match kind {
        DomainKind::Int if !text.is_some_and(is_decimal_integer) => {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::Bool if !matches!(text, Some("true" | "false")) => {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::MInt(width) => {
            let digits = match (width, mint_width_digits(sort)) {
                (MIntWidth::Bits(_) | MIntWidth::Unrepresentable, Some(digits)) => digits,
                _ => return no_element(InvalidDomainValueReason::NoWidth),
            };
            let Some(literal) = text.and_then(MIntLiteral::parse) else {
                return no_element(InvalidDomainValueReason::NotALiteral);
            };
            if !literal.names_width(digits) {
                return no_element(InvalidDomainValueReason::OtherWidth);
            }
            if literal.is_negative() && mint_width_beyond_bound(width) {
                return Err(TextRejection::BeyondBound);
            }
            Ok(())
        }
        DomainKind::Bytes
            if !sort.is_builtin(BuiltinSort::Bytes)
                && !text
                    .is_some_and(|text| text.chars().all(|character| character <= '\u{ff}')) =>
        {
            no_element(InvalidDomainValueReason::NotALiteral)
        }
        DomainKind::Int
        | DomainKind::Bool
        | DomainKind::Bytes
        | DomainKind::String
        | DomainKind::Token => Ok(()),
    }
}

/// A decimal integer with an optional sign, the literal syntax of `INT.Int`.
pub(crate) fn is_decimal_integer(value: &str) -> bool {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value).as_bytes();
    !digits.is_empty() && digits.iter().all(u8::is_ascii_digit)
}

std::thread_local! {
    /// Whether a [`BuiltDomainValues`] records this thread's constructions.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// The constructions recorded, each with the kind it was built with.
    static BUILT: RefCell<Vec<(Term, DomainKind)>> = const { RefCell::new(Vec::new()) };
}

/// The domain values built on this thread while this record is alive, each with the kind it was
/// built with, for the hook evaluation entry: a hook's value is a value of the application's
/// sort only if every domain value the hook built has the kind its sort has in the definition.
/// A record nested in another keeps the outer one's entries and drops its own when it ends.
pub(crate) struct BuiltDomainValues {
    start: usize,
    outer: bool,
}

impl BuiltDomainValues {
    pub(crate) fn record() -> Self {
        let outer = RECORDING.replace(true);
        let start = BUILT.with_borrow(Vec::len);
        Self { start, outer }
    }

    /// True when every domain value built since [`Self::record`] has the kind `definition`
    /// gives its sort.
    pub(crate) fn of_their_sorts_kinds(&self, definition: &BackendDefinition) -> bool {
        BUILT.with_borrow(|built| {
            built[self.start..].iter().all(|(term, kind)| {
                matches!(term.kind(), TermKind::DomainValue { sort, .. }
                    if definition.domain_kind(sort) == Some(*kind))
            })
        })
    }
}

impl Drop for BuiltDomainValues {
    fn drop(&mut self) {
        RECORDING.set(self.outer);
        BUILT.with_borrow_mut(|built| built.truncate(self.start));
    }
}

#[cfg(debug_assertions)]
std::thread_local! {
    /// The sorts of the definitions whose scopes are open on this thread, innermost last.
    static SCOPES: RefCell<Vec<Arc<BTreeMap<Name, SortInfo>>>> = const { RefCell::new(Vec::new()) };
}

/// A backend entry point's definition scope: while it is open, a debug build checks every
/// construction outside a hook evaluation against the definition (the module documentation).
/// Opened beside `rule::ApartScope` by the simplification, rewrite, execution, proof and
/// critical-pair entry points; a release build keeps nothing.
pub(crate) struct DomainScope(());

impl DomainScope {
    pub(crate) fn enter(definition: &BackendDefinition) -> Self {
        #[cfg(debug_assertions)]
        SCOPES.with_borrow_mut(|scopes| scopes.push(Arc::clone(definition.sort_table())));
        #[cfg(not(debug_assertions))]
        let _ = definition;
        Self(())
    }
}

impl Drop for DomainScope {
    fn drop(&mut self) {
        #[cfg(debug_assertions)]
        SCOPES.with_borrow_mut(|scopes| {
            scopes.pop();
        });
    }
}

/// Note the construction of `term`, a domain value built with `kind`: record it for the hook
/// evaluation entry, or check it against the innermost definition scope in a debug build.
pub(super) fn note_construction(term: &Term, kind: DomainKind) {
    if RECORDING.get() {
        BUILT.with_borrow_mut(|built| built.push((term.clone(), kind)));
        return;
    }
    #[cfg(debug_assertions)]
    debug_check(term, kind);
}

/// The definition of the innermost scope gives the value's sort no other kind than `kind`, and
/// the stored text is a fixed point of `kind`'s canonicalizer. A sort the definition gives no
/// kind (undeclared, or without domain values) is no carrier of the definition, so it holds no
/// value whose identity another text could share.
#[cfg(debug_assertions)]
fn debug_check(term: &Term, kind: DomainKind) {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return;
    };
    SCOPES.with_borrow(|scopes| {
        let Some(sorts) = scopes.last() else {
            return;
        };
        let declared = crate::definition::domain_kind_in(sorts, sort);
        debug_assert!(
            declared.is_none_or(|declared| declared == kind),
            "a domain value of {sort:?} built with the kind {kind:?}, where the definition gives \
             the sort the kind {declared:?}"
        );
        debug_assert!(
            super::canonical_text(kind, sort, value.clone()) == *value,
            "the domain value {value:?} of {sort:?} is not in the canonical text of {kind:?}"
        );
    });
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, fs, path::Path};

    use k_rust_kore::kore::parser::parse_definition;

    use super::*;

    /// Every construction route of a domain value, as `(file, calls of domain_value_of(,
    /// value uses of TermKind::DomainValue {)` outside test code, with the source of each
    /// route's kind. A new route fails `every_domain_value_is_built_by_a_listed_route` until it
    /// is listed here with its kind source.
    const ROUTES: &[(&str, usize, usize)] = &[
        // `Term::int`, `Term::bool`, `Term::string`, `Term::bytes`: the constant kind of their
        // builtin-named sort (`SortInt` and `SortBool` by name, `SortString` and `SortBytes` the
        // builtin hook's own sort). `domain_value_of` itself builds the node; the raw test
        // constructor and the drop sentinel (no value of any sort) build one without a kind.
        ("term.rs", 4, 3),
        // Internalization of `\dv` and of a KORE string literal, and
        // `BackendDefinition::domain_value`: `domain_kind` of the sort.
        ("definition.rs", 3, 0),
        // `STRING.string2token`: `domain_kind` of the result sort; `STRING.token2string`: the
        // constant `String` kind of its result.
        ("builtin/string.rs", 2, 0),
        // `float_term`: the constant kind of `SortFloat` (`Token` until Float values have a kind
        // of their own).
        ("builtin/float.rs", 1, 0),
        // KVar renaming: `domain_kind` of the token's sort, read with the definition's KVar
        // sorts (`KVarSorts`).
        ("builtin/substitution.rs", 1, 0),
        // The externalized Boolean literal: `domain_kind` of the sort hooked `BOOL.Bool`.
        ("externalize.rs", 1, 0),
        // The SMT model reader: the `Int` and `Bool` kinds of its translation, when the
        // definition gives `SortInt` and `SortBool` those kinds.
        ("smt/z3.rs", 2, 0),
    ];

    /// The non-test source of `text`: everything before its test module.
    fn non_test_source(text: &str) -> &str {
        text.find("#[cfg(test)]\nmod tests")
            .map_or(text, |end| &text[..end])
    }

    fn rust_files(directory: &Path, found: &mut Vec<std::path::PathBuf>) {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name == "tests") {
                    continue;
                }
                rust_files(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found.push(path);
            }
        }
    }

    /// The source scan of `shared_domain_value_contract` C5: every call of `domain_value_of(`
    /// and every value use of `TermKind::DomainValue {` (as the argument of a constructor) in the
    /// backend's non-test code is a route of [`ROUTES`].
    #[test]
    fn every_domain_value_is_built_by_a_listed_route() {
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut files = Vec::new();
        rust_files(&source, &mut files);
        let mut found = BTreeMap::<String, (usize, usize)>::new();
        for path in files {
            let relative = path
                .strip_prefix(&source)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            if relative.starts_with("builtin/hook_models") || relative == "term/domain.rs" {
                continue;
            }
            let text = fs::read_to_string(&path).unwrap();
            let code = non_test_source(&text)
                .lines()
                .filter(|line| !line.trim_start().starts_with("//"))
                .collect::<Vec<_>>()
                .join("\n");
            let calls = code.matches("domain_value_of(").count()
                - code.matches("fn domain_value_of(").count();
            let values = code.matches("new(TermKind::DomainValue {").count();
            if calls + values > 0 {
                found.insert(relative, (calls, values));
            }
        }
        let expected = ROUTES
            .iter()
            .map(|(file, calls, values)| ((*file).to_owned(), (*calls, *values)))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            found, expected,
            "a domain value is built outside the route table of term/domain.rs"
        );
    }

    /// The raw constructor exists only in test builds and with the test-only feature, which no
    /// normal build enables: its declaration carries that `cfg`, and the feature is not a
    /// default one.
    #[test]
    fn the_raw_constructor_exists_only_in_test_builds() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let term = fs::read_to_string(root.join("src/term.rs")).unwrap();
        let declaration = term
            .find("pub fn raw_domain_value(")
            .expect("the raw constructor is declared in term.rs");
        assert!(
            term[..declaration]
                .trim_end()
                .rsplit('\n')
                .take(3)
                .any(|line| line.trim() == r#"#[cfg(any(test, feature = "raw-domain-values"))]"#),
            "the raw constructor is not behind the test-only feature"
        );
        let manifest = fs::read_to_string(root.join("Cargo.toml")).unwrap();
        assert!(
            manifest
                .lines()
                .any(|line| line.trim() == "raw-domain-values = []"),
            "the feature raw-domain-values is not declared without dependencies"
        );
        assert!(
            !manifest
                .lines()
                .any(|line| line.trim_start().starts_with("default")
                    && line.contains("raw-domain-values")),
            "raw-domain-values is a default feature"
        );
    }

    fn definition(source: &str) -> BackendDefinition {
        let syntax = parse_definition(source).expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// Under a definition scope, a debug build refuses a construction whose kind is not the one
    /// the definition gives the sort: here a `Token` at a sort hooked `INT.Int`.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "built with the kind Token")]
    fn a_construction_with_another_kind_than_the_definitions_is_refused_in_a_scope() {
        let definition = definition(
            r#"[]
            module MAIN
                hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            endmodule []"#,
        );
        let _scope = DomainScope::enter(&definition);
        let _ = Term::domain_value_of(DomainKind::Token, Sort::simple("SortMyInt"), "07");
    }

    /// A sort the definition gives no kind holds no value of the definition, so a construction
    /// there is not refused; and a construction outside every scope is not checked.
    #[test]
    fn a_construction_at_a_sort_without_a_kind_is_not_refused() {
        let definition = definition(
            r#"[]
            module MAIN
                sort SortS{} []
            endmodule []"#,
        );
        {
            let _scope = DomainScope::enter(&definition);
            let _ = Term::bool(true);
        }
        let _ = Term::domain_value_of(DomainKind::Token, Sort::builtin(BuiltinSort::Int), "07");
    }

    #[test]
    fn texts_are_validated_by_kind() {
        let int = Sort::builtin(BuiltinSort::Int);
        let word = Sort::Application {
            name: "SortMInt".into(),
            arguments: vec![Sort::simple("Sort8")],
        };
        let wide = Sort::Application {
            name: "SortMInt".into(),
            arguments: vec![Sort::simple("Sort33554432")],
        };
        let renamed_bytes = Sort::simple("SortMyBytes");
        let bytes = Sort::builtin(BuiltinSort::Bytes);
        let no_element = |reason| Err::<(), _>(TextRejection::NamesNoElement(reason));
        let cases = [
            (DomainKind::Int, &int, KoreString::from("-07"), Ok(())),
            (
                DomainKind::Int,
                &int,
                KoreString::from("7a"),
                no_element(InvalidDomainValueReason::NotALiteral),
            ),
            (
                DomainKind::Bool,
                &int,
                KoreString::from("maybe"),
                no_element(InvalidDomainValueReason::NotALiteral),
            ),
            (
                DomainKind::MInt(MIntWidth::Bits(8)),
                &word,
                KoreString::from("-1p8"),
                Ok(()),
            ),
            (
                DomainKind::MInt(MIntWidth::Bits(8)),
                &word,
                KoreString::from("1p16"),
                no_element(InvalidDomainValueReason::OtherWidth),
            ),
            (
                DomainKind::MInt(MIntWidth::Bits(8)),
                &word,
                KoreString::from("abc"),
                no_element(InvalidDomainValueReason::NotALiteral),
            ),
            (
                DomainKind::MInt(MIntWidth::NoWidth),
                &word,
                KoreString::from("1p8"),
                no_element(InvalidDomainValueReason::NoWidth),
            ),
            (
                DomainKind::MInt(MIntWidth::Bits(33_554_432)),
                &wide,
                KoreString::from("-1p33554432"),
                Err(TextRejection::BeyondBound),
            ),
            (
                DomainKind::MInt(MIntWidth::Bits(33_554_432)),
                &wide,
                KoreString::from("1p33554432"),
                Ok(()),
            ),
            (
                DomainKind::Bytes,
                &renamed_bytes,
                KoreString::from("\u{ff}"),
                Ok(()),
            ),
            (
                DomainKind::Bytes,
                &renamed_bytes,
                KoreString::from("\u{100}"),
                no_element(InvalidDomainValueReason::NotALiteral),
            ),
            (
                DomainKind::Bytes,
                &bytes,
                KoreString::from(vec![0xff_u8, 0x00]),
                Ok(()),
            ),
            (
                DomainKind::String,
                &int,
                KoreString::from("anything"),
                Ok(()),
            ),
            (
                DomainKind::Token,
                &int,
                KoreString::from("anything"),
                Ok(()),
            ),
        ];
        for (kind, sort, value, expected) in cases {
            assert_eq!(
                validate_text(kind, sort, &value),
                expected,
                "{kind:?} {value:?}"
            );
        }
    }
}
