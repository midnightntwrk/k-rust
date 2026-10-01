use std::collections::{BTreeSet, HashSet};

use krs_ir::{PackageId, Sha256Digest, SourceFileId};

use super::*;

#[test]
fn registered_spellings_are_well_formed_and_unique() {
    let mut seen = BTreeSet::new();
    for info in codes::REGISTRY {
        let components: Vec<_> = info.code.as_str().split("::").collect();
        assert_eq!(components.len(), 3, "{}", info.code);
        assert_eq!(components[0], "krs");
        for component in &components[1..] {
            assert!(component.starts_with(|ch: char| ch.is_ascii_lowercase()));
            assert!(component.split('-').all(|word| {
                !word.is_empty()
                    && word
                        .bytes()
                        .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit())
            }));
        }
        assert!(seen.insert(info.code.as_str()), "duplicate {}", info.code);
        assert!(!info.summary.is_empty());
        assert!(!info.summary.contains(['\n', '\r']));
    }
    let stages = [
        codes::plan::CODES,
        codes::emit::CODES,
        codes::generate::CODES,
        codes::reference::CODES,
        codes::native::CODES,
        codes::collect::CODES,
        codes::analysis::CODES,
        codes::rust_expansion::CODES,
        codes::syntax::CODES,
        codes::expand::CODES,
        codes::policy::CODES,
    ];
    let stage_codes: BTreeSet<_> = stages.into_iter().flatten().map(Code::as_str).collect();
    assert_eq!(seen, stage_codes);
}

#[test]
fn registered_spellings_are_available_in_const_contexts() {
    const CODE: &Code = &codes::expand::PARSE;
    const PARSE: &str = CODE.as_str();
    assert_eq!(PARSE, codes::expand::PARSE.to_string());
    assert!(
        codes::REGISTRY
            .iter()
            .any(|info| info.code == codes::expand::PARSE)
    );
    assert!(
        codes::REGISTRY
            .iter()
            .any(|info| info.code == codes::policy::CFG)
    );
}

#[test]
fn foreign_codes_preserve_borrowed_and_owned_spellings_without_registration() {
    let borrowed = Code::foreign("E0412");
    let owned = Code::foreign(String::from("E0412"));
    assert_eq!(borrowed, owned);
    assert_eq!(borrowed.cmp(&owned), std::cmp::Ordering::Equal);
    assert_eq!(HashSet::from([borrowed.clone(), owned.clone()]).len(), 1);
    assert_eq!(owned.as_str(), "E0412");
    assert_eq!(borrowed.to_string(), "E0412");
    assert!(!codes::REGISTRY.iter().any(|info| info.code == owned));
    let native = Code::foreign(format!("Native{}", "ParseError"));
    assert_eq!(native.clone().as_str(), "NativeParseError");
}

#[test]
fn error_constructor_starts_with_only_a_primary_label() {
    let diagnostic = Diagnostic::error(codes::expand::PARSE, "invalid source", Location::None);
    assert_eq!(diagnostic.code, codes::expand::PARSE);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(diagnostic.message, "invalid source");
    assert!(matches!(diagnostic.primary.location, Location::None));
    assert!(diagnostic.primary.message.is_none());
    assert!(diagnostic.secondary.is_empty());
    assert!(diagnostic.notes.is_empty());
}

#[test]
fn builders_preserve_label_explanations_and_producer_order() {
    let first_key = SourceMapKey::new("definition.first").unwrap();
    let second_key = SourceMapKey::new("definition.second").unwrap();
    let diagnostic = Diagnostic::error(codes::policy::CFG, "rejected attribute", Location::None)
        .with_secondary(Label::new(Location::Definition(first_key.clone())).with_message("first"))
        .with_secondary(Label::new(Location::Definition(second_key.clone())))
        .with_note("first note")
        .with_note(String::from("second note"));
    assert_eq!(diagnostic.notes, ["first note", "second note"]);
    assert_eq!(diagnostic.secondary.len(), 2);
    assert_eq!(diagnostic.secondary[0].message.as_deref(), Some("first"));
    assert!(diagnostic.secondary[1].message.is_none());
    let Location::Definition(key) = &diagnostic.secondary[0].location else {
        panic!("first definition key lost");
    };
    assert_eq!(key, &first_key);
    let Location::Definition(key) = &diagnostic.secondary[1].location else {
        panic!("second definition key lost");
    };
    assert_eq!(key, &second_key);
}

#[test]
fn file_and_exact_source_locations_preserve_ir_coordinates() {
    let path = DisplayPath::new("src/lib.rs").unwrap();
    let bytes = ByteRange::new(3, 8).unwrap();
    let label = Label::new(Location::File {
        path: path.clone(),
        range: bytes,
    });
    let Location::File {
        path: actual,
        range,
    } = label.location
    else {
        panic!("file coordinates lost");
    };
    assert_eq!(actual, path);
    assert_eq!(range, bytes);

    let package = PackageId::new("example", "example", "0.1.0", "workspace").unwrap();
    let digest = Sha256Digest::new("0".repeat(64)).unwrap();
    let file = SourceFileId::new(package, path.as_str(), digest).unwrap();
    let range = SourceRange::from_byte_range(file, bytes).unwrap();
    let location = Location::Source(range.clone());
    let Location::Source(actual) = location.clone() else {
        panic!("source identity lost");
    };
    assert_eq!(actual, range);
}

#[cfg(feature = "proc-macro2")]
#[test]
fn macro_span_location_preserves_the_producer_span() {
    let tokens: proc_macro2::TokenStream = "identifier".parse().unwrap();
    let span = tokens.into_iter().next().unwrap().span();
    let diagnostic =
        Diagnostic::error(codes::expand::PARSE, "invalid source", Location::Span(span));
    let Location::Span(actual) = diagnostic.primary.location else {
        panic!("macro span lost");
    };
    assert_eq!(actual.byte_range(), span.byte_range());
}

#[test]
fn supplying_a_file_resolves_all_input_ranges_and_preserves_other_locations() {
    let path = DisplayPath::new("src/input.rs").unwrap();
    let existing_path = DisplayPath::new("src/other.rs").unwrap();
    let primary_range = ByteRange::new(3, 8).unwrap();
    let secondary_range = ByteRange::new(10, 15).unwrap();
    let diagnostic = Diagnostic::error(
        codes::syntax::INVALID_TRIVIA,
        "invalid source",
        Location::Range(primary_range),
    )
    .with_secondary(Label::new(Location::Range(secondary_range)).with_message("related"))
    .with_secondary(Label::new(Location::File {
        path: existing_path.clone(),
        range: secondary_range,
    }))
    .with_secondary(Label::new(Location::None))
    .with_secondary(Label::new(Location::Definition(
        SourceMapKey::new("definition.item").unwrap(),
    )))
    .with_file(&path);
    for (label, expected_path, expected_range) in [
        (&diagnostic.primary, &path, primary_range),
        (&diagnostic.secondary[0], &path, secondary_range),
        (&diagnostic.secondary[1], &existing_path, secondary_range),
    ] {
        let Location::File { path, range } = &label.location else {
            panic!("expected file coordinates");
        };
        assert_eq!(path, expected_path);
        assert_eq!(*range, expected_range);
    }
    assert_eq!(diagnostic.secondary[0].message.as_deref(), Some("related"));
    assert!(matches!(diagnostic.secondary[2].location, Location::None));
    assert!(matches!(
        diagnostic.secondary[3].location,
        Location::Definition(_)
    ));
}
