use crate::{
    InputAddress, InputSpace, NativeNodePlace, SentenceNodeRole, adapt_definition,
    test_fixtures::smoke_definition,
};

#[test]
fn native_code_spellings_forward_the_upstream_stable_spelling() {
    use k_rust::diagnostic::DiagnosticCode;
    use krs_diagnostic::codes::CodeKind;

    for (code, expected, kind) in [
        (
            DiagnosticCode::CellCollectionVarWithoutInitial,
            "CellCollectionVarWithoutInitial",
            CodeKind::Author,
        ),
        (
            DiagnosticCode::DuplicateKLabel,
            "DuplicateKLabel",
            CodeKind::Internal,
        ),
        (
            DiagnosticCode::InvalidIoStream,
            "InvalidIoStream",
            CodeKind::Internal,
        ),
        (
            DiagnosticCode::UndefinedSort,
            "UndefinedSort",
            CodeKind::Internal,
        ),
        (
            DiagnosticCode::UnusedSymbol,
            "UnusedSymbol",
            CodeKind::Author,
        ),
        (
            DiagnosticCode::TermTooDeep,
            "TermTooDeep",
            CodeKind::Environment,
        ),
    ] {
        let mapped = super::native_diagnostic_code(code);
        assert_eq!(mapped.as_str(), expected);
        assert_eq!(mapped.kind(), kind, "{expected}");
    }
    for &code in DiagnosticCode::ALL {
        let mapped = super::native_diagnostic_code(code);
        assert_eq!(mapped.as_str(), code.as_str());
        assert!(
            !krs_diagnostic::codes::REGISTRY
                .iter()
                .any(|entry| entry.code.as_str() == mapped.as_str())
        );
    }
}

#[test]
fn a_native_codes_kind_follows_who_wrote_the_sentence_it_names() {
    use k_rust::diagnostic::{Diagnostic, DiagnosticCode, Severity};
    use krs_diagnostic::codes::CodeKind;

    use crate::{OriginMapping, SentenceProducer, test_fixtures::node};

    let mapping = |index, producer| OriginMapping {
        key: node("diag.sentence").key().clone(),
        origin: node("diag.sentence"),
        module: "DIAG".to_owned(),
        place: NativeNodePlace::Sentence {
            index,
            role: SentenceNodeRole::Sentence,
        },
        producer,
    };
    let origins = [
        mapping(0, SentenceProducer::Lowered),
        mapping(1, SentenceProducer::Raw),
    ];
    for (code, sentence, kind) in [
        (DiagnosticCode::UnboundVariable, Some(1), CodeKind::Author),
        (DiagnosticCode::UnboundVariable, Some(0), CodeKind::Internal),
        (DiagnosticCode::TermTooDeep, Some(1), CodeKind::Environment),
        (
            DiagnosticCode::UnadmittedHookNamespace,
            None,
            CodeKind::Author,
        ),
        (DiagnosticCode::UndefinedSort, None, CodeKind::Internal),
    ] {
        let mut frontend = super::FrontendDiagnostic::from(&Diagnostic {
            severity: Severity::Error,
            code,
            message: String::new(),
            source: None,
            location: None,
            input_addresses: sentence
                .map(|index| InputAddress::new(InputSpace::Structured, "DIAG", index))
                .into_iter()
                .collect(),
        });
        super::attribute_diagnostics(&origins, std::slice::from_mut(&mut frontend));
        assert_eq!(frontend.code.as_str(), code.as_str());
        assert_eq!(frontend.code.kind(), kind, "{code} at {sentence:?}");
        assert_eq!(frontend.source_map_key.is_some(), sentence.is_some());
    }

    // A diagnostic about a sentence derived from both a lowered and a raw sentence: the
    // author's K is involved, so it is the author's, and the first address locates it.
    let mut merged = super::FrontendDiagnostic::from(&Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::UnboundVariable,
        message: String::new(),
        source: None,
        location: None,
        input_addresses: vec![
            InputAddress::new(InputSpace::Structured, "DIAG", 0),
            InputAddress::new(InputSpace::Structured, "DIAG", 1),
        ],
    });
    super::attribute_diagnostics(&origins, std::slice::from_mut(&mut merged));
    assert_eq!(merged.code.kind(), CodeKind::Author);
    assert_eq!(merged.source_map_key, Some(origins[0].key.clone()));
}

#[test]
fn native_advice_is_given_in_krs_terms() {
    use k_rust::diagnostic::{Diagnostic, DiagnosticCode, Severity};
    use krs_diagnostic::ToDiagnostic;

    let native = |code, message: &str| {
        super::FrontendDiagnostic::from(&Diagnostic {
            severity: Severity::Warning,
            code,
            message: message.to_owned(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        })
    };
    let hook = native(
        DiagnosticCode::UnadmittedHookNamespace,
        "hook namespace `KRYPTO` of `hook(KRYPTO.sha256raw)` is neither builtin nor selected with --hook-namespaces; the production compiles as an unhooked function",
    );
    assert_eq!(hook.help.len(), 1);
    assert!(hook.help[0].starts_with("KRS has no `--hook-namespaces`"));
    assert_eq!(hook.to_diagnostic().help, hook.help);

    let cell = native(
        DiagnosticCode::CellCollectionVarWithoutInitial,
        "Configuration variable found in declaration of collection cell <account>. Implicitly, this causes the initial configuration to start with one <account> element instead of zero. Add the `initial=\"\"` attribute to make that behavior explicit.",
    );
    assert!(cell.help.is_empty());
}

fn native_diagnostic_for_test() -> super::FrontendDiagnostic {
    super::FrontendDiagnostic {
        severity: super::DiagnosticSeverity::Error,
        code: krs_diagnostic::Code::foreign(
            "UndefinedKLabel",
            krs_diagnostic::codes::CodeKind::Internal,
        ),
        message: "label missing is undefined".to_owned(),
        source: Some("native-definition".to_owned()),
        location: Some(super::SourceLocation {
            start_line: 2,
            start_column: 3,
            end_line: 2,
            end_column: 8,
        }),
        source_map_key: None,
        input_addresses: Vec::new(),
        help: Vec::new(),
    }
}

#[test]
fn native_diagnostics_retain_authored_keys_and_generated_coordinates() {
    use krs_diagnostic::{Location, Severity, ToDiagnostic};

    let ir = smoke_definition();
    let adapted = adapt_definition(&ir).unwrap();
    let mapping = adapted
        .origins()
        .iter()
        .find(|mapping| {
            matches!(
                mapping.place,
                NativeNodePlace::Sentence {
                    role: SentenceNodeRole::Sentence,
                    ..
                }
            )
        })
        .unwrap();
    let NativeNodePlace::Sentence { index, .. } = mapping.place else {
        unreachable!()
    };
    let mut frontend = native_diagnostic_for_test();
    frontend.severity = super::DiagnosticSeverity::Warning;
    frontend.input_addresses.push(InputAddress::new(
        InputSpace::Structured,
        &mapping.module,
        u32::try_from(index).unwrap(),
    ));
    super::attribute_diagnostics(adapted.origins(), std::slice::from_mut(&mut frontend));
    assert_eq!(frontend.source_map_key, Some(mapping.key.clone()));
    let diagnostic = frontend.to_diagnostic();
    assert_eq!(diagnostic.severity, Severity::Warning);
    assert!(matches!(diagnostic.primary.location, Location::Definition(key) if key == mapping.key));
    assert!(
        matches!(&diagnostic.secondary[0].location, Location::Generated(range)
        if range.artifact == "native-definition" && range.start_line == 2
            && range.start_column == 3 && range.end_line == 2 && range.end_column == 8)
    );

    frontend.input_addresses[0] = InputAddress::new(
        InputSpace::Compile,
        &mapping.module,
        u32::try_from(index).unwrap(),
    );
    super::attribute_diagnostics(adapted.origins(), std::slice::from_mut(&mut frontend));
    assert!(frontend.source_map_key.is_none());
    let unlocated = frontend.to_diagnostic();
    assert!(matches!(unlocated.primary.location, Location::None));
    assert_eq!(unlocated.secondary.len(), 1);
}

#[test]
fn compile_error_fallback_names_every_diagnostic_and_preserves_source() {
    use std::error::Error;

    let mut second = native_diagnostic_for_test();
    second.code =
        krs_diagnostic::Code::foreign("UndefinedSort", krs_diagnostic::codes::CodeKind::Internal);
    second.message = "sort Missing is undefined".to_owned();
    let native = k_rust::kompile::CompileError {
        stage: "definition checks",
        message: "definition rejected".to_owned(),
        diagnostics: Vec::new(),
    };
    let compile = super::CompileError {
        diagnostics: vec![native_diagnostic_for_test(), second],
        source: Box::new(native.clone()),
    };
    assert!(
        compile
            .to_string()
            .contains("UndefinedKLabel: label missing is undefined")
    );
    let error = super::DefinitionCompileError::Compile(compile);
    assert_eq!(
        error.to_string(),
        "native frontend stage definition checks failed: definition rejected\nUndefinedKLabel: label missing is undefined\nUndefinedSort: sort Missing is undefined"
    );
    assert_eq!(error.diagnostics().len(), 2);
    let super::DefinitionCompileError::Compile(compile) = &error else {
        unreachable!()
    };
    assert_eq!(compile.source.as_ref(), &native);
    assert!(error.source().unwrap().source().is_some());
}

#[test]
fn preparation_and_reparse_errors_preserve_typed_details() {
    use k_rust::diagnostic::{Diagnostic, DiagnosticCode, Severity};

    let native = k_rust::outer::LoadError::SourceDiagnostics(vec![Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::UndefinedSort,
        message: "sort Missing is undefined".to_owned(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }]);
    let preparation = super::DefinitionCompileError::Preparation(native.clone().into());
    assert!(
        preparation
            .to_string()
            .contains("UndefinedSort: sort Missing is undefined")
    );
    assert_eq!(preparation.diagnostics().len(), 1);
    let super::DefinitionCompileError::Preparation(super::PreparationError::Loader {
        error, ..
    }) = preparation
    else {
        unreachable!()
    };
    assert_eq!(*error, native);

    let parse = k_rust::kore::parser::ParseError {
        offset: 17,
        message: "expected module".to_owned(),
    };
    let reparse = super::DefinitionCompileError::KoreReparse {
        artifact: "definition.kore",
        error: parse.clone(),
    };
    assert_eq!(
        reparse.to_string(),
        "pinned parser rejected definition.kore: expected module at byte 17"
    );
    let super::DefinitionCompileError::KoreReparse { error, .. } = reparse else {
        unreachable!()
    };
    assert_eq!(error, parse);
}
