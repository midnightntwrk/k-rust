use crate::{
    InputAddress, InputSpace, NativeNodePlace, SentenceNodeRole, adapt_definition,
    test_fixtures::smoke_definition,
};

#[test]
fn native_code_spellings_match_the_pinned_wire_names() {
    use k_rust::diagnostic::DiagnosticCode;

    for (code, expected) in [
        (
            DiagnosticCode::CellCollectionVarWithoutInitial,
            "CellCollectionVarWithoutInitial",
        ),
        (DiagnosticCode::DuplicateKLabel, "DuplicateKLabel"),
        (DiagnosticCode::InvalidIoStream, "InvalidIoStream"),
        (DiagnosticCode::UndefinedSort, "UndefinedSort"),
        (DiagnosticCode::UnusedSymbol, "UnusedSymbol"),
    ] {
        let mapped = super::native_diagnostic_code(code);
        assert_eq!(mapped.as_str(), expected);
        assert_eq!(mapped.as_str(), format!("{code:?}"));
        assert!(
            !krs_diagnostic::codes::REGISTRY
                .iter()
                .any(|entry| entry.code == mapped)
        );
    }
}

fn native_diagnostic_for_test() -> super::FrontendDiagnostic {
    super::FrontendDiagnostic {
        severity: super::DiagnosticSeverity::Error,
        code: krs_diagnostic::Code::foreign("UndefinedKLabel"),
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
    super::resolve_diagnostic_keys(adapted.origins(), std::slice::from_mut(&mut frontend));
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
    super::resolve_diagnostic_keys(adapted.origins(), std::slice::from_mut(&mut frontend));
    assert!(frontend.source_map_key.is_none());
    let unlocated = frontend.to_diagnostic();
    assert!(matches!(unlocated.primary.location, Location::None));
    assert_eq!(unlocated.secondary.len(), 1);
}

#[test]
fn compile_error_fallback_names_every_diagnostic_and_preserves_source() {
    use std::error::Error;

    let mut second = native_diagnostic_for_test();
    second.code = krs_diagnostic::Code::foreign("UndefinedSort");
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
