//! Restricted declarative single-cell initializer parser tests.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, SyntaxErrorKind};

#[test]
fn empty_init_attribute_and_zero_argument_foo_initializer_are_accepted() {
    krs_syntax::InitAttribute::parse_source("").unwrap();
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "pub fn init() -> Self { \
         Self { k: k::configuration::KCell::new(k![model::Foo]) } \
         }",
    )
    .unwrap();
    assert!(initializer.variables().is_empty());
    assert_eq!(
        initializer
            .cell()
            .constructor()
            .segments
            .last()
            .unwrap()
            .ident,
        "new"
    );
    assert_eq!(initializer.cell().term().symbols().len(), 1);
    assert_eq!(
        initializer.cell().term().symbols()[0]
            .path()
            .segments
            .last()
            .unwrap()
            .ident,
        "Foo"
    );

    let candidates = initializer.reference_candidates().unwrap();
    assert_eq!(candidates.len(), 3);
    assert_eq!(candidates[0].path_spelling(), "Self");
    assert_eq!(
        candidates[1].path_spelling(),
        "k::configuration::KCell::new"
    );
    assert_eq!(candidates[2].path_spelling(), "model::Foo");
}

#[test]
fn one_main_variable_preserves_parameter_body_and_resolution_candidates() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(\
            #[k::config_var(name = \"PGM\", main)]\
            program: k::Term<dyn model::KItem>,\
         ) -> Self {\
            Self { k: KCell::new(k![program]) }\
         }",
    )
    .unwrap();
    assert_eq!(initializer.variables().len(), 1);
    let variable = &initializer.variables()[0];
    assert_eq!(variable.binding(), "program");
    assert_eq!(variable.attribute().name().value(), "PGM");
    assert!(variable.term_sort().is_dynamic());

    let roles = initializer
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(roles[0], ProvenanceRole::InitializerDeclaration);
    assert_eq!(roles[1], ProvenanceRole::InitializerResultType);
    assert_eq!(roles[2], ProvenanceRole::ConfigurationVariable);
    assert_eq!(roles[3], ProvenanceRole::ConfigurationVariableName);
    assert_eq!(roles[4], ProvenanceRole::ConfigurationVariableType);
    assert!(roles.contains(&ProvenanceRole::InitializerBody));
    assert!(roles.contains(&ProvenanceRole::InitializerTermPath));

    let candidates = initializer.reference_candidates().unwrap();
    let paths = candidates
        .iter()
        .map(krs_syntax::ReferenceCandidate::path_spelling)
        .collect::<Vec<_>>();
    assert_eq!(paths, ["Self", "model::KItem", "KCell::new"]);
    assert!(!paths.iter().any(|path| path == "program"));
}

#[test]
fn main_variable_accepts_a_declared_open_syntax_sort() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(\
            #[k::config_var(name = \"PGM\", main)]\
            program: k::Term<dyn model::Expr>,\
         ) -> Self {\
            Self { k: KCell::new(k![program]) }\
         }",
    )
    .unwrap();
    let variable = &initializer.variables()[0];
    assert!(variable.term_sort().is_dynamic());
    assert_eq!(
        variable.term_sort().sort().segments.last().unwrap().ident,
        "Expr"
    );
    let candidates = initializer.reference_candidates().unwrap();
    assert_eq!(candidates[1].path_spelling(), "model::Expr");
}

#[test]
fn readable_initializer_infers_variables_wrappers_and_main_input() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(pgm: model::Stmt, env: builtin::Map<builtin::Id, model::Value>) -> Self {\
             Self { k: k![pgm], env }\
         }",
    )
    .unwrap();
    assert_eq!(initializer.variables().len(), 2);
    let pgm = &initializer.variables()[0];
    assert_eq!(pgm.binding(), "pgm");
    assert_eq!(pgm.attribute().name().value(), "PGM");
    assert!(pgm.attribute().has_inferred_name());
    assert!(pgm.attribute().is_main());
    assert!(pgm.attribute().has_inferred_main());
    let env = &initializer.variables()[1];
    assert_eq!(env.attribute().name().value(), "ENV");
    assert!(!env.attribute().is_main());

    assert!(initializer.cells()[0].has_inferred_constructor());
    assert!(initializer.cells()[1].has_inferred_constructor());
    let candidates = initializer
        .reference_candidates()
        .unwrap()
        .into_iter()
        .map(|candidate| candidate.path_spelling())
        .collect::<Vec<_>>();
    assert_eq!(candidates, ["Self", "model::Stmt", "builtin::Map"]);

    let roles = initializer
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(
        roles
            .iter()
            .filter(|role| **role == ProvenanceRole::ConfigurationVariableName)
            .count(),
        2
    );
    assert!(roles.contains(&ProvenanceRole::ConfigurationVariableMain));
    assert_eq!(
        roles
            .iter()
            .filter(|role| **role == ProvenanceRole::InitializerCellConstructor)
            .count(),
        2
    );
}

#[test]
fn readable_initializer_honors_name_override_and_rejects_ambiguous_main() {
    let overridden = krs_syntax::InitializerFunction::parse_source(
        "fn init(#[renamed::config_var(name = \"SOURCE\")] pgm: Stmt) -> Self {\
             Self { k: renamed::k![pgm] }\
         }",
    )
    .unwrap();
    let variable = &overridden.variables()[0];
    assert_eq!(variable.attribute().name().value(), "SOURCE");
    assert!(!variable.attribute().has_inferred_name());
    assert!(variable.attribute().has_inferred_main());

    let error = krs_syntax::InitializerFunction::parse_source(
        "fn init(first: Stmt, second: Stmt) -> Self { Self { k: k![first, second] } }",
    )
    .unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::AmbiguousMainConfigurationVariable
    ));
}

#[test]
fn initializer_rejects_empty_and_repeated_fields_at_field_tokens() {
    let missing =
        krs_syntax::InitializerFunction::parse_source("fn init() -> Self { Self {} }").unwrap_err();
    assert!(matches!(
        missing.kind(),
        SyntaxErrorKind::UnsupportedInitializerBody { .. }
    ));

    let repeated_source =
        "fn init() -> Self { Self { k: KCell::new(k![Foo]), k: KCell::new(k![Bar]) } }";
    let repeated = krs_syntax::InitializerFunction::parse_source(repeated_source).unwrap_err();
    assert!(matches!(
        repeated.kind(),
        SyntaxErrorKind::DuplicateConfigurationField { .. }
    ));
    assert_eq!(
        repeated.span().start().column,
        repeated_source.rfind("k:").unwrap()
    );
}

#[test]
fn host_statements_control_flow_mutation_calls_and_early_return_are_rejected() {
    let cases = [
        "fn init() -> Self { let x = Foo; Self { k: KCell::new(k![x]) } }",
        "fn init() -> Self { if flag { Self { k: KCell::new(k![Foo]) } } else { Self { k: KCell::new(k![Bar]) } } }",
        "fn init() -> Self { return Self { k: KCell::new(k![Foo]) }; }",
        "fn init() -> Self { Self { k: make_cell() } }",
        "fn init() -> Self { Self { k: KCell::new(other![Foo]) } }",
        "fn init() -> Self { Self { k: KCell::new(k![lhs + rhs]) } }",
        "fn init() -> Self { Self { k: KCell::new(k![Foo]), ..base } }",
    ];
    for source in cases {
        let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedInitializerBody { .. }
                | SyntaxErrorKind::UnsupportedTermExpression { .. }
        ));
    }
}

#[test]
fn unsupported_signatures_variables_and_ambiguous_main_are_rejected_locally() {
    let ambiguous_source = "fn init(\
         #[k::config_var(name = \"ONE\", main)] one: Term<dyn KItem>,\
         #[k::config_var(name = \"TWO\", main)] two: Term<dyn KItem>\
         ) -> Self { Self { k: KCell::new(k![one]) } }";
    let ambiguous = krs_syntax::InitializerFunction::parse_source(ambiguous_source).unwrap_err();
    assert!(matches!(
        ambiguous.kind(),
        SyntaxErrorKind::AmbiguousMainConfigurationVariable
    ));
    assert_eq!(
        ambiguous.span().start().column,
        ambiguous_source.rfind("main").unwrap()
    );

    let cases = [
        "fn build() -> Self { Self { k: KCell::new(k![Foo]) } }",
        "fn init(&self) -> Self { Self { k: KCell::new(k![Foo]) } }",
        "async fn init() -> Self { Self { k: KCell::new(k![Foo]) } }",
        "fn init<T>() -> Self { Self { k: KCell::new(k![Foo]) } }",
        "fn init() -> Machine { Self { k: KCell::new(k![Foo]) } }",
        "fn init(#[k::config_var(name = \"PGM\", main, parser = \"X\")] program: Term<dyn KItem>) -> Self { Self { k: KCell::new(k![program]) } }",
        "fn init(#[k::config_var(name = \"PGM\", name = \"OTHER\", main)] program: Term<dyn KItem>) -> Self { Self { k: KCell::new(k![program]) } }",
    ];
    for source in cases {
        let error = krs_syntax::InitializerFunction::parse_source(source).unwrap_err();
        assert!(matches!(
            error.kind(),
            SyntaxErrorKind::UnsupportedInitializerSignature { .. }
                | SyntaxErrorKind::UnsupportedConfigurationVariable { .. }
                | SyntaxErrorKind::MissingArgument { .. }
                | SyntaxErrorKind::DuplicateArgument { .. }
                | SyntaxErrorKind::UnknownArgument { .. }
        ));
    }
}

#[test]
fn init_marker_rejects_payload_at_first_token() {
    let error = krs_syntax::InitAttribute::parse_source("unexpected").unwrap_err();
    assert!(matches!(
        error.kind(),
        SyntaxErrorKind::UnexpectedAttributePayload { attribute: "init" }
    ));
    assert_eq!(error.span().start().column, 0);
}
