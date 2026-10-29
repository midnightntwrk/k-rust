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
            .unwrap()
            .constructor()
            .segments
            .last()
            .unwrap()
            .ident,
        "new"
    );
    assert_eq!(initializer.cell().unwrap().term().symbols().len(), 1);
    assert_eq!(
        initializer.cell().unwrap().term().symbols()[0]
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
    assert!(variable.term_sort().unwrap().is_dynamic());

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
    assert!(variable.term_sort().unwrap().is_dynamic());
    assert_eq!(
        variable
            .term_sort()
            .unwrap()
            .sort()
            .segments
            .last()
            .unwrap()
            .ident,
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
    assert_eq!(
        candidates,
        [
            "Self",
            "model::Stmt",
            "builtin::Map",
            "builtin::Id",
            "model::Value"
        ]
    );

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
        "fn init() -> Self { Self { k: KCell::new(k![*lhs]) } }",
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
fn documentation_lint_levels_and_cfg_stay_on_the_initializer() {
    let source = "/// Loads the program.\n\
         #[doc(alias = \"start\")]\n\
         #[allow(dead_code)] #[expect(unused_variables)] #[warn(missing_docs)]\n\
         #[deny(unused_mut)] #[cfg(feature = \"x\")]\n\
         fn init() -> Self { Self { k: KCell::new(k![Foo]) } }";
    let initializer = krs_syntax::InitializerFunction::parse_source(source).unwrap();
    let names: Vec<_> = initializer
        .item()
        .attrs
        .iter()
        .map(|attribute| attribute.path().get_ident().unwrap().to_string())
        .collect();
    assert_eq!(
        names,
        ["doc", "doc", "allow", "expect", "warn", "deny", "cfg"]
    );
}

#[test]
fn other_initializer_attributes_are_rejected_at_the_attribute() {
    for attribute in [
        "#[inline]",
        "#[must_use]",
        "#[forbid(unsafe_code)]",
        "#[cfg_attr(test, allow(dead_code))]",
        "#[clippy::cognitive_complexity]",
        "#[::doc = \"x\"]",
    ] {
        let source = format!(
            "/// Kept.\n{attribute}\nfn init() -> Self {{ Self {{ k: KCell::new(k![Foo]) }} }}"
        );
        let error = krs_syntax::InitializerFunction::parse_source(&source).unwrap_err();
        assert!(
            matches!(
                error.kind(),
                SyntaxErrorKind::UnsupportedInitializerSignature { .. }
            ),
            "{attribute}: {error:?}"
        );
        assert_eq!(error.span().start().line, 2, "{attribute}");
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

#[test]
fn optional_accessors_accept_direct_types_and_nonlegacy_cells() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(env: Map<Id, Value>) -> Self { Self { env: Cell::new(env) } }",
    )
    .unwrap();
    assert!(initializer.variables()[0].term_sort().is_none());
    assert!(initializer.cell().is_none());
    assert_eq!(
        initializer.reference_candidates().unwrap()[0].path_spelling(),
        "Self"
    );
}

#[test]
fn notation_for_a_builtin_call_is_a_readable_initializer_term() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(ready: Bool, cap: Int) -> Self {\
             Self { flag: ready && true, limit: cap.max::<Int>(0), k: k![Start(ready || false)] }\
         }",
    )
    .unwrap();
    for cell in &initializer.cells()[..2] {
        assert!(cell.has_inferred_constructor());
        let krs_syntax::InitializerCellContent::Leaf {
            value: krs_syntax::StateTerm::Term(term),
            ..
        } = cell.content()
        else {
            panic!("a notation cell is a leaf term");
        };
        assert_eq!(term.root_kind(), krs_syntax::TermRootKind::Call);
    }
    let error = krs_syntax::InitializerFunction::parse_source(
        "fn init() -> Self { Self { limit: cap.max(0) } }",
    )
    .unwrap_err();
    assert!(
        matches!(
            error.kind(),
            SyntaxErrorKind::InvalidExpressionNotation { .. }
        ),
        "{error}"
    );
}

/// A collection-typed configuration variable keeps its element types, in
/// either type form, with nested ones, each anchored in preorder across the
/// variables and offered for name resolution.
#[test]
fn configuration_variables_keep_their_element_types() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(\
            xs: List<Value>,\
            sets: k::Term<Map<Id, Set<Int>>>,\
            n: Int,\
         ) -> Self {\
            Self { stack: list::concat(xs, list::item(n)), seen: sets }\
         }",
    )
    .unwrap();
    let arguments = initializer
        .variables()
        .iter()
        .map(|variable| {
            krs_syntax::SortArgument::preorder(variable.arguments())
                .into_iter()
                .map(|argument| quote::ToTokens::to_token_stream(&argument.path).to_string())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        arguments,
        [vec!["Value"], vec!["Id", "Set", "Int"], Vec::<&str>::new()]
    );
    let anchors = initializer
        .provenance()
        .unwrap()
        .into_iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ConfigurationVariableTypeArgument)
        .map(|anchor| anchor.ordinal())
        .collect::<Vec<_>>();
    assert_eq!(anchors, [0, 1, 2, 3]);
    let candidates = initializer.reference_candidates().unwrap();
    let paths = candidates
        .iter()
        .map(krs_syntax::ReferenceCandidate::path_spelling)
        .collect::<Vec<_>>();
    assert_eq!(
        paths[..8],
        ["Self", "List", "Map", "Int", "Value", "Id", "Set", "Int"]
    );
}

/// The `k!` and `map!` structure anchors of one initializer name distinct
/// nodes: each role's ordinals run `0..n` across the cells, in cell order with
/// nested groups in place, so no two nodes share a provenance key.
#[test]
fn structure_anchors_are_numbered_across_the_initializer() {
    let initializer = krs_syntax::InitializerFunction::parse_source(
        "fn init(pgm: Stmt, n: Id, m: Map<Id, Value>) -> Self {
            Self {
                k: k::k![pgm, StmtSyntax::Tick()],
                slot: k::k![1, 2],
                env: k::map![],
                frame: Frame { fk: k::k![3], fenv: k::map![m[n <- 3]] },
                env2: k::map![m[n <- 2]],
            }
        }",
    )
    .unwrap();
    let anchors = initializer.provenance().unwrap();
    let mut keys = std::collections::BTreeSet::new();
    for anchor in &anchors {
        assert!(
            keys.insert((anchor.role(), anchor.ordinal())),
            "repeated key {:?} {}",
            anchor.role(),
            anchor.ordinal()
        );
    }
    for (role, count) in [
        (ProvenanceRole::KSequencePayload, 3),
        (ProvenanceRole::KSequenceItem, 5),
        (ProvenanceRole::MapPayload, 3),
        (ProvenanceRole::MapKey, 2),
        (ProvenanceRole::MapValue, 2),
        (ProvenanceRole::MapUpdateBase, 2),
    ] {
        let numbered = anchors
            .iter()
            .filter(|anchor| anchor.role() == role)
            .map(|anchor| {
                let start = anchor.range().start();
                (anchor.ordinal(), (start.line, start.column))
            })
            .collect::<Vec<_>>();
        let ordinals = numbered
            .iter()
            .map(|(ordinal, _)| *ordinal)
            .collect::<Vec<_>>();
        assert_eq!(ordinals, (0..count).collect::<Vec<u32>>(), "{role:?}");
        assert!(
            numbered.windows(2).all(|pair| pair[0].1 < pair[1].1),
            "{role:?} is not in source order: {numbered:?}"
        );
    }
}

/// An empty shell is an authored node whose text is its invocation: its
/// payload key is anchored there, path to closing delimiter, and numbered
/// with the payloads of the other shells of its role.
#[test]
fn empty_shells_are_keyed_at_their_invocation() {
    let source = "fn init(n: Id, e: Map) -> Self { Self { k: k::k![], env: k::map![], \
                  store: k::map![e; n <- 1], built: k::map![n -> 1] } }";
    let initializer = krs_syntax::InitializerFunction::parse_source(source).unwrap();
    let anchors = initializer.provenance().unwrap();
    let payloads = |role| {
        anchors
            .iter()
            .filter(|anchor| anchor.role() == role)
            .map(|anchor| {
                let (start, end) = (anchor.range().start(), anchor.range().end());
                assert_eq!((start.line, end.line), (1, 1));
                (anchor.ordinal(), &source[start.column..end.column])
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(payloads(ProvenanceRole::KSequencePayload), [(0, "k::k![]")]);
    // A map that writes entries is a collection literal, a term with no map payload.
    assert_eq!(
        payloads(ProvenanceRole::MapPayload),
        [(0, "k::map![]"), (1, "e; n <- 1")]
    );
}

/// Each literal of an initializer's terms is a node of its own: it is keyed
/// `initializer_term_literal`, anchored at its tokens and numbered in
/// preorder across the terms in expansion order (a term's whole value, an
/// argument, a `k!` item, a map key and value, an update's key and value,
/// a nested group's cells), whatever term holds it.
#[test]
fn literals_are_keyed_across_the_initializer_terms() {
    let source = "fn init(pgm: Stmt, m: Map<Int, Int>) -> Self { Self { \
        acc: 0, sum: int::add(2, -3), k: k::k![pgm, 7, Pair(true, \"s\")], \
        env: k::map![1 -> int::mul(4, 5.0)], frame: Frame { ret: 9 }, \
        env2: k::map![m[6 <- 8]] } }";
    let initializer = krs_syntax::InitializerFunction::parse_source(source).unwrap();
    let literals = initializer
        .provenance()
        .unwrap()
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::InitializerTermLiteral)
        .map(|anchor| {
            let (start, end) = (anchor.range().start(), anchor.range().end());
            assert_eq!((start.line, end.line), (1, 1));
            (anchor.ordinal(), &source[start.column..end.column])
        })
        .collect::<Vec<_>>();
    assert_eq!(
        literals,
        [
            (0, "0"),
            (1, "2"),
            (2, "-3"),
            (3, "7"),
            (4, "true"),
            (5, "\"s\""),
            (6, "1"),
            (7, "4"),
            (8, "5.0"),
            (9, "9"),
            (10, "6"),
            (11, "8"),
        ]
    );
}
