//! A compilation's provenance does not depend on the route its input took.
//!
//! `KRUST-PROVENANCE` bytes are a function of each receipt's normal form, never of which origin
//! sets or paths share memory. Decoding a document makes one allocation per table entry where
//! the compile that wrote it may have held several equal ones, so a compile of a decoded loaded
//! definition meets other allocations than a compile of the source; its documents must be
//! byte-identical all the same, which is what a consumer that hashes them across a prepared
//! base, or replays a recorded semantic input, relies on.

use k_rust::builtin::embedded;
use k_rust::definition::json;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{
    LoadOptions, LoadedDefinition, LoadedParts, ResolvedSource, load_with_options,
};

fn load(file: &str, source: &str, module: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new(file, source),
        module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").expect("the prelude is embedded")],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{file} does not load: {error:?}"))
}

/// The provenance documents of the unfiltered execution definition and the KORE of compiling
/// `loaded`.
fn compiled(loaded: &LoadedDefinition) -> (String, String) {
    let artifacts = compile_loaded_definition(loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the definition does not compile: {error:?}"));
    (
        json::to_provenance_string(&artifacts.execution_definition, loaded.source_table())
            .expect("the execution definition encodes"),
        artifacts.definition_kore,
    )
}

/// Compiling a loaded definition, and compiling the definition decoded from its document, give
/// byte-identical execution provenance (and KORE), for the configuration of a deep chain and a
/// wide sequence (configuration expansion, cell concretization and sort injection all
/// re-receipt their nodes) and for the repository's rewrite example.
#[test]
fn compiling_a_decoded_definition_writes_the_same_provenance() {
    let shape = |configuration: &str| {
        format!(
            r#"module MAIN-SYNTAX
  imports INT-SYNTAX
  syntax E ::= Int | E "+" E [left, symbol(plus)]
  syntax KItem ::= foo(E) [symbol(foo)]
endmodule
module MAIN
  imports MAIN-SYNTAX
  imports INT
  configuration <k> $PGM:K </k> <c> {configuration} </c>
  rule <k> foo(0) => .K </k>
endmodule
"#
        )
    };
    let chain = (0..30)
        .map(|operand| (operand % 10).to_string())
        .collect::<Vec<_>>()
        .join(" + ");
    let sequence = (0..30)
        .map(|operand| format!("foo({})", operand % 10))
        .collect::<Vec<_>>()
        .join(" ~> ");
    let rewrite = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/rewrite.k"),
    )
    .expect("the rewrite example is readable");
    for (file, source, module) in [
        ("chain.k", shape(&format!("foo({chain})")), "MAIN"),
        ("sequence.k", shape(&sequence), "MAIN"),
        ("rewrite.k", rewrite, "REWRITE"),
    ] {
        let loaded = load(file, &source, module);
        let document = json::to_provenance_string(loaded.definition(), loaded.source_table())
            .expect("the loaded definition encodes");
        let decoded = json::from_provenance_str(&document).expect("the document decodes");
        let relinked = LoadedDefinition::from_loaded_parts(LoadedParts {
            files: Vec::new(),
            source_table: decoded.source_table,
            definition: decoded.definition,
            diagnostics: Vec::new(),
        })
        .expect("the decoded definition relinks");
        assert_eq!(
            json::to_provenance_string(relinked.definition(), relinked.source_table()).unwrap(),
            document,
            "{file}: the loaded document is a fixed point"
        );
        let (direct, direct_kore) = compiled(&loaded);
        let (routed, routed_kore) = compiled(&relinked);
        assert!(direct == routed, "{file}: the execution provenance differs");
        assert_eq!(direct_kore, routed_kore, "{file}");
    }
}

/// The documents of a deep and of a wide fixture, pinned byte for byte, so that a change of what
/// the recorder names or of the order the writer visits receipts in, which every version 8
/// reader would still accept, shows as a reviewed change of these snapshots (and of the digests
/// consumers keep of such documents).
#[test]
fn golden_documents_of_a_deep_and_a_wide_fixture() {
    use k_rust::definition::{Attributes, Definition, FlatModule, Sentence};
    use k_rust::kast::{Sort, Term, TermMetadata, TermSpan};
    use k_rust::provenance::{
        GeneratingPass, LogicalSourceId, SourceTable, record_generated_origins,
    };
    use std::sync::Arc;

    let mut sources = SourceTable::default();
    let source = sources.intern(LogicalSourceId::new("fixture.k", b"fixture"));
    let spanned = |term: Term, start: usize| {
        term.with_metadata(TermMetadata {
            span: Some(TermSpan {
                source,
                start,
                end: start + 1,
            }),
            ..TermMetadata::default()
        })
    };
    let definition = |body: Term, attributes: Attributes| Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![Arc::new(Sentence::Rule {
                body,
                requires: Term::Token {
                    token: "true".into(),
                    sort: Sort::new("Bool"),
                },
                ensures: Term::Token {
                    token: "true".into(),
                    sort: Sort::new("Bool"),
                },
                attributes,
            })],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };
    let label = || Attributes::new([("label".into(), "MAIN.rule".into())].into());
    let attributes = |definition: &Definition| {
        definition.modules[0].local_sentences[0]
            .attributes()
            .clone()
    };
    // Deep: `s(s(s(z)))`, spans at every level, its leaf replaced by two passes in turn.
    let deep = |leaf: &str| {
        (1..4).fold(Term::apply(leaf, Vec::new()), |term, level| {
            spanned(Term::apply("s", vec![term]), level)
        })
    };
    let loaded = definition(deep("z0"), label());
    let first = record_generated_origins(
        &loaded,
        definition(deep("z1"), attributes(&loaded)),
        GeneratingPass::ConcretizeCells,
    );
    let second = record_generated_origins(
        &first,
        definition(deep("z2"), attributes(&first)),
        GeneratingPass::AddSortInjections,
    );
    // Wide: `a ~> b ~> c`, spans on every item, each item wrapped in `w(_)`.
    let items = |wrap: bool| {
        Term::Sequence(
            ["a", "b", "c"]
                .into_iter()
                .enumerate()
                .map(|(index, item)| {
                    let item = spanned(Term::apply(item, Vec::new()), index);
                    if wrap {
                        Term::apply("w", vec![item])
                    } else {
                        item
                    }
                })
                .collect(),
        )
    };
    let flat = definition(items(false), label());
    let wide = record_generated_origins(
        &flat,
        definition(items(true), attributes(&flat)),
        GeneratingPass::ConfigurationExpansion,
    );
    let mut settings = insta::Settings::clone_current();
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| {
        insta::assert_snapshot!(
            "provenance_golden_deep",
            json::to_provenance_string_pretty(&second, &sources).unwrap()
        );
        insta::assert_snapshot!(
            "provenance_golden_wide",
            json::to_provenance_string_pretty(&wide, &sources).unwrap()
        );
    });
}

/// A document holding every arm of the format's conventions, pinned byte for byte (design §14.1,
/// G4b): two modules and several sentences; a rule with metadata in all three fields and a
/// configuration with metadata in its `ensures`; every term constructor (application, rewrite,
/// alias, sequence, variable, token, injected label) with metadata; spans in two sources, a
/// production and a sort; a sentence receipt naming a source link and a sentence link; and term
/// receipts of two passes under a rewrite and an alias, the later ones naming the earlier sets.
/// A change of how any of these is numbered or written, in the writer and reader together,
/// shows as a reviewed change of this snapshot. The test also checks that the document still
/// holds every arm, so that editing the fixture cannot drop one unnoticed.
#[test]
fn golden_document_of_every_shape() {
    use k_rust::definition::{Attributes, Definition, FlatModule, Sentence};
    use k_rust::kast::{Label, ProductionIdentity, Sort, Term, TermMetadata, TermSpan};
    use k_rust::provenance::{
        GeneratingPass, LogicalSourceId, ORIGIN_ATTRIBUTE, OriginRecord, ProvenanceLink, SourceId,
        SourceTable, record_generated_origins,
    };
    use std::sync::Arc;

    let mut sources = SourceTable::default();
    let main_source = sources.intern(LogicalSourceId::new("fixture.k", b"fixture"));
    let other_source = sources.intern(LogicalSourceId::new("other.k", b"other"));
    let span = |source: SourceId, start: usize| TermSpan {
        source,
        start,
        end: start + 2,
    };
    let spanned = |term: Term, source: SourceId, start: usize| {
        term.with_metadata(TermMetadata {
            span: Some(span(source, start)),
            ..TermMetadata::default()
        })
    };
    let token = |token: &str, sort: &str| Term::Token {
        token: token.into(),
        sort: Sort::new(sort),
    };
    let label = |name: &str| Attributes::new([("label".into(), name.into())].into());
    // `r((f(X) #as ALIAS) => (g() ~> TOKEN))`, every node spanned; `f` carries a production and
    // the alias a sort. `pattern` replaces `f(X)` when given.
    let body = |alias: &str, number: &str, pattern: Option<Term>| {
        let pattern = pattern.unwrap_or_else(|| {
            Term::apply("f", vec![spanned(Term::variable("X"), main_source, 8)]).with_metadata(
                TermMetadata {
                    span: Some(span(main_source, 6)),
                    production: ProductionIdentity::from_hex("0123456789abcdef0123456789abcdef"),
                    ..TermMetadata::default()
                },
            )
        });
        let alias = Term::variable(alias).with_metadata(TermMetadata {
            span: Some(span(main_source, 12)),
            sort: Some(Sort::new("Exp")),
            ..TermMetadata::default()
        });
        spanned(
            Term::apply(
                "r",
                vec![spanned(
                    Term::Rewrite {
                        left: Box::new(spanned(
                            Term::As {
                                pattern: Box::new(pattern),
                                alias: Box::new(alias),
                            },
                            main_source,
                            4,
                        )),
                        right: Box::new(spanned(
                            Term::Sequence(vec![
                                spanned(Term::apply("g", Vec::new()), main_source, 16),
                                spanned(token(number, "Int"), main_source, 20),
                            ]),
                            main_source,
                            14,
                        )),
                    },
                    main_source,
                    2,
                )],
            ),
            main_source,
            0,
        )
    };
    let main_rule = |body: Term| Sentence::Rule {
        body,
        requires: spanned(
            Term::apply("c", vec![spanned(Term::variable("X"), other_source, 2)]),
            other_source,
            0,
        ),
        ensures: spanned(token("true", "Bool"), other_source, 4),
        attributes: label("MAIN.shapes"),
    };
    let configuration = Sentence::Configuration {
        body: spanned(
            Term::apply(
                "cell",
                vec![spanned(
                    Term::InjectedLabel(Label::new("h")),
                    main_source,
                    26,
                )],
            ),
            main_source,
            24,
        ),
        ensures: spanned(token("true", "Bool"), main_source, 30),
        attributes: label("MAIN.config"),
    };
    let mut other_attributes = label("OTHER.rule");
    other_attributes.insert(
        ORIGIN_ATTRIBUTE,
        OriginRecord {
            pass: GeneratingPass::MacroExpansion,
            origins: vec![
                ProvenanceLink::Source {
                    span: span(other_source, 6),
                },
                ProvenanceLink::Sentence {
                    unique_id: "a".repeat(64),
                },
            ]
            .into(),
            destination: None,
        }
        .to_value(),
    );
    let other_rule = Sentence::Rule {
        body: spanned(
            Term::apply("o", vec![spanned(Term::variable("Z"), other_source, 10)]),
            other_source,
            8,
        ),
        requires: token("true", "Bool"),
        ensures: token("true", "Bool"),
        attributes: other_attributes,
    };
    let definition = |main: Sentence, previous: Option<&Definition>| {
        let main = match previous {
            Some(previous) => {
                let mut main = main;
                *attributes_mut(&mut main) =
                    previous.modules[0].local_sentences[0].attributes().clone();
                main
            }
            None => main,
        };
        Definition {
            main_module: "MAIN".into(),
            modules: vec![
                FlatModule {
                    name: "MAIN".into(),
                    imports: Vec::new(),
                    local_sentences: vec![Arc::new(main), Arc::new(configuration.clone())],
                    attributes: Attributes::default(),
                },
                FlatModule {
                    name: "OTHER".into(),
                    imports: Vec::new(),
                    local_sentences: vec![Arc::new(other_rule.clone())],
                    attributes: Attributes::default(),
                },
            ],
            attributes: Attributes::default(),
        }
    };
    fn attributes_mut(sentence: &mut Sentence) -> &mut Attributes {
        match sentence {
            Sentence::Rule { attributes, .. } => attributes,
            _ => unreachable!("the main sentence is a rule"),
        }
    }
    let loaded = definition(main_rule(body("Y", "1", None)), None);
    // The first pass renames the alias and changes the token: the root, the rewrite, the alias
    // node, the new variable and the sequence are receipted.
    let first = record_generated_origins(
        &loaded,
        definition(main_rule(body("W", "2", None)), Some(&loaded)),
        GeneratingPass::ConcretizeCells,
    );
    // The second places the pattern, unchanged, under a new injection, in the first pass's
    // output (whose receipts the other nodes keep): the nodes above the pattern and the
    // injection are receipted, naming the first pass's sets.
    fn bare(mut term: &mut Term) -> &mut Term {
        while let Term::Annotated { term: inner, .. } = term {
            term = inner;
        }
        term
    }
    let mut second_main = (*first.modules[0].local_sentences[0]).clone();
    let Sentence::Rule {
        body: second_body, ..
    } = &mut second_main
    else {
        unreachable!()
    };
    let Term::Apply { arguments, .. } = bare(second_body) else {
        unreachable!()
    };
    let Term::Rewrite { left, .. } = bare(&mut arguments[0]) else {
        unreachable!()
    };
    let Term::As { pattern, .. } = bare(left) else {
        unreachable!()
    };
    let moved = (**pattern).clone();
    **pattern = Term::apply("inj", vec![moved]);
    let second = record_generated_origins(
        &first,
        definition(second_main, Some(&first)),
        GeneratingPass::AddSortInjections,
    );

    let document = json::to_provenance_string_pretty(&second, &sources).unwrap();
    let envelope: serde_json::Value = serde_json::from_str(&document).unwrap();
    let mut nodes = std::collections::BTreeSet::new();
    let mut pending = vec![&envelope["term"]];
    while let Some(value) = pending.pop() {
        match value {
            serde_json::Value::Object(members) => {
                if let Some(serde_json::Value::String(node)) = members.get("node") {
                    nodes.insert(node.clone());
                }
                pending.extend(members.values());
            }
            serde_json::Value::Array(items) => pending.extend(items),
            _ => {}
        }
    }
    for node in [
        "KApply",
        "KRewrite",
        "KAs",
        "KSequence",
        "KVariable",
        "KToken",
        "InjectedKLabel",
    ] {
        assert!(nodes.contains(node), "the document holds no {node}");
    }
    let entries = envelope["termMetadata"].as_array().unwrap();
    let has = |test: &dyn Fn(&serde_json::Value) -> bool| entries.iter().any(test);
    for field in 0..3 {
        assert!(
            has(&|entry| entry["moduleIndex"] == 0
                && entry["sentenceIndex"] == 0
                && entry["field"] == field),
            "no metadata in the rule's field {field}"
        );
    }
    assert!(has(
        &|entry| entry["sentenceIndex"] == 1 && entry["field"] == 1
    ));
    assert!(has(&|entry| entry["moduleIndex"] == 1));
    for member in ["span", "production", "sort", "origin"] {
        assert!(
            has(&|entry| !entry["metadata"][member].is_null()),
            "no {member}"
        );
    }
    for source in 0..2 {
        assert!(has(&|entry| entry["metadata"]["span"]["source"] == source));
    }
    let parts = envelope["originSets"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|entry| entry.as_array().unwrap())
        .map(|part| part["kind"].as_str().unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(parts, ["sentence", "set", "source"].into());
    let anchors = envelope["anchors"].as_array().unwrap();
    assert!(anchors.iter().any(|anchor| !anchor["module"].is_null()));
    assert!(anchors.iter().any(|anchor| !anchor["parent"].is_null()));

    let mut settings = insta::Settings::clone_current();
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| insta::assert_snapshot!("provenance_golden_shapes", document));
}
