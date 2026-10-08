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
