//! Parity of adapter-built lexical and layout sentences (KF-004, X9.2).
//!
//! K's outer syntax desugars `syntax lexical` and `syntax #Layout` privately,
//! so the adapter rebuilds them as flat sentences. This test lowers a theory
//! with lexicals, layout, and a token regex that refers to them, emits its
//! `.k`, lowers that text with k-rust's own outer frontend, and requires the
//! adapter's sentences to be equivalent (k-rust `definition/equivalence.rs`)
//! to the ones k-rust builds, apart from source-location attributes.

use k_rust::definition::{Attributes, Sentence, equivalence::sentence_equivalent};
use krs_ir::testing;
use krs_ir::{
    ConfigurationRoot, FixedCell, FixedConfiguration, FixedInitializerCell, ItemKind,
    LayoutSentence, LexicalSentence, ModuleId, NodeOrigin, PackageId, ProductionAttribute,
    SemanticId, StableItemId,
};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
    SemanticTerm, SemanticTheory,
};

fn package() -> PackageId {
    testing::package("KRS-LEXING", "lexing")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "lexing", name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        package(),
        "src/lib.rs",
        testing::digest_with("2".repeat(64)),
        0,
        1,
    )
}

fn theory() -> SemanticTheory {
    let name = item("Name", ItemKind::Sort);
    let token = SemanticProduction::new(
        origin("name.token"),
        item("NameToken", ItemKind::Constructor),
        SemanticSortRef::Declared(name.clone()),
        vec![
            SemanticProductionItem::regex_terminal(
                origin("name.regex"),
                None,
                "{Alpha}{AlphaNum}*",
                None,
            )
            .unwrap(),
        ],
        vec![ProductionAttribute::Token {
            origin: origin("name.attribute"),
            lexical_precedence: None,
        }],
    )
    .unwrap();
    let cell = SemanticId::new("cell.k").unwrap();
    let configuration = FixedConfiguration::new(
        origin("configuration"),
        SemanticId::new("configuration").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                origin("cell"),
                cell.clone(),
                "k",
                vec![],
                SemanticSortRef::int(),
            )
            .unwrap(),
        ],
        origin("initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            origin("initializer.cell"),
            cell,
            SemanticTerm::token(origin("initializer.token"), SemanticSortRef::int(), "0").unwrap(),
        )],
    )
    .unwrap();
    let module = SemanticModule::new(
        origin("module"),
        ModuleId::new("KRS-LEXING").unwrap(),
        vec![],
        vec![SemanticSort::new(origin("name"), name)],
        vec![],
        vec![token],
        vec![],
        vec![],
        Some(configuration),
        vec![],
    )
    .with_lexicals(vec![
        LexicalSentence::new(origin("lexical.alpha"), "Alpha", "[a-zA-Z]").unwrap(),
        LexicalSentence::new(origin("lexical.alpha-num"), "AlphaNum", r"[a-zA-Z0-9_\-]").unwrap(),
    ])
    .with_layouts(vec![
        LayoutSentence::new(origin("layout.comment"), r"(;[^\n\r]*)").unwrap(),
        LayoutSentence::new(origin("layout.space"), r"([\ \n\r\t])").unwrap(),
    ]);
    SemanticTheory::new(vec![module]).unwrap()
}

/// Lexical and layout sentences, with every attribute except `token` dropped.
fn lexing_sentences<'a>(sentences: impl IntoIterator<Item = &'a Sentence>) -> Vec<Sentence> {
    sentences
        .into_iter()
        .filter_map(|sentence| {
            let mut attributes = Attributes::default();
            match sentence {
                Sentence::SyntaxLexical { name, regex, .. } => Some(Sentence::SyntaxLexical {
                    name: name.clone(),
                    regex: regex.clone(),
                    attributes,
                }),
                Sentence::Production {
                    label,
                    parameters,
                    sort,
                    items,
                    attributes: source,
                } if sort.name == "#Layout" => {
                    if let Some(token) = source.get("token") {
                        attributes.insert("token", token.clone());
                    }
                    Some(Sentence::Production {
                        label: label.clone(),
                        parameters: parameters.clone(),
                        sort: sort.clone(),
                        items: items.clone(),
                        attributes,
                    })
                }
                _ => None,
            }
        })
        .collect()
}

#[test]
fn adapted_lexicals_and_layout_match_k_rust_outer_lowering() {
    let lowered = krs_compiler::lower_semantic_theory(&theory()).unwrap();
    let emitted = krs_compiler::emit_k(&lowered).unwrap();
    let source = emitted.source();
    assert!(
        source.contains("syntax lexical Alpha = r\"[a-zA-Z]\"\n"),
        "{source}"
    );
    assert!(
        source.contains("syntax #Layout ::= r\"([\\\\ \\\\n\\\\r\\\\t])\" [token]\n"),
        "{source}"
    );

    let main = lowered.definition().main_module().as_str().to_owned();
    let parsed = k_rust::outer::parse("lexing.k", source).unwrap();
    let outer = k_rust::outer::lower(&parsed, main).unwrap();
    let adapted = krs_k_rust::adapt_definition(lowered.definition()).unwrap();

    let expected = lexing_sentences(
        outer
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter().map(AsRef::as_ref)),
    );
    let actual = lexing_sentences(
        adapted
            .definition()
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter().map(AsRef::as_ref)),
    );
    assert_eq!(expected.len(), 4, "{expected:#?}");
    assert_eq!(actual.len(), expected.len(), "{actual:#?}");
    for expected in &expected {
        assert!(
            actual
                .iter()
                .any(|actual| sentence_equivalent(actual, expected)),
            "no adapted sentence is equivalent to {expected:#?}\nadapted: {actual:#?}"
        );
    }
}
