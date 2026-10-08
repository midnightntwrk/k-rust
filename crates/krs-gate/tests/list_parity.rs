//! Parity of adapter-built syntactic lists (KF-020, X9.2).
//!
//! K's outer syntax desugars `List{Elem, "sep"}` and `NeList{..}` privately,
//! so the adapter rebuilds the cons and terminator productions as k-rust's
//! `lower_user_list` does. This test lowers a theory with a `List` and a
//! separator-less `NeList`, emits its `.k`, lowers that text with k-rust's own
//! outer frontend, and requires the adapter's list productions to be
//! equivalent (k-rust `definition/equivalence.rs`) to the ones k-rust builds:
//! same labels, sorts, and items, and the same `userList` kind. The other
//! attributes are dropped: k-rust's outer lowering keeps source locations and
//! the authored `symbol`/`terminator-symbol` keys, which the adapter, like for
//! every production, expresses as the label instead.

use k_rust::definition::{Attributes, Sentence, equivalence::sentence_equivalent};
use krs_ir::testing;
use krs_ir::{
    ConfigurationRoot, FixedCell, FixedConfiguration, FixedInitializerCell, ItemKind, ModuleId,
    NodeOrigin, PackageId, ProductionAttribute, ProductionFieldId, SemanticId, StableItemId,
};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
    SemanticTerm, SemanticTheory,
};

fn package() -> PackageId {
    testing::package("KRS-LISTS", "lists")
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    testing::item_in(package(), "lists", name, kind)
}

fn origin(key: &str) -> NodeOrigin {
    testing::origin_in(
        key,
        package(),
        "src/lib.rs",
        testing::digest_with("3".repeat(64)),
        0,
        1,
    )
}

/// The cons and terminator productions of one list of `Int`.
fn list(name: &str, separator: &str, non_empty: bool) -> (SemanticSort, [SemanticProduction; 2]) {
    let sort = item(name, ItemKind::Sort);
    let cons = item(&format!("{name}Cons"), ItemKind::Constructor);
    let nil = item(&format!("{name}Nil"), ItemKind::Constructor);
    let mut items = vec![SemanticProductionItem::non_terminal(
        origin(&format!("{name}.head")),
        ProductionFieldId::new("head").unwrap(),
        SemanticSortRef::int(),
    )];
    if !separator.is_empty() {
        items.push(
            SemanticProductionItem::terminal(origin(&format!("{name}.separator")), separator)
                .unwrap(),
        );
    }
    items.push(SemanticProductionItem::non_terminal(
        origin(&format!("{name}.tail")),
        ProductionFieldId::new("tail").unwrap(),
        SemanticSortRef::Declared(sort.clone()),
    ));
    let cons_production = SemanticProduction::new(
        origin(&format!("{name}.cons")),
        cons.clone(),
        SemanticSortRef::Declared(sort.clone()),
        items,
        vec![ProductionAttribute::ListCons {
            origin: origin(&format!("{name}.list")),
            separator: separator.to_owned(),
            non_empty,
            terminator: nil.clone(),
        }],
    )
    .unwrap();
    let nil_production = SemanticProduction::new(
        origin(&format!("{name}.nil")),
        nil,
        SemanticSortRef::Declared(sort.clone()),
        vec![
            SemanticProductionItem::terminal(
                origin(&format!("{name}.terminator")),
                format!(".{name}"),
            )
            .unwrap(),
        ],
        vec![ProductionAttribute::ListTerminator {
            origin: origin(&format!("{name}.list-terminator")),
            cons,
        }],
    )
    .unwrap();
    (
        SemanticSort::new(origin(&format!("{name}.sort")), sort),
        [cons_production, nil_production],
    )
}

fn theory() -> SemanticTheory {
    let (ints, ints_productions) = list("Ints", ",", false);
    let (ops, ops_productions) = list("Ops", "", true);
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
        ModuleId::new("KRS-LISTS").unwrap(),
        vec![],
        vec![ints, ops],
        vec![],
        ints_productions
            .into_iter()
            .chain(ops_productions)
            .collect(),
        vec![],
        vec![],
        Some(configuration),
        vec![],
    );
    SemanticTheory::new(vec![module]).unwrap()
}

/// The productions of the list sorts, with every attribute except `userList`
/// dropped.
fn list_productions<'a>(sentences: impl IntoIterator<Item = &'a Sentence>) -> Vec<Sentence> {
    sentences
        .into_iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label,
                parameters,
                sort,
                items,
                attributes: source,
            } if matches!(sort.name.as_str(), "Ints" | "Ops") => {
                let mut attributes = Attributes::default();
                if let Some(kind) = source.get("userList") {
                    attributes.insert("userList", kind.clone());
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
        })
        .collect()
}

#[test]
fn adapted_lists_match_k_rust_outer_lowering() {
    let lowered = krs_compiler::lower_semantic_theory(&theory()).unwrap();
    let emitted = krs_compiler::emit_k(&lowered).unwrap();
    let source = emitted.source();
    assert!(
        source.contains(
            "syntax Ints ::= List{Int, \",\"} [symbol(intsCons), terminator-symbol(intsNil), private]\n"
        ),
        "{source}"
    );
    assert!(
        source.contains(
            "syntax Ops ::= NeList{Int, \"\"} [symbol(opsCons), terminator-symbol(opsNil), private]\n"
        ),
        "{source}"
    );
    assert!(!source.contains("\".Ints\""), "{source}");

    let main = lowered.definition().main_module().as_str().to_owned();
    let parsed = k_rust::outer::parse("lists.k", source).unwrap();
    let outer = k_rust::outer::lower(&parsed, main).unwrap();
    let adapted = krs_k_rust::adapt_definition(lowered.definition()).unwrap();

    let expected = list_productions(
        outer
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter().map(AsRef::as_ref)),
    );
    let actual = list_productions(
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
