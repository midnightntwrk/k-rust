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
//!
//! A strict list's value list (KF-020) adds K's `overload` key, which K
//! writes once on each `List{..}` sentence and copies to the generated
//! terminator: the adapter's keys must be the ones k-rust derives.

use k_rust::definition::{Attributes, Sentence, equivalence::sentence_equivalent};
use krs_ir::testing;
use krs_ir::{
    ConfigurationRoot, FixedCell, FixedConfiguration, FixedInitializerCell, ItemKind, ModuleId,
    NodeOrigin, PackageId, ProductionAttribute, ProductionFieldId, SemanticId, StableItemId,
};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
    SemanticSubsort, SemanticTerm, SemanticTheory,
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
    list_of(name, SemanticSortRef::int(), separator, non_empty)
}

/// The cons and terminator productions of one list of `element`.
fn list_of(
    name: &str,
    element: SemanticSortRef,
    separator: &str,
    non_empty: bool,
) -> (SemanticSort, [SemanticProduction; 2]) {
    let sort = item(name, ItemKind::Sort);
    let cons = item(&format!("{name}Cons"), ItemKind::Constructor);
    let nil = item(&format!("{name}Nil"), ItemKind::Constructor);
    let mut items = vec![SemanticProductionItem::non_terminal(
        origin(&format!("{name}.head")),
        ProductionFieldId::new("head").unwrap(),
        element,
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
    module_theory(
        vec![ints, ops],
        vec![],
        ints_productions
            .into_iter()
            .chain(ops_productions)
            .collect(),
    )
}

/// `Vals ::= List{Val, ","}`, the value list of `Exps ::= List{Exp, ","}`.
fn value_list_theory() -> SemanticTheory {
    let exp = item("Exp", ItemKind::Sort);
    let val = item("Val", ItemKind::Sort);
    let (exps, exps_productions) =
        list_of("Exps", SemanticSortRef::Declared(exp.clone()), ",", false);
    let (vals, vals_productions) =
        list_of("Vals", SemanticSortRef::Declared(val.clone()), ",", false);
    let subsorts = vec![
        SemanticSubsort::new(
            origin("val-exp"),
            SemanticSortRef::Declared(val.clone()),
            SemanticSortRef::Declared(exp.clone()),
        ),
        SemanticSubsort::new(
            origin("vals-exps"),
            SemanticSortRef::Declared(vals.id().clone()),
            SemanticSortRef::Declared(exps.id().clone()),
        ),
    ];
    module_theory(
        vec![
            SemanticSort::new(origin("exp"), exp),
            SemanticSort::new(origin("val"), val),
            exps,
            vals,
        ],
        subsorts,
        exps_productions
            .into_iter()
            .chain(vals_productions)
            .collect(),
    )
}

fn module_theory(
    sorts: Vec<SemanticSort>,
    subsorts: Vec<SemanticSubsort>,
    productions: Vec<SemanticProduction>,
) -> SemanticTheory {
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
        sorts,
        subsorts,
        productions,
        vec![],
        vec![],
        Some(configuration),
        vec![],
    );
    SemanticTheory::new(vec![module]).unwrap()
}

/// The cons and terminator productions of the list sorts, with every
/// attribute except `userList` and `overload` dropped.
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
            } if matches!(sort.name.as_str(), "Ints" | "Ops" | "Exps" | "Vals")
                && source.get("userList").is_some() =>
            {
                let mut attributes = Attributes::default();
                for key in ["userList", "overload"] {
                    if let Some(value) = source.get(key) {
                        attributes.insert(key, value.clone());
                    }
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
    assert_parity(&lowered, source);
}

#[test]
fn value_list_overload_keys_match_k_rust_outer_lowering() {
    let lowered = krs_compiler::lower_semantic_theory(&value_list_theory()).unwrap();
    let emitted = krs_compiler::emit_k(&lowered).unwrap();
    let source = emitted.source();
    for line in [
        "syntax Exps ::= List{Exp, \",\"} [symbol(expsCons), terminator-symbol(expsNil), private, overload(expsCons)]\n",
        "syntax Vals ::= List{Val, \",\"} [symbol(valsCons), terminator-symbol(valsNil), private, overload(expsCons)]\n",
    ] {
        assert!(source.contains(line), "{source}");
    }
    let adapted = krs_k_rust::adapt_definition(lowered.definition()).unwrap();
    let keys = list_productions(
        adapted
            .definition()
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter().map(AsRef::as_ref)),
    )
    .into_iter()
    .filter_map(|sentence| match sentence {
        Sentence::Production { attributes, .. } => attributes.get("overload").cloned(),
        _ => None,
    })
    .collect::<Vec<_>>();
    // The terminators take the cons key, as K copies it to them.
    assert_eq!(keys.len(), 4, "{keys:?}");
    assert!(
        keys.iter().all(|key| key.as_str() == Some("expsCons")),
        "{keys:?}"
    );
    assert_parity(&lowered, source);
}

fn assert_parity(lowered: &krs_compiler::LoweredDefinition, source: &str) {
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
