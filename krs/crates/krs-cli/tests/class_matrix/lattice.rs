//! K4, the full tier: KRS's sort judges answer every subsort question about a generated base the
//! way k-rust's lattice of the emitted definition does.
//!
//! Each base's own package is collected, and its Definition IR is adapted and loaded by k-rust as
//! `krs build` loads it. Two k-rust judges read the loaded definition: `compute_subsorts`, the
//! semantic relation, and `compute_disambiguation_subsorts`, which adds `(element, list)` for
//! every user list. Both relations leave out the kernel's `{S} KItem ::= S`, a fact that
//! compilation states for every sort but `K`, so each judge is completed with it when the
//! definition declares it. Every KRS judge (`krs_compiler::testing::SortJudge`) is compared with
//! both over every ordered pair of distinct sorts, and the disagreements are classified as the fast
//! tier classifies them (`krs-compiler/tests/lattice.rs`): `S ≤ KItem`, `KItem ≤ K`, element ≤
//! list, other. The `KItem ≤ K` and element ≤ list counts are printed and never fail; the others
//! pass only as `pending.toml` records them, keyed `lattice/class-BASE/JUDGE~JUDGE/CLASS`.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use k_rust::definition::{
    PartialOrder, ProductionItem, Sentence, compute_disambiguation_subsorts, compute_subsorts,
};
use k_rust::kast::Sort;
use krs_compiler::testing::{SortJudge, SortJudges};
use krs_ir::BuiltinSort;
use krs_ir_levels::k_surface::DefinitionIndex;
use krs_ir_levels::{DefinitionIr, DefinitionSortRef, SemanticSortRef};
use krs_k_rust::{Backend, adapt_definition, prepare_definition};

/// The fact a disagreement is about.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Class {
    SortKItem,
    KItemK,
    ElementList,
    Other,
}

impl Class {
    pub const fn name(self) -> &'static str {
        match self {
            Self::SortKItem => "s-kitem",
            Self::KItemK => "kitem-k",
            Self::ElementList => "element-list",
            Self::Other => "other",
        }
    }

    /// Whether the class's answer is undecided, so that a disagreement is counted, not failed.
    pub const fn open(self) -> bool {
        matches!(self, Self::KItemK | Self::ElementList)
    }
}

fn is_k_item(sort: &SemanticSortRef) -> bool {
    matches!(sort, SemanticSortRef::Declared(id)
        if id.item_name() == "KItem" && id.package().k_namespace() == "KRS-FRAMEWORK")
}

fn class(judges: &SortJudges, candidate: &SemanticSortRef, expected: &SemanticSortRef) -> Class {
    if is_k_item(expected) {
        Class::SortKItem
    } else if *expected == SemanticSortRef::Builtin(BuiltinSort::KSequence) {
        Class::KItemK
    } else if judges
        .user_lists()
        .contains(&(candidate.clone(), expected.clone()))
    {
        Class::ElementList
    } else {
        Class::Other
    }
}

/// One of k-rust's relations over the emitted definition.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum KRustJudge {
    /// `compute_subsorts`, the semantic relation.
    Subsorts,
    /// `compute_disambiguation_subsorts`.
    Disambiguation,
}

impl KRustJudge {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Subsorts => "k-rust-subsorts",
            Self::Disambiguation => "k-rust-disambiguation",
        }
    }
}

/// How many sort pairs the KRS judge holds and k-rust's does not, and the converse.
#[derive(Default)]
pub struct Count {
    pub krs_only: usize,
    pub k_rust_only: usize,
}

/// The comparison of one base's definition.
pub struct Comparison {
    /// The sorts compared.
    pub sorts: usize,
    /// The disagreements by judge pair and class.
    pub counts: BTreeMap<(SortJudge, KRustJudge, Class), Count>,
}

fn sort(name: &str) -> Sort {
    Sort {
        name: name.to_owned(),
        parameters: Vec::new(),
    }
}

/// The emitted K name of a Definition IR sort.
fn emitted_name(index: &DefinitionIndex<'_>, sort: &DefinitionSortRef) -> Option<String> {
    match sort {
        DefinitionSortRef::Declared(symbol) => index.sort_name(symbol).map(str::to_owned),
        DefinitionSortRef::Builtin(builtin) => Some(builtin.k_name().to_owned()),
        DefinitionSortRef::Cell(cell) => index.cell_sort_name(cell),
        DefinitionSortRef::Parameter(_) => None,
    }
}

/// Whether `sentence` is the kernel's `{S} KItem ::= S`.
fn is_kernel_top(sentence: &Sentence) -> bool {
    let Sentence::Production {
        label: None,
        parameters,
        sort,
        items,
        ..
    } = sentence
    else {
        return false;
    };
    sort.name == "KItem"
        && matches!(items.as_slice(), [ProductionItem::NonTerminal { sort: child, .. }]
            if parameters.contains(child))
}

/// `relation` completed, when `kernel`, with `S ≤ KItem` for each of the compared `sorts` that is
/// neither `KItem` nor one of its supersorts (`K`, and the rule grammar's sorts above it).
fn completed(relation: &PartialOrder<Sort>, sorts: &[Sort], kernel: bool) -> PartialOrder<Sort> {
    let mut pairs = relation.direct_relations().clone();
    if kernel {
        let k_item = sort("KItem");
        for sort in sorts {
            if *sort != k_item && !relation.less_than_eq(&k_item, sort) {
                pairs.insert((sort.clone(), k_item.clone()));
            }
        }
    }
    PartialOrder::new(pairs)
        .unwrap_or_else(|cycle| panic!("the completed relation has a cycle: {cycle:?}"))
}

/// Compare every KRS judge with k-rust's two relations over `definition`, which lowering emitted
/// from the bundle the judges were built from.
///
/// # Panics
///
/// Panics if k-rust cannot adapt or load the definition, or its relation has a cycle.
#[must_use]
pub fn compare(judges: &SortJudges, definition: &DefinitionIr) -> Comparison {
    let adapted = adapt_definition(definition).expect("k-rust adapts the emitted definition");
    let loaded = prepare_definition(adapted.definition().clone(), Backend::Haskell)
        .expect("k-rust loads the emitted definition");
    let sentences = loaded
        .definition()
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter().map(AsRef::as_ref))
        .collect::<Vec<&Sentence>>();
    let kernel = sentences.iter().any(|sentence| is_kernel_top(sentence));

    let index = DefinitionIndex::new(definition);
    let names = judges
        .sorts()
        .iter()
        .filter_map(|semantic| {
            let name = emitted_name(&index, judges.definition_sort(semantic)?)?;
            Some((semantic.clone(), sort(&name)))
        })
        .collect::<BTreeMap<_, _>>();
    let queried = names.values().cloned().collect::<Vec<_>>();
    let semantic = compute_subsorts(sentences.iter().copied(), false)
        .expect("the semantic relation has no cycle");
    let disambiguation =
        compute_disambiguation_subsorts(&sentences).expect("the relation has no cycle");
    let relations = [
        (KRustJudge::Subsorts, completed(&semantic, &queried, kernel)),
        (
            KRustJudge::Disambiguation,
            completed(&disambiguation, &queried, kernel),
        ),
    ];

    let mut counts = BTreeMap::<(SortJudge, KRustJudge, Class), Count>::new();
    for (candidate, candidate_name) in &names {
        for (expected, expected_name) in names.iter().filter(|(other, _)| *other != candidate) {
            let class = class(judges, candidate, expected);
            for (k_rust, relation) in &relations {
                let k_rust_holds = relation.less_than(candidate_name, expected_name);
                for judge in SortJudge::ALL {
                    let krs_holds = judges.is_subsort(judge, candidate, expected);
                    if krs_holds == k_rust_holds {
                        continue;
                    }
                    let count = counts.entry((judge, *k_rust, class)).or_default();
                    if krs_holds {
                        count.krs_only += 1;
                    } else {
                        count.k_rust_only += 1;
                    }
                }
            }
        }
    }
    Comparison {
        sorts: names.len(),
        counts,
    }
}

/// The signature `pending.toml` records for one count.
#[must_use]
pub fn signature(count: &Count, judge: SortJudge, k_rust: KRustJudge) -> String {
    let mut text = String::new();
    write!(
        text,
        "{} pairs only {} holds; {} pairs only {} holds",
        count.krs_only,
        judge.name(),
        count.k_rust_only,
        k_rust.name()
    )
    .expect("writing to a String cannot fail");
    text
}
