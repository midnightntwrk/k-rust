//! K4, the fast tier: KRS's sort judges answer every subsort question about one definition the
//! same way.
//!
//! Each stage that judges subsorts builds its own graph (`krs_compiler::testing::SortJudge`): the
//! inference catalog, both IR validators, the overlap check, and the coverage lint. Over the
//! fixture bundles of this directory and synthetic edits of them, every judge is asked
//! `is_subsort(a, b)` for every ordered pair of the definition's sorts, and each pair of judges
//! that answers differently is a disagreement, classified by the fact it is about:
//!
//! - `S ≤ KItem`: whether a sort is a `KItem`;
//! - `KItem ≤ K`: whether a `KItem`, or any sort, is a `K` (the computation's sort);
//! - element ≤ list: whether a user list's element is the list;
//! - other.
//!
//! The `KItem ≤ K` and element ≤ list classes are printed and never fail: which answer one
//! shared lattice should give is not decided yet, and these counts are its input. Every other
//! disagreement is red: it passes only when `pending.toml` records it, keyed
//! `lattice/DEFINITION/JUDGE~JUDGE/CLASS` with its exact count, under the PENDING rules.
//!
//! Comparing the judges with k-rust's `compute_subsorts` needs the emitted definition and is the
//! full tier's.

#[path = "fixtures/configuration.rs"]
mod configuration;
#[path = "fixtures/grammar.rs"]
mod grammar;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use krs_compiler::testing::{SortJudge, SortJudges};
use krs_ir::testing::{DescriptorBundleInputs, DescriptorInputs};
use krs_ir::{
    BuiltinSort, DescriptorPayload, DescriptorSortParent, ItemKind, ProvenanceRole, SortDescriptor,
    StableItemId,
};
use krs_ir_levels::SemanticSortRef;
use krs_test_support::class_matrix::pending::{
    Judgement, LATTICE, Observation, Pending, UNASSIGNED,
};

/// The fact a disagreement is about.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Class {
    SortKItem,
    KItemK,
    ElementList,
    Other,
}

impl Class {
    const fn name(self) -> &'static str {
        match self {
            Self::SortKItem => "s-kitem",
            Self::KItemK => "kitem-k",
            Self::ElementList => "element-list",
            Self::Other => "other",
        }
    }

    /// Whether the class's answer is undecided, so that a disagreement is counted, not failed.
    const fn open(self) -> bool {
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

/// A sort declaration with `parents`, keyed as the collector keys one.
fn sort_with_parents(id: StableItemId, parents: &[StableItemId]) -> DescriptorInputs {
    let parents = parents
        .iter()
        .zip(0..)
        .map(|(sort, ordinal)| DescriptorSortParent {
            sort: sort.clone(),
            key: configuration::key(ProvenanceRole::SortParent, ordinal),
        })
        .collect::<BTreeSet<_>>();
    DescriptorInputs::new(
        id,
        BTreeMap::new(),
        configuration::provenance(
            configuration::key(ProvenanceRole::SortDeclaration, 0),
            parents.iter().map(|parent| parent.key.clone()),
        ),
        DescriptorPayload::Sort(SortDescriptor { parents }),
    )
}

/// The definitions the judges are compared on: the fixture bundles, and edits of them that
/// declare a chain of sorts beside one with an explicit `KItem` parent, and put a builtin sort
/// below a chain that ends at `KItem`. A definition emits `KItem` only when it uses it, so only
/// the edits ask the judges about it.
fn definitions() -> Vec<(&'static str, DescriptorBundleInputs)> {
    let configuration = configuration::bundle();

    let mut chain = configuration.clone();
    let stmt = configuration::id("Stmt", ItemKind::Sort);
    let value = configuration::id("Value", ItemKind::Sort);
    let code = configuration::id("Code", ItemKind::Sort);
    chain
        .descriptors
        .retain(|descriptor| descriptor.id != value);
    chain.descriptors.extend([
        sort_with_parents(stmt.clone(), &[]),
        sort_with_parents(value, &[stmt]),
        sort_with_parents(code, &[configuration::framework_kitem()]),
    ]);

    let (grammar, _) = grammar::bundle();
    let mut builtin = grammar.clone();
    grammar::add_builtin_expr_subsort(&mut builtin, BuiltinSort::Int, "Int");
    let expr = grammar::id("Expr", ItemKind::Sort);
    builtin
        .descriptors
        .retain(|descriptor| descriptor.id != expr);
    builtin
        .descriptors
        .push(sort_with_parents(expr, &[configuration::framework_kitem()]));

    vec![
        ("configuration", configuration),
        ("configuration-sort-chain", chain),
        ("grammar", grammar),
        ("grammar-builtin-subsort", builtin),
    ]
}

fn read_pending() -> Pending {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/class-matrix/pending.toml");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    Pending::parse(&text).unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"))
}

/// The disagreements of one pair of judges about one class: how many sort pairs the first
/// judge holds and the second does not, and the converse.
#[derive(Default)]
struct Count {
    first_only: usize,
    second_only: usize,
}

impl Count {
    fn signature(&self, first: SortJudge, second: SortJudge) -> String {
        format!(
            "{} pairs only {} holds; {} pairs only {} holds",
            self.first_only,
            first.name(),
            self.second_only,
            second.name()
        )
    }
}

/// The disagreements of every pair of judges over every ordered pair of distinct sorts, by
/// class; counts in `unanimous_no` the pairs of an open class that every judge refuses.
fn disagreements(
    judges: &SortJudges,
    unanimous_no: &mut BTreeMap<Class, usize>,
) -> BTreeMap<(SortJudge, SortJudge, Class), Count> {
    let mut counts = BTreeMap::<(SortJudge, SortJudge, Class), Count>::new();
    let sorts = judges.sorts();
    for candidate in sorts {
        for expected in sorts.iter().filter(|expected| *expected != candidate) {
            let answers =
                SortJudge::ALL.map(|judge| (judge, judges.is_subsort(judge, candidate, expected)));
            let class = class(judges, candidate, expected);
            if class.open() && answers.iter().all(|(_, holds)| !holds) {
                *unanimous_no.entry(class).or_default() += 1;
            }
            for (index, &(first, first_holds)) in answers.iter().enumerate() {
                for &(second, second_holds) in &answers[index + 1..] {
                    if first_holds == second_holds {
                        continue;
                    }
                    let count = counts.entry((first, second, class)).or_default();
                    if first_holds {
                        count.first_only += 1;
                    } else {
                        count.second_only += 1;
                    }
                }
            }
        }
    }
    counts
}

/// The failures, and the `pending.toml` entries that would record their new deviations.
fn failure_message(failures: &[(&String, Judgement)]) -> String {
    let mut message = format!("{} sort-judge disagreements fail:\n", failures.len());
    for (id, judgement) in failures {
        writeln!(message, "  {id}: {judgement}").expect("writing to a String");
    }
    message.push_str("\nTo record the new deviations in pending.toml:\n\n");
    for (id, judgement) in failures {
        if let Judgement::Unexpected { observed } | Judgement::DeviationChanged { observed, .. } =
            judgement
        {
            writeln!(
                message,
                "[{id:?}]\nfinding = \"{UNASSIGNED}\"\ndeviation = {observed:?}\n"
            )
            .expect("writing to a String");
        }
    }
    message
}

#[test]
fn the_krs_sort_judges_agree() {
    let pending = read_pending();
    let mut observed = BTreeMap::<String, String>::new();
    let mut report = String::new();
    let mut open = BTreeMap::<Class, usize>::new();
    let mut unanimous_no = BTreeMap::<Class, usize>::new();
    for (name, inputs) in definitions() {
        let bundle = inputs
            .build()
            .unwrap_or_else(|error| panic!("{name}: the bundle builds: {error}"));
        let judges = SortJudges::of_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{name}: the bundle lowers: {error}"));
        let counts = disagreements(&judges, &mut unanimous_no);
        let sorts = judges.sorts();
        writeln!(
            report,
            "{name}: {} sorts, {} ordered pairs",
            sorts.len(),
            sorts.len() * (sorts.len() - 1)
        )
        .expect("writing to a String");
        for ((first, second, class), count) in &counts {
            let signature = count.signature(*first, *second);
            writeln!(
                report,
                "  {} ~ {} {}: {signature}",
                first.name(),
                second.name(),
                class.name()
            )
            .expect("writing to a String");
            if class.open() {
                *open.entry(*class).or_default() += count.first_only + count.second_only;
            } else {
                observed.insert(
                    format!(
                        "lattice/{name}/{}~{}/{}",
                        first.name(),
                        second.name(),
                        class.name()
                    ),
                    signature,
                );
            }
        }
    }
    for class in [Class::KItemK, Class::ElementList] {
        writeln!(
            report,
            "{}: {} disagreements (counted, not failed); {} pairs every judge refuses",
            class.name(),
            open.get(&class).copied().unwrap_or(0),
            unanimous_no.get(&class).copied().unwrap_or(0),
        )
        .expect("writing to a String");
    }

    // The full tier records its own definitions' disagreements under `lattice/class-..`.
    let names = definitions()
        .into_iter()
        .map(|(name, _)| format!("{LATTICE}{name}/"))
        .collect::<Vec<_>>();
    let recorded = pending
        .entries
        .keys()
        .filter(|id| names.iter().any(|name| id.starts_with(name)))
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut red = Vec::new();
    let mut failures = Vec::new();
    for id in recorded
        .iter()
        .chain(observed.keys())
        .collect::<BTreeSet<_>>()
    {
        let observation = observed.get(id).map_or(Observation::Conforms, |signature| {
            Observation::Deviates(signature)
        });
        match pending.judge(id, observation) {
            Judgement::Conforms => {}
            Judgement::Red => red.push(id.as_str()),
            judgement => failures.push((id, judgement)),
        }
    }
    let tally = pending.tally(red.iter().copied());
    writeln!(report, "{} red as pending.toml records", red.len()).expect("writing to a String");
    for (finding, count) in &tally.by_finding {
        writeln!(report, "  red by finding {finding}: {count}").expect("writing to a String");
    }
    eprint!("{report}");

    assert!(failures.is_empty(), "{}", failure_message(&failures));
}
