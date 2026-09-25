//! ```toml algorithm-site
//! id = "kompile.sort_helpers.generate"
//! role = "part"
//! sites = ["subsort_kitem", "subsort_kitem_pass"]
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Add backend subsort declarations from every user sort to `KItem`.

use std::{fmt, sync::Arc};

use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, PartialOrder, ProductionItem, Sentence, retain_new_sentences,
    },
    kast::{FrontendSort, Sort},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SubsortKItemError(pub String);

impl fmt::Display for SubsortKItemError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for SubsortKItemError {}

/// Apply Java's `Kompile.subsortKItem` module transformation.
pub fn subsort_kitem(definition: &Definition) -> Result<Definition, SubsortKItemError> {
    super::super::pipeline::run_standalone(
        definition,
        subsort_kitem_pass,
        Some(GeneratingPass::SubsortKItem),
    )
}

pub(crate) fn subsort_kitem_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, SubsortKItemError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| SubsortKItemError(error.to_string()))?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = views.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        // Invariant: `generated` holds a `KItem ::= Sort` subsort production for every non-parser sort of `sorts.all_sorts()` before `sort`; each iteration consumes one sort.
        for sort in sorts.all_sorts() {
            if is_parser_sort(sort) {
                continue;
            }
            let production = Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::KItem),
                items: vec![ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                }],
                attributes: Attributes::default(),
            };
            generated.push(production);
        }
        let generated = retain_new_sentences(
            visible
                .iter()
                .copied()
                .chain(module.local_sentences.iter().map(Arc::as_ref)),
            generated,
        );
        module
            .local_sentences
            .extend(generated.into_iter().map(Arc::new));
    }
    Ok(output)
}

/// `subsorts` with the `KItem ::= S` subsorts this stage adds for every sort `S` of `sorts` that is
/// not a parser sort: the order sort injection works in after this stage has run.
pub(crate) fn with_kitem_subsorts<'a>(
    subsorts: &PartialOrder<Sort>,
    sorts: impl IntoIterator<Item = &'a Sort>,
) -> Result<PartialOrder<Sort>, crate::definition::PartialOrderCycle<Sort>> {
    let kitem = Sort::builtin(BuiltinSort::KItem);
    PartialOrder::new(
        subsorts.direct_relations().iter().cloned().chain(
            sorts
                .into_iter()
                .filter(|sort| !is_parser_sort(sort))
                .map(|sort| (sort.clone(), kitem.clone())),
        ),
    )
}

/// Whether a single `inj{actual, expected}` is justified: `actual <= expected` along subsort axioms
/// of the emitted theory.
///
/// Those axioms are the declared subsorts except the ones into `K` (the emitted definition has no
/// subsort axiom into `K`: a `KItem` becomes a `K` as a one-element sequence, not by injection),
/// plus `S <= KItem` for every sort `S` that is not a parser sort, which this stage declares and
/// which semantic-cast resolution and sort injection may need before it has run. The relation is
/// their transitive closure; it continues above `KItem` only through declared supersorts of
/// `KItem` that are not reached through `K`.
pub(crate) fn injectable(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    if actual == expected {
        return true;
    }
    let k = Sort::builtin(BuiltinSort::K);
    if expected == &k {
        return false;
    }
    let k_item = Sort::builtin(BuiltinSort::KItem);
    if subsorts.less_than_eq(&k, expected) {
        return injectable_path(actual, expected, subsorts);
    }
    // No path to `expected` passes through `K`, since `K` is not below it.
    subsorts.less_than_eq(actual, expected)
        || ((expected == &k_item || subsorts.less_than_eq(&k_item, expected))
            && reaches_k_item(actual, subsorts))
}

/// Whether compilation can place a term of sort `actual` at a position of sort `expected`: by one
/// injection ([`injectable`]); at a `K` position as the one-element sequence of a `KItem`; or at a
/// position above `K` as the injection of that sequence (`inj{K, expected}` of `actual ~> .K`).
/// Collection and user-list positions, where the injector also wraps an element, are the
/// injector's own concern.
pub(crate) fn placeable(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k = Sort::builtin(BuiltinSort::K);
    injectable(actual, expected, subsorts)
        || (injectable(actual, &Sort::builtin(BuiltinSort::KItem), subsorts)
            && (expected == &k || injectable(&k, expected, subsorts)))
}

/// Whether `actual <= KItem` along the axioms of [`injectable`], none of which leads out of `K`.
fn reaches_k_item(actual: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k = Sort::builtin(BuiltinSort::K);
    let k_item = Sort::builtin(BuiltinSort::KItem);
    actual == &k_item
        || subsorts.less_than_eq(actual, &k_item)
        || !is_parser_sort(actual)
        || subsorts.relations_from(actual).is_some_and(|supersorts| {
            supersorts
                .iter()
                .any(|sort| !is_parser_sort(sort) && !subsorts.less_than_eq(&k, sort))
        })
}

/// [`injectable`] for an `expected` above `K`: a search over the axioms, which excludes the
/// declared edges into `K`.
// Invariant: `seen` holds every sort reached from `actual` so far, each expanded once, so the search visits at most every declared sort plus `KItem`, scanning the direct relations once per sort.
fn injectable_path(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    let k = Sort::builtin(BuiltinSort::K);
    let k_item = Sort::builtin(BuiltinSort::KItem);
    let mut seen = std::collections::BTreeSet::from([actual.clone()]);
    let mut pending = vec![actual.clone()];
    while let Some(sort) = pending.pop() {
        if &sort == expected {
            return true;
        }
        let implicit = (!is_parser_sort(&sort)).then(|| k_item.clone());
        let declared = subsorts
            .direct_relations()
            .iter()
            .filter(|(lesser, greater)| *lesser == sort && *greater != k)
            .map(|(_, greater)| greater.clone());
        for next in declared.chain(implicit) {
            if seen.insert(next.clone()) {
                pending.push(next);
            }
        }
    }
    false
}

/// A sort of K's own term syntax (`K`, `KItem`, `KConfigVar`, `KBott`, `KLabel`, `KList`, `KString`,
/// a `#`-prefixed sort, or a numeric sort argument), which this stage does not place below `KItem`.
pub(super) fn is_parser_sort(sort: &Sort) -> bool {
    [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
        .iter()
        .any(|builtin| sort.name == builtin.k_name())
        || [
            FrontendSort::KBott,
            FrontendSort::KLabel,
            FrontendSort::KList,
            FrontendSort::KString,
        ]
        .iter()
        .any(|frontend| sort.name == frontend.as_str())
        || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}
