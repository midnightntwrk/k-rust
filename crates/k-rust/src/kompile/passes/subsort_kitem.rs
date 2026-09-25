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

/// Whether `actual <= expected` in the module's declared subsort order `subsorts` extended with
/// K's implicit sort structure: every sort that is not a parser sort is below `KItem` (the edges
/// this stage adds), and `KItem` is below `K`; the extension is transitive.
///
/// Semantic-cast resolution runs before this stage and sort injection may serve callers that never
/// ran it, so both compare sorts with this one relation rather than relying on the materialized
/// edges. A path through an implicit edge reaches `KItem` from `actual` (as `KItem` itself, a
/// declared subsort of `KItem`, a non-parser sort, or a sort declared below a non-parser sort)
/// and continues from `KItem` or `K` to `expected` along the declared order.
pub(crate) fn implicit_less_than_eq(
    actual: &Sort,
    expected: &Sort,
    subsorts: &PartialOrder<Sort>,
) -> bool {
    if actual == expected || subsorts.less_than_eq(actual, expected) {
        return true;
    }
    let k_item = Sort::builtin(BuiltinSort::KItem);
    let k = Sort::builtin(BuiltinSort::K);
    let from_k_item = expected == &k_item
        || expected == &k
        || subsorts.less_than_eq(&k_item, expected)
        || subsorts.less_than_eq(&k, expected);
    if !from_k_item {
        return false;
    }
    actual == &k_item
        || subsorts.less_than_eq(actual, &k_item)
        || !is_parser_sort(actual)
        || subsorts
            .relations_from(actual)
            .is_some_and(|supersorts| supersorts.iter().any(|sort| !is_parser_sort(sort)))
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
