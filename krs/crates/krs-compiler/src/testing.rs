//! Contract assertions for semantic lowering and canonical K emission, and KRS's sort judges.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::testing::assert_canonical_contract;
use krs_ir::{
    BuiltinSort, DescriptorBundle, GrammarProductionItemKind, OriginFrame, ProductionAttribute,
    RangedOriginKind, TransformationOriginKind,
};
use krs_ir_levels::{DefinitionSortRef, SemanticModule, SemanticSortRef, SemanticTheory};

use crate::{
    EmittedK, LoweredDefinition, SourceMap, emit_k, lower_descriptor_bundle, lower_semantic_theory,
};

/// Asserts canonical IR, deterministic lowering and emission, and complete provenance frames.
///
/// Returns the first lowered definition and emission for fixture-specific assertions.
/// The semantic theory must be valid for both lowering and emission.
///
/// # Panics
///
/// Panics if the theory is not canonical, lowering or emission fails, their results differ
/// between runs, or a source-map entry lacks the required provenance frames.
#[must_use]
pub fn assert_lowering_contract(theory: &SemanticTheory) -> (LoweredDefinition, EmittedK) {
    assert_canonical_contract(theory);

    let lowered = lower_semantic_theory(theory).expect("semantic theory must lower");
    let repeated = lower_semantic_theory(theory).expect("semantic theory must lower again");
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        repeated.definition().to_canonical_json().unwrap(),
        "DefinitionIr changed between lowering runs"
    );
    assert_eq!(
        lowered.source_map().to_canonical_json().unwrap(),
        repeated.source_map().to_canonical_json().unwrap(),
        "source map changed between lowering runs"
    );
    assert_eq!(
        lowered.symbol_map().to_canonical_json().unwrap(),
        repeated.symbol_map().to_canonical_json().unwrap(),
        "symbol map changed between lowering runs"
    );
    assert_canonical_contract(lowered.definition());
    assert_origin_frames(lowered.source_map(), "lowered");

    let emitted = emit_k(&lowered).expect("lowered definition must emit");
    let reemitted = emit_k(&lowered).expect("lowered definition must emit again");
    assert_eq!(
        emitted.source(),
        reemitted.source(),
        "K source changed between emissions"
    );
    assert_eq!(
        emitted.spec(),
        reemitted.spec(),
        "K specification changed between emissions"
    );
    assert_eq!(
        emitted.source_map().to_canonical_json().unwrap(),
        reemitted.source_map().to_canonical_json().unwrap(),
        "emitted source map changed between emissions"
    );
    assert_eq!(
        emitted.symbol_map().to_canonical_json().unwrap(),
        reemitted.symbol_map().to_canonical_json().unwrap(),
        "emitted symbol map changed between emissions"
    );
    assert_origin_frames(emitted.source_map(), "emitted");

    (lowered, emitted)
}

fn assert_origin_frames(map: &SourceMap, phase: &str) {
    for entry in map.entries() {
        assert!(
            matches!(
                entry.origin().frames().first(),
                Some(OriginFrame::Ranged {
                    kind: RangedOriginKind::Authored,
                    ..
                })
            ),
            "{phase} source-map entry {} must start with an authored frame",
            entry.key()
        );
        assert!(
            matches!(
                entry.origin().frames().last(),
                Some(OriginFrame::Transformation {
                    kind: TransformationOriginKind::DefinitionIr,
                    ..
                })
            ),
            "{phase} source-map entry {} must end with a DefinitionIr frame",
            entry.key()
        );
    }
}

/// One of KRS's sort judges: a subsort graph one stage builds for itself, and the subsort
/// question it answers over it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SortJudge {
    /// G1: the inference catalog that descriptor lowering builds from the bundle.
    Catalog,
    /// G2: the Semantic IR validator.
    SemanticValidator,
    /// G3: the Definition IR validator, over the sorts lowering names.
    DefinitionValidator,
    /// G4: the rule-overlap check.
    Overlap,
    /// G5: the coverage lint and the equation-overlap check.
    Coverage,
}

impl SortJudge {
    /// Every judge.
    pub const ALL: [Self; 5] = [
        Self::Catalog,
        Self::SemanticValidator,
        Self::DefinitionValidator,
        Self::Overlap,
        Self::Coverage,
    ];

    /// The judge's name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Catalog => "catalog",
            Self::SemanticValidator => "semantic-validator",
            Self::DefinitionValidator => "definition-validator",
            Self::Overlap => "overlap",
            Self::Coverage => "coverage",
        }
    }
}

type Judge = Box<dyn Fn(&SemanticSortRef, &SemanticSortRef) -> bool>;

/// Every KRS sort judge over one definition, and the sorts they judge: each builtin sort, each
/// declared sort, each sort a subsort sentence names, and each group cell's generated sort.
pub struct SortJudges {
    sorts: Vec<SemanticSortRef>,
    judges: Vec<(SortJudge, Judge)>,
    user_lists: BTreeSet<(SemanticSortRef, SemanticSortRef)>,
    definition_sorts: BTreeMap<SemanticSortRef, DefinitionSortRef>,
}

impl SortJudges {
    /// Lowers `bundle` through Semantic IR to Definition IR and builds every judge over it.
    ///
    /// # Errors
    ///
    /// Returns the error of the step that does not lower the bundle, or of a sort that the
    /// Definition IR does not name.
    pub fn of_bundle(bundle: &DescriptorBundle) -> Result<Self, String> {
        let catalog =
            crate::semantic::catalog_subsort_judge(bundle).map_err(|error| error.to_string())?;
        let theory = lower_descriptor_bundle(bundle).map_err(|error| error.to_string())?;
        let lowered = lower_semantic_theory(&theory).map_err(|error| error.to_string())?;
        let modules = theory.modules();

        let mut sorts = BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect::<BTreeSet<_>>();
        for module in modules {
            sorts.extend(
                module
                    .sorts()
                    .iter()
                    .map(|sort| SemanticSortRef::Declared(sort.id().clone())),
            );
            for edge in module.subsorts() {
                sorts.insert(edge.subsort().clone());
                sorts.insert(edge.supersort().clone());
            }
        }
        sorts.extend(crate::overlap::group_cell_sorts(modules));
        sorts.retain(|sort| !matches!(sort, SemanticSortRef::Parameter(_)));

        let lower_sort =
            crate::lowering::definition_sort_names(&theory).map_err(|error| error.to_string())?;
        let lowered_sorts = sorts
            .iter()
            .map(|sort| Ok((sort.clone(), lower_sort(sort)?)))
            .collect::<Result<BTreeMap<SemanticSortRef, DefinitionSortRef>, crate::LoweringError>>()
            .map_err(|error| error.to_string())?;
        let definition = lowered.definition().subsort_judge();
        let definition_sorts = lowered_sorts.clone();

        let mut user_lists = BTreeSet::new();
        for production in modules.iter().flat_map(SemanticModule::productions) {
            let cons = production
                .attributes()
                .iter()
                .any(|attribute| matches!(attribute, ProductionAttribute::ListCons { .. }));
            if !cons || !production.parameters().is_empty() {
                continue;
            }
            let list = production.result_sort();
            user_lists.extend(
                production
                    .items()
                    .iter()
                    .filter_map(|item| match item.kind() {
                        GrammarProductionItemKind::NonTerminal { sort, .. } if sort != list => {
                            Some((sort.clone(), list.clone()))
                        }
                        _ => None,
                    }),
            );
        }

        Ok(Self {
            sorts: sorts.into_iter().collect(),
            judges: vec![
                (SortJudge::Catalog, Box::new(catalog)),
                (
                    SortJudge::SemanticValidator,
                    Box::new(theory.subsort_judge()),
                ),
                (
                    SortJudge::DefinitionValidator,
                    Box::new(move |candidate, expected| {
                        definition(&lowered_sorts[candidate], &lowered_sorts[expected])
                    }),
                ),
                (
                    SortJudge::Overlap,
                    Box::new(crate::overlap::subsort_judge(modules)),
                ),
                (
                    SortJudge::Coverage,
                    Box::new(crate::coverage::subsort_judge(modules)),
                ),
            ],
            user_lists,
            definition_sorts,
        })
    }

    /// The sorts the judges are asked about.
    #[must_use]
    pub fn sorts(&self) -> &[SemanticSortRef] {
        &self.sorts
    }

    /// Whether `judge` holds `candidate` to be a subsort of `expected`.
    ///
    /// # Panics
    ///
    /// Panics if a sort is not one of [`Self::sorts`] and `judge` names sorts through lowering.
    #[must_use]
    pub fn is_subsort(
        &self,
        judge: SortJudge,
        candidate: &SemanticSortRef,
        expected: &SemanticSortRef,
    ) -> bool {
        let (_, judge) = self
            .judges
            .iter()
            .find(|(name, _)| *name == judge)
            .expect("every judge is built");
        judge(candidate, expected)
    }

    /// The Definition IR sort that lowering names `sort` by, for each of [`Self::sorts`]: how a
    /// judge over the emitted definition is asked about the same sort.
    #[must_use]
    pub fn definition_sort(&self, sort: &SemanticSortRef) -> Option<&DefinitionSortRef> {
        self.definition_sorts.get(sort)
    }

    /// The `(element, list)` sort pairs of the definition's user lists: the non-parametric
    /// productions with a list-cons attribute, by their other non-terminal.
    #[must_use]
    pub const fn user_lists(&self) -> &BTreeSet<(SemanticSortRef, SemanticSortRef)> {
        &self.user_lists
    }
}
