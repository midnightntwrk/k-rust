//! Initializer and covering-lambda totality is decided after written equations and macro expansions are available.
//! For I initializer and deferred lambda labels, T RHS nodes and U child-unit obligations, the least fixed point takes at most I changing rounds, O(I x (I + T + U) x log P) plus the main-module EquationTotality judgement and resolution.
//! RHS preparation allocates O(T + U) once.
#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::head_totality::{
    CollectionLiterals, EquationTotality, is_true, term_is_defined_with,
};
use crate::definition::totality::TotalityWitness;
use crate::definition::{AttributeKey, ProductionItem, ResolveError, Sentence, match_rule_label};
use crate::kast::{InternalLabel, Label, Sort, Term};
use crate::provenance::GeneratingPass;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn declare_deferred_totality_pass(
    input: &super::super::pipeline::PassInput<'_>,
    state: &mut super::super::pipeline::PipelineState,
) -> Result<super::super::pipeline::PassOutcome, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let main = resolved.main_module_id();
    let productions = resolved.production_catalog(main);
    let main_rules = deferred_equations::MainRules::new(resolved);
    let rules = main_rules.catalog();
    let totality = resolved
        .overloads(main)
        .ok()
        .map(|overloads| EquationTotality::judge(&productions, rules, &overloads));
    let lambdas = state
        .covering_lambdas
        .iter()
        .map(|lambda| (lambda.label().to_owned(), lambda))
        .collect::<BTreeMap<_, _>>();
    let mut headed = BTreeSet::new();
    for (_, rule) in rules.rules() {
        if !rule.attributes().has(AttributeKey::Simplification) {
            headed.insert(match_rule_label(rule).name);
        }
    }
    let mut deferred_labels = BTreeSet::new();
    let mut cells = BTreeSet::new();
    let mut defined = BTreeSet::new();
    let mut units = BTreeMap::<Sort, BTreeSet<String>>::new();
    for (_, production) in productions.productions() {
        if let Sentence::Production {
            sort, attributes, ..
        } = production
            && (attributes.has(AttributeKey::Cell) || attributes.has(AttributeKey::CellCollection))
            && let Some(unit) = attributes.string(AttributeKey::Unit)
        {
            units
                .entry(sort.clone())
                .or_default()
                .insert(unit.to_owned());
        }
    }
    let mut child_units = BTreeMap::<String, BTreeSet<String>>::new();
    // Generation receipts separate configuration products from source-written markers.
    // Signatures separate nullary initializers from configuration-map readers.
    // Collect cell boundaries and evidently defined hooked units before deferred dependencies.
    for (_, production) in productions.productions() {
        let Sentence::Production {
            label: Some(label),
            items,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if production
            .attributes()
            .origin_record()
            .is_some_and(|origin| origin.pass == GeneratingPass::ResolveFun)
            && attributes.has(AttributeKey::Function)
            && !attributes.has(AttributeKey::Total)
            && lambdas.contains_key(&label.name)
        {
            deferred_labels.insert(label.name.clone());
        }
        if !configuration_generated(production) {
            continue;
        }
        if attributes.has(AttributeKey::Cell) {
            cells.insert(label.name.clone());
            let required = child_units.entry(label.name.clone()).or_default();
            for item in items {
                if let ProductionItem::NonTerminal { sort, .. } = item
                    && let Some(units) = units.get(sort)
                {
                    required.extend(units.iter().cloned());
                }
            }
        }
        // Ordinary cell constructors and optional units use EquationTotality below: source
        // equations or a merged function property can make a generated label partial.
        // Hooked collection units build the empty collection despite lacking a total marker,
        // but any non-simplification rule headed by the unit can change that meaning.
        // The unit's own receipt supplies its origin; a cell's source-written unit property
        // cannot supply evidence.
        if matches!(items.as_slice(), [ProductionItem::Terminal(_)])
            && attributes.has(AttributeKey::Function)
            && matches!(
                attributes.string(AttributeKey::Hook),
                Some("BAG.unit" | "SET.unit" | "MAP.unit" | "LIST.unit")
            )
            && !headed.contains(&label.name)
        {
            defined.insert(label.name.clone());
        }
        if attributes.has(AttributeKey::Initializer)
            && attributes.has(AttributeKey::Function)
            && matches!(items.as_slice(), [ProductionItem::Terminal(_)])
        {
            deferred_labels.insert(label.name.clone());
        }
    }
    let collections = CollectionLiterals::of(&productions, &headed);
    let deferred_rules = DeferredEquations::gather(
        &main_rules,
        deferred_labels,
        &cells,
        &child_units,
        collections,
    );
    let proven = proven_deferred_labels(&deferred_rules, &lambdas, &defined, totality.as_ref());
    let mut declarations = Vec::new();
    // Gather proven writes before cloning: an empty set preserves the input and its views.
    for (module_index, module) in input.definition.modules.iter().enumerate() {
        for (sentence_index, sentence) in module.local_sentences.iter().enumerate() {
            let Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } = &**sentence
            else {
                continue;
            };
            let initializer = configuration_generated(sentence)
                && attributes.has(AttributeKey::Initializer)
                && matches!(items.as_slice(), [ProductionItem::Terminal(_)]);
            let lambda = lambdas.get(&label.name).filter(|_| {
                attributes
                    .origin_record()
                    .is_some_and(|origin| origin.pass == GeneratingPass::ResolveFun)
            });
            if (!initializer && lambda.is_none())
                || attributes.has(AttributeKey::Total)
                || productions.find_equivalent(sentence).is_none()
                || !attributes.has(AttributeKey::Function)
                || !proven.contains(&label.name)
            {
                continue;
            }
            // Only the complete all-equations judgement can mint evidence, after its fixed point.
            let mut label_is_defined = |label: &Label| {
                deferred_label_is_defined(
                    label,
                    &deferred_rules,
                    &proven,
                    &defined,
                    totality.as_ref(),
                )
            };
            let witness = if let Some(lambda) = lambda {
                TotalityWitness::defined_body(
                    defined_lambda(lambda, &deferred_rules, &mut label_is_defined)
                        .expect("the fixed point established every lambda equation"),
                )
            } else {
                TotalityWitness::nullary_initializer(
                    deferred_rules
                        .defined_initializer(&label.name, &mut label_is_defined)
                        .expect("the fixed point established every initializer equation"),
                )
            };
            declarations.push((module_index, sentence_index, witness));
        }
    }
    if declarations.is_empty() {
        return Ok(super::super::pipeline::PassOutcome::Unchanged);
    }
    let mut output = input.definition.clone();
    for (module, sentence, witness) in declarations {
        crate::definition::sentence_mut(&mut output.modules[module].local_sentences[sentence])
            .attributes_mut()
            .declare_total(witness);
    }
    Ok(super::super::pipeline::PassOutcome::Changed(output))
}

// Fresh-constant resolution expands the generated counter configuration and restamps its
// new productions. Existing configuration productions retain their expansion receipts.
fn configuration_generated(sentence: &Sentence) -> bool {
    sentence.attributes().origin_record().is_some_and(|origin| {
        matches!(
            origin.pass,
            GeneratingPass::ConfigurationExpansion | GeneratingPass::ResolveFreshConstants
        )
    })
}

/// Evidence that an unconditional equation covers the nullary initializer's only argument tuple
/// and every equation builds a defined value with a trivial postcondition.
pub(crate) struct DefinedInitializer(());

struct DeferredRule {
    // Collected with generated-cell boundary frames already removed.
    rule_right: Term,
    requires: Term,
    ensures: Term,
    child_units: BTreeSet<String>,
}

fn initializer_child_units(
    term: &Term,
    child_units: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    let mut required = BTreeSet::new();
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && let Some(units) = child_units.get(&label.name)
        {
            required.extend(units.iter().cloned());
        }
    });
    required
}

fn deferred_result_is_defined(
    rule: &DeferredRule,
    collections: &CollectionLiterals,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    is_true(&rule.ensures)
        && term_is_defined_with(&rule.rule_right, collections, defined)
        && rule
            .child_units
            .iter()
            .all(|unit| defined(&Label::new(unit)))
}

fn initializer_rules_are_defined(
    rules: &[DeferredRule],
    collections: &CollectionLiterals,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    // A partial function needs an applicable equation, not only defined possible results.
    // Nullary signatures have one argument tuple, covered by any unconditional equation.
    rules.iter().any(|rule| is_true(&rule.requires))
        && rules
            .iter()
            .all(|rule| deferred_result_is_defined(rule, collections, defined))
}

pub(super) use deferred_equations::DeferredEquations;

mod deferred_equations {
    use super::*;
    use crate::definition::{ResolvedDefinition, RuleCatalog};
    use crate::kompile::passes::resolve_fun::CoveringLambda;

    // This wrapper selects the main module once, so gathering cannot use a module-local catalog
    // that omits equations contributed by an importer in the emitted theory.
    pub(super) struct MainRules<'a>(RuleCatalog<'a>);

    impl<'a> MainRules<'a> {
        pub(super) fn new(resolved: &'a ResolvedDefinition) -> Self {
            Self(resolved.rule_catalog(resolved.main_module_id()))
        }

        pub(super) fn catalog(&self) -> &RuleCatalog<'a> {
            &self.0
        }
    }

    /// Complete main-module catalog equations for each deferred label, indexed by their matched heads.
    /// The map is private; only catalog gathering can populate it, and the lambda judgement
    /// looks up the covering receipt's label itself rather than accepting an equation slice.
    pub(in crate::kompile::passes) struct DeferredEquations {
        equations_by_label: BTreeMap<String, Vec<DeferredRule>>,
        collections: CollectionLiterals,
    }

    impl DeferredEquations {
        pub(super) fn gather(
            main_rules: &MainRules<'_>,
            labels: BTreeSet<String>,
            cells: &BTreeSet<String>,
            child_units: &BTreeMap<String, BTreeSet<String>>,
            collections: CollectionLiterals,
        ) -> Self {
            let mut equations_by_label = labels
                .into_iter()
                .map(|label| (label, Vec::new()))
                .collect::<BTreeMap<_, _>>();
            for (_, rule) in main_rules.catalog().rules() {
                let Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                } = rule
                else {
                    unreachable!("rule catalogs contain rules")
                };
                let label = match_rule_label(rule);
                if let Some(equations) = equations_by_label.get_mut(&label.name) {
                    let rule_right = match body.unannotated() {
                        Term::Rewrite { right, .. } => &**right,
                        Term::As { .. }
                        | Term::Apply { .. }
                        | Term::Sequence(_)
                        | Term::Variable { .. }
                        | Term::Token { .. }
                        | Term::InjectedLabel(_) => body,
                        Term::Annotated { .. } => {
                            unreachable!("unannotated terms carry no annotation")
                        }
                    };
                    equations.push(DeferredRule {
                        // Boundary syntax is independent of the proven-label set; erase it once.
                        rule_right: without_initializer_frames(rule_right, cells),
                        requires: requires.clone(),
                        ensures: ensures.clone(),
                        // Cell closing fills absent optional/collection slots with these units.
                        // Check all possible insertions rather than duplicating its placement analysis.
                        // This may withhold evidence when a partial unit's slot is already populated.
                        child_units: initializer_child_units(rule_right, child_units),
                    });
                }
            }
            Self {
                equations_by_label,
                collections,
            }
        }

        pub(super) fn labels(&self) -> impl Iterator<Item = &String> {
            self.equations_by_label.keys()
        }

        pub(super) fn contains(&self, label: &str) -> bool {
            self.equations_by_label.contains_key(label)
        }

        pub(super) fn defined_initializer(
            &self,
            label: &str,
            defined: &mut dyn FnMut(&Label) -> bool,
        ) -> Option<DefinedInitializer> {
            super::defined_initializer(
                self.equations_by_label.get(label)?,
                &self.collections,
                defined,
            )
        }

        pub(in crate::kompile::passes) fn lambda_is_defined(
            &self,
            lambda: &CoveringLambda,
            defined: &mut dyn FnMut(&Label) -> bool,
        ) -> bool {
            self.equations_by_label
                .get(lambda.label())
                .is_some_and(|rules| {
                    !rules.is_empty()
                        && rules.iter().all(|rule| {
                            is_true(&rule.requires)
                                && deferred_result_is_defined(rule, &self.collections, defined)
                        })
                })
        }
    }
}

fn defined_lambda(
    lambda: &super::resolve_fun::CoveringLambda,
    equations: &DeferredEquations,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> Option<super::resolve_fun::DefinedBody> {
    lambda.defined_body(equations, defined)
}

fn deferred_rules_are_defined(
    label: &str,
    equations: &DeferredEquations,
    lambdas: &BTreeMap<String, &super::resolve_fun::CoveringLambda>,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> bool {
    if let Some(lambda) = lambdas.get(label) {
        defined_lambda(lambda, equations, defined).is_some()
    } else {
        equations.defined_initializer(label, defined).is_some()
    }
}

fn defined_initializer(
    rules: &[DeferredRule],
    collections: &CollectionLiterals,
    defined: &mut dyn FnMut(&Label) -> bool,
) -> Option<DefinedInitializer> {
    if initializer_rules_are_defined(rules, collections, defined) {
        Some(DefinedInitializer(()))
    } else {
        None
    }
}

/// Before cell closing, boundary #noDots applications describe the absence of a frame.
/// Erase only that positional syntax so the shared term judgement still checks every content term.
fn without_initializer_frames(term: &Term, generated_cells: &BTreeSet<String>) -> Term {
    match term.unannotated() {
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .enumerate()
                .filter(|(index, argument)| {
                    let boundary = generated_cells.contains(&label.name)
                        && (*index == 0 || *index + 1 == arguments.len());
                    let marker = matches!(argument.unannotated(), Term::Apply { label, arguments }
                        if label.is(InternalLabel::NoDots) && arguments.is_empty());
                    !(boundary && marker)
                })
                .map(|(_, argument)| without_initializer_frames(argument, generated_cells))
                .collect(),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| without_initializer_frames(item, generated_cells))
                .collect(),
        ),
        Term::Variable { .. }
        | Term::Token { .. }
        | Term::InjectedLabel(_)
        | Term::Rewrite { .. }
        | Term::As { .. } => term.unannotated().clone(),
        Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
    }
}

fn proven_deferred_labels(
    rules: &DeferredEquations,
    lambdas: &BTreeMap<String, &super::resolve_fun::CoveringLambda>,
    generated_defined_labels: &BTreeSet<String>,
    totality: Option<&EquationTotality>,
) -> BTreeSet<String> {
    let mut proven = BTreeSet::new();
    // Every changing round admits at least one label, and admission only grows.
    // Thus at most |rules| changing rounds precede the fixed point; cycles cannot prove themselves.
    loop {
        let before = proven.len();
        for label in rules.labels() {
            if !proven.contains(label)
                && deferred_rules_are_defined(label, rules, lambdas, &mut |label| {
                    deferred_label_is_defined(
                        label,
                        rules,
                        &proven,
                        generated_defined_labels,
                        totality,
                    )
                })
            {
                proven.insert(label.clone());
            }
        }
        if proven.len() == before {
            return proven;
        }
    }
}

fn deferred_label_is_defined(
    label: &Label,
    rules: &DeferredEquations,
    proven: &BTreeSet<String>,
    generated_defined_labels: &BTreeSet<String>,
    totality: Option<&EquationTotality>,
) -> bool {
    // Collected equations decide deferred generated labels, even if a source declaration
    // already names one; an earlier declaration cannot bypass the all-equations judgement.
    if rules.contains(&label.name) {
        proven.contains(&label.name)
    } else {
        generated_defined_labels.contains(&label.name)
            || label.is(InternalLabel::Cells)
            || totality.is_some_and(|t| t.label_is_defined(label))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{Attributes, Definition, FlatModule};
    use crate::names::BuiltinSort;
    use std::sync::Arc;
    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::builtin(BuiltinSort::Bool),
        }
    }
    fn incomplete_cell(label: &str, content: Term) -> Term {
        let marker = Term::apply(InternalLabel::NoDots.as_str(), vec![]);
        Term::apply(label, vec![marker.clone(), content, marker])
    }
    fn covering_lambda() -> super::super::resolve_fun::CoveringLambda {
        let int = Sort::builtin(BuiltinSort::Int);
        let variable = Term::Variable {
            name: "X".into(),
            sort: Some(int.clone()),
        };
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: vec![],
                local_sentences: vec![
                    Arc::new(Sentence::SyntaxSort {
                        parameters: vec![],
                        sort: int.clone(),
                        attributes: Attributes::default(),
                    }),
                    Arc::new(Sentence::Rule {
                        body: Term::apply(
                            "#fun3",
                            vec![
                                Term::apply("#SemanticCastToInt", vec![variable.clone()]),
                                variable,
                                Term::Token {
                                    token: "1".into(),
                                    sort: int,
                                },
                            ],
                        ),
                        requires: truth(),
                        ensures: truth(),
                        attributes: Attributes::default(),
                    }),
                ],
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        super::super::super::pipeline::run_standalone_raw(&definition, |input, state| {
            super::super::resolve_fun::resolve_fun_pass(input, state).unwrap();
            assert_eq!(state.covering_lambdas.len(), 1);
            Ok::<_, std::convert::Infallible>(state.covering_lambdas.pop().unwrap())
        })
        .unwrap()
    }

    fn equation(label: &str, right: Term, requires: Term, ensures: Term) -> Sentence {
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply(label, vec![Term::variable("X")])),
                right: Box::new(right),
            },
            requires,
            ensures,
            attributes: Attributes::default(),
        }
    }

    fn catalog_equations(
        labels: BTreeSet<String>,
        rules: Vec<Sentence>,
        cells: &BTreeSet<String>,
        child_units: &BTreeMap<String, BTreeSet<String>>,
    ) -> DeferredEquations {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: vec![],
                local_sentences: rules.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        let resolved = crate::definition::ResolvedDefinition::resolve(&definition).unwrap();
        DeferredEquations::gather(
            &deferred_equations::MainRules::new(&resolved),
            labels,
            cells,
            child_units,
            CollectionLiterals::default(),
        )
    }

    #[test]
    fn deferred_lambda_evidence_requires_unconditional_equations() {
        let lambda = covering_lambda();
        let unconditional = || equation(lambda.label(), Term::variable("X"), truth(), truth());
        let conditional = || {
            equation(
                lambda.label(),
                Term::variable("X"),
                Term::variable("Condition"),
                truth(),
            )
        };
        let judge = |rules| {
            let equations = catalog_equations(
                BTreeSet::from([lambda.label().to_owned()]),
                rules,
                &BTreeSet::new(),
                &BTreeMap::new(),
            );
            defined_lambda(&lambda, &equations, &mut |_| false).is_some()
        };
        assert!(judge(vec![unconditional()]));
        assert!(!judge(vec![conditional()]));
        assert!(!judge(vec![unconditional(), conditional()]));
        assert!(!judge(vec![]));
        assert!(!judge(vec![equation(
            lambda.label(),
            Term::variable("X"),
            truth(),
            Term::variable("Postcondition"),
        )]));
        assert!(!judge(vec![equation(
            lambda.label(),
            Term::apply("partial", vec![]),
            truth(),
            truth(),
        )]));
        let equations = catalog_equations(
            BTreeSet::from([lambda.label().to_owned()]),
            vec![equation(
                lambda.label(),
                incomplete_cell("<n>", truth()),
                truth(),
                truth(),
            )],
            &BTreeSet::from(["<n>".into()]),
            &BTreeMap::from([("<n>".into(), BTreeSet::from(["partial".into()]))]),
        );
        assert!(defined_lambda(&lambda, &equations, &mut |label| label.name == "<n>").is_none());
    }

    #[test]
    fn deferred_lambda_evidence_cannot_use_another_labels_equations() {
        let lambda = covering_lambda();
        let labels = BTreeSet::from([lambda.label().to_owned(), "other".into()]);
        let own_equations = [
            vec![],
            vec![equation(
                lambda.label(),
                Term::variable("X"),
                Term::variable("Condition"),
                truth(),
            )],
            vec![equation(
                lambda.label(),
                Term::apply("partial", vec![]),
                truth(),
                truth(),
            )],
        ];
        for mut rules in own_equations {
            rules.push(equation("other", Term::variable("X"), truth(), truth()));
            let equations =
                catalog_equations(labels.clone(), rules, &BTreeSet::new(), &BTreeMap::new());
            assert!(
                equations
                    .defined_initializer("other", &mut |_| false)
                    .is_some()
            );
            assert!(
                defined_lambda(&lambda, &equations, &mut |_| false).is_none(),
                "another label's equations must not mint this lambda's DefinedBody"
            );
            let lambdas = BTreeMap::from([(lambda.label().to_owned(), &lambda)]);
            assert_eq!(
                proven_deferred_labels(&equations, &lambdas, &BTreeSet::new(), None),
                BTreeSet::from(["other".into()]),
            );
        }
    }

    #[test]
    fn initializer_frame_markers_are_only_syntax_at_generated_cell_boundaries() {
        let cells = BTreeSet::from(["<n>".to_owned()]);
        let marker = Term::apply(InternalLabel::NoDots.as_str(), vec![]);
        let value = truth();
        let judge = |term: &Term| {
            let rule = DeferredRule {
                rule_right: without_initializer_frames(term, &cells),
                requires: truth(),
                ensures: truth(),
                child_units: BTreeSet::new(),
            };
            defined_initializer(&[rule], &CollectionLiterals::default(), &mut |label| {
                cells.contains(&label.name) || label.name == "content"
            })
            .is_some()
        };
        assert!(judge(&incomplete_cell("<n>", value.clone())));
        assert!(!judge(&marker));
        assert!(!judge(&incomplete_cell("<n>", marker.clone())));
        assert!(!judge(&Term::apply(
            "content",
            vec![marker.clone(), value.clone(), marker.clone()],
        )));
        assert!(!judge(&incomplete_cell(
            "<n>",
            Term::apply("content", vec![marker.clone()]),
        )));
        assert!(!judge(&Term::apply(
            "<n>",
            vec![
                Term::apply(InternalLabel::NoDots.as_str(), vec![value.clone()]),
                value,
                marker
            ],
        )));
    }

    #[test]
    fn initializer_cycles_cannot_prove_themselves_even_with_a_defined_alternative() {
        let cells = BTreeSet::from(["<x>".to_owned(), "<y>".to_owned()]);
        let rule =
            |label, cell, child| equation(label, incomplete_cell(cell, child), truth(), truth());
        let rules = catalog_equations(
            BTreeSet::from(["initXCell".into(), "initYCell".into()]),
            vec![
                rule("initXCell", "<x>", truth()),
                rule("initXCell", "<x>", Term::apply("initYCell", vec![])),
                rule("initYCell", "<y>", Term::apply("initXCell", vec![])),
            ],
            &cells,
            &BTreeMap::new(),
        );
        assert!(proven_deferred_labels(&rules, &BTreeMap::new(), &cells, None).is_empty());
    }

    #[test]
    fn nullary_initializer_needs_unconditional_coverage_and_every_result_defined() {
        let conditional = || DeferredRule {
            rule_right: truth(),
            requires: Term::variable("Condition"),
            ensures: truth(),
            child_units: BTreeSet::new(),
        };
        let unconditional = || DeferredRule {
            requires: truth(),
            ..conditional()
        };
        let judge = |rules: &[DeferredRule]| {
            defined_initializer(rules, &CollectionLiterals::default(), &mut |_| false).is_some()
        };
        assert!(!judge(&[]));
        assert!(!judge(&[conditional()]));
        assert!(judge(&[unconditional()]));
        assert!(judge(&[conditional(), unconditional()]));
        assert!(judge(&[unconditional(), conditional()]));
        assert!(!judge(&[
            unconditional(),
            DeferredRule {
                rule_right: Term::apply("partial", vec![]),
                ..conditional()
            },
        ]));
        assert!(!judge(&[
            unconditional(),
            DeferredRule {
                ensures: Term::variable("Postcondition"),
                ..conditional()
            },
        ]));
    }
}
