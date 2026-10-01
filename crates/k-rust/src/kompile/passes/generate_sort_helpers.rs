//! ```toml algorithm
//! id = "kompile.sort_helpers.generate"
//! name = "generation of sort predicates, projections, and helper rules"
//! sites = ["generate_sort_predicate_syntax", "regenerate_sort_predicate_syntax", "generate_sort_projections"]
//! variable = "M = modules; S = visible sorts; V = visible sentences; D = sort-predicate productions declared locally, summed over modules; F = distinct result sorts of the productions that get a named field projection"
//! counters = []
//! no_counter = "sort-helper generation has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one definition, excluding the predicate rules"
//! bound = "O(M x (S + V log V) + F x (V + S log S))"
//!
//! [[cost]]
//! mode = "predicate rules (generate_sort_predicate_rules_pass)"
//! bound = "O(M x V log V + D x S log S) plus one forced subsort view per module"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! The field projections of a production are total only when it is the sole no-junk alternative of its sort; that judgement derives the alternatives of the sort from the main module once per sort (one scan of its productions and one of its sorts, O(V + S log S)), and only for the F sorts of productions with a named field.
//!
//! The predicate-rule step (`generate_sort_predicate_rules_pass` in `finalize.rs`) forces each module's subsort view and emits the `true` rule of a predicate only when its sort is placeable at `K`; that check scans the sort's supersorts in the closure, O(S log S).
//!
//! Generate sort predicates and projection functions consumed by later backend passes.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::definition::ResolveError;
use serde_json::{Value, json};

use crate::definition::production_kind::{ProductionKind, SortGenerators};
use crate::definition::totality::TotalityWitness;
use crate::definition::{AttributeKey, DefinitionViews, ModuleId, ProductionId};
use crate::kast::ProductionIdentity;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolvedDefinition,
        Sentence, SortCatalog, extend_with_new_sentences, retain_new_sentences,
    },
    kast::{Label, Sort, Term, parser::parse_sort},
    provenance::GeneratingPass,
};

/// Apply Java's `GenerateSortPredicateSyntax` transformation.
pub fn generate_sort_predicate_syntax(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(
        definition,
        generate_sort_predicate_syntax_pass,
        Some(GeneratingPass::GenerateSortPredicateSyntax),
    )
}

pub(crate) fn generate_sort_predicate_syntax_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    Ok(generate_sort_predicate_syntax_from_resolved(
        input.definition,
        resolved,
    ))
}

fn generate_sort_predicate_syntax_from_resolved(
    definition: &Definition,
    resolved: &ResolvedDefinition,
) -> Definition {
    let views = resolved.views();
    let mut output = definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let sorts = views.sort_catalog(module_id);
        let visible = resolved.sentences(module_id);
        let mut generated = Vec::new();
        // Predicate rules produce Boolean tokens even in standalone definitions.
        // Supply their token sort at the compilation root when the source does
        // not provide one. Imported prelude declarations remain authoritative.
        if module_id == resolved.main_module_id()
            && !sorts
                .token_sorts()
                .contains(&Sort::builtin(BuiltinSort::Bool))
        {
            let mut attributes = Attributes::default();
            attributes.mark(AttributeKey::Token);
            generated.push(Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::Bool),
                attributes,
            });
        }
        // A sort has a predicate exactly when its role says so; the rule grammar offers `isS(_)`
        // from the same predicate, so a rule can mention exactly the predicates declared here.
        // Invariant: `generated` holds the optional `Bool` token sort and the sort predicate production of every sort of `sorts.local_sorts()` before `sort` whose role has a sort predicate; each iteration consumes one sort.
        for sort in sorts
            .local_sorts()
            .iter()
            .filter(|sort| sort.role().has_sort_predicate())
        {
            let label = Label::sort_predicate(sort);
            let production = Sentence::Production {
                label: Some(label.clone()),
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::Bool),
                items: vec![
                    ProductionItem::Terminal(label.name.clone()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::builtin(BuiltinSort::K),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: {
                    let mut attributes = Attributes::from_pairs([
                        (AttributeKey::Function, Value::String(String::new())),
                        (AttributeKey::Predicate, sort_json(sort)),
                    ]);
                    attributes.declare_total(TotalityWitness::covering_predicate());
                    attributes
                },
            };
            generated.push(production);
        }
        let mut generated = retain_new_sentences(
            visible
                .iter()
                .copied()
                .chain(module.local_sentences.iter().map(Arc::as_ref)),
            generated,
        );
        if !generated.is_empty() {
            let k_sort = Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::builtin(BuiltinSort::K),
                attributes: Attributes::default(),
            };
            if !module
                .local_sentences
                .iter()
                .any(|sentence| **sentence == k_sort)
            {
                generated.push(k_sort);
            }
            module
                .local_sentences
                .extend(generated.into_iter().map(Arc::new));
        }
    }
    output
}

/// Restore generated sort predicates to their canonical unary signature after passes that may
/// temporarily add arguments, then generate predicates for any newly introduced sorts.
pub fn regenerate_sort_predicate_syntax(
    definition: &Definition,
) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(definition, regenerate_sort_predicate_syntax_pass, None)
}

pub(crate) fn regenerate_sort_predicate_syntax_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // Only labeled predicate productions change; taking a mutable sentence copies a
            // shared one.
            if !matches!(&**sentence, Sentence::Production { label: Some(_), attributes, .. }
                if attributes.has(AttributeKey::Predicate))
            {
                continue;
            }
            let sentence = crate::definition::sentence_mut(sentence);
            let Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            if !attributes.has(AttributeKey::Predicate) {
                continue;
            }
            *items = vec![
                ProductionItem::Terminal(label.name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::builtin(BuiltinSort::K),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ];
        }
    }
    Ok(generate_sort_predicate_syntax_from_resolved(
        &output, resolved,
    ))
}

/// Apply the non-coverage form of Java's `GenerateSortProjections` transformation.
pub fn generate_sort_projections(definition: &Definition) -> Result<Definition, ResolveError> {
    super::super::pipeline::run_standalone(
        definition,
        generate_sort_projections_pass,
        Some(GeneratingPass::GenerateSortProjections),
    )
}

pub(crate) fn generate_sort_projections_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveError> {
    let resolved = input.resolved_raw().map_err(Clone::clone)?;
    let views = resolved.views();
    let mut main_generators = MainSortGenerators::new(&views, resolved.main_module_id());
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let productions = views.production_catalog(module_id);
        let sorts = views.sort_catalog(module_id);
        let defined_labels = productions
            .defined_labels()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>();
        let local_productions = productions
            .productions()
            .filter(|(id, _)| productions.is_local(*id))
            .map(|(id, production)| (productions.identity(id), production.clone()))
            .collect::<Vec<_>>();
        let mut generated = Vec::new();
        // A sort has a projection exactly when its role says so; the rule grammar offers
        // `project:S(_)` from the same predicate.
        // Invariant: `generated` holds the projection production and rule of every sort of `sorts.all_sorts()` before `sort` whose role has a sort projection and whose projection label is not in `defined_labels`; each iteration consumes one sort.
        for sort in sorts.all_sorts() {
            if !sort.role().has_sort_projection() {
                continue;
            }
            let label = Label::projection(sort);
            if defined_labels.contains(&LabelHead::from(&label)) {
                continue;
            }
            generated.extend(sort_projection(sort, label));
        }
        // Invariant: `generated` also holds the named field projections of every production of `local_productions` before `production`; each iteration consumes one production.
        for (identity, production) in &local_productions {
            // A field projection derives from the one production that names the field.
            generated.extend(
                named_projections(production, *identity, &mut main_generators, &defined_labels)
                    .into_iter()
                    .map(|mut projection| {
                        projection
                            .attributes_mut()
                            .union_input_addresses(production.attributes());
                        projection
                    }),
            );
        }
        extend_with_new_sentences(&mut module.local_sentences, generated);
    }
    Ok(output)
}

fn sort_projection(sort: &Sort, label: Label) -> [Sentence; 2] {
    let variable = Term::Variable {
        name: "K".into(),
        sort: Some(sort.clone()),
    };
    let mut projection_attributes = Attributes::default();
    projection_attributes.mark(AttributeKey::Projection);
    let mut production_attributes = projection_attributes.clone();
    production_attributes.mark(AttributeKey::Function);
    [
        Sentence::Production {
            label: Some(label.clone()),
            parameters: Vec::new(),
            sort: sort.clone(),
            items: vec![
                ProductionItem::Terminal(label.name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::builtin(BuiltinSort::K),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes: production_attributes,
        },
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Apply {
                    label,
                    arguments: vec![variable.clone()],
                }),
                right: Box::new(variable),
            },
            requires: truth(),
            ensures: truth(),
            attributes: projection_attributes,
        },
    ]
}

fn named_projections(
    production: &Sentence,
    identity: ProductionIdentity,
    main_generators: &mut MainSortGenerators<'_, '_>,
    defined_labels: &std::collections::BTreeSet<LabelHead>,
) -> Vec<Sentence> {
    let Sentence::Production {
        label: Some(source_label),
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return Vec::new();
    };
    if !ProductionKind::of(production).admits_field_projection() {
        return Vec::new();
    }
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, name } => Some((sort, name)),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !nonterminals.iter().any(|(_, name)| name.is_some()) {
        return Vec::new();
    }
    if nonterminals
        .iter()
        .filter_map(|(_, name)| name.as_ref())
        .any(|name| {
            defined_labels.contains(&LabelHead::new(
                Label::field_projection(&source_label.name, name).name,
            ))
        })
    {
        return Vec::new();
    }
    let sole_generator = sole_generator(main_generators, identity, parameters, sort);
    let variables = nonterminals
        .iter()
        .enumerate()
        .map(|(index, (sort, _))| Term::Variable {
            name: format!("K{index}"),
            sort: Some((*sort).clone()),
        })
        .collect::<Vec<_>>();
    let mut generated = Vec::new();
    // Invariant: `generated` holds the projection production and rule of every named nonterminal of `nonterminals` before `index`; each iteration consumes one nonterminal.
    for (index, (field_sort, field_name)) in nonterminals.iter().enumerate() {
        let Some(field_name) = field_name else {
            continue;
        };
        let label = Label::field_projection(&source_label.name, field_name);
        let mut attributes = Attributes::default();
        attributes.mark(AttributeKey::Function);
        if let Some(sole_generator) = sole_generator {
            attributes.declare_total(TotalityWitness::sole_generator(sole_generator));
        }
        generated.push(Sentence::Production {
            label: Some(label.clone()),
            parameters: Vec::new(),
            sort: (*field_sort).clone(),
            items: vec![
                ProductionItem::Terminal(field_name.clone()),
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: sort.clone(),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            attributes,
        });
        generated.push(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Apply {
                    label,
                    arguments: vec![Term::Apply {
                        label: source_label.clone(),
                        arguments: variables.clone(),
                    }],
                }),
                right: Box::new(variables[index].clone()),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
    }
    generated
}

/// Evidence that a field projection's source is the only alternative of its sort's no-junk
/// axiom, so every value of the sort is an application of the source and each projection of it
/// denotes exactly one value.
///
/// Its field is private, which makes `sole_generator` its only constructor: the one judgement
/// that reads the alternatives of the source's sort mints it. It is `Copy` because one judgement
/// on the source covers every projection generated from it.
#[derive(Clone, Copy)]
pub(crate) struct SoleGenerator(());

/// The no-junk alternatives of the main module's sorts, as [`SortGenerators`] derives them for the
/// emitted no-junk axioms, computed once per sort a projection source asks about.
///
/// The subsort order and sort catalog are read only when a source has a named field, and one
/// sort's alternatives are one scan of the main module's productions, so the pass does that scan
/// at most once per sort of a field projection source.
struct MainSortGenerators<'v, 'a> {
    views: &'v DefinitionViews<'a>,
    main: ModuleId,
    sole: BTreeMap<Sort, Option<ProductionId>>,
}

impl<'v, 'a> MainSortGenerators<'v, 'a> {
    fn new(views: &'v DefinitionViews<'a>, main: ModuleId) -> Self {
        Self {
            views,
            main,
            sole: BTreeMap::new(),
        }
    }

    /// The main-module production that is the only alternative of `sort`'s no-junk axiom.
    ///
    /// `None` also when the main module's subsort order is cyclic: that order has no no-junk
    /// axioms at all (emission rejects the cycle), so no projection is judged total on it.
    fn sole_generator(&mut self, sort: &Sort) -> Option<ProductionId> {
        if let Some(sole) = self.sole.get(sort) {
            return *sole;
        }
        let sole = self.views.subsorts(self.main).ok().and_then(|subsorts| {
            SortGenerators::of(
                self.views.production_catalog(self.main),
                self.views.sort_catalog(self.main),
                subsorts,
                sort,
            )
            .sole_generator()
        });
        self.sole.insert(sort.clone(), sole);
        sole
    }
}

/// Judge whether the projection source with content identity `source`, sort parameters
/// `parameters` and result sort `sort` is the only alternative of `sort`'s no-junk axiom, minting
/// the evidence when it is.
///
/// The alternatives are those [`SortGenerators`] derives from the main module's productions,
/// sort catalog and subsort order, the same derivation the emitted no-junk axiom of `sort` uses.
/// A source not visible in the main module is no alternative there, so it is never the sole one.
/// A source with sort parameters generates one sort per instantiation, and each instance may have
/// further productions of its own, so no single axiom makes it sole and it is never judged so.
///
/// The judgement runs at the `generate_sort_projections` stage, before the definition is final,
/// and still gives the alternatives the emitted axiom lists for every sort it can judge sole. An
/// alternative of a sort's no-junk axiom comes from a base, algebraic or token production of the
/// sort, from a declared strict subsort with a chain of subsort axioms into it, or from a `token`
/// attribute on the sort's declaration. After this stage the pipeline adds only function
/// productions (sort predicates, sort and field projections, the counter-cell getter), rules,
/// configurations, the `KItem ::= S` subsort productions, the counter cell inside the generated
/// top cell's production, a `Bool` sort declaration that the seeding stage has already added, and
/// a parsing module above the main module. None of them gives an existing sort a new alternative:
/// function productions and rules are no alternatives, and the `KItem ::= S` productions add
/// injection alternatives only to `KItem` and to the sorts `KItem` injects into. `KItem` already
/// has the injections of the `KItem` subsorts an earlier stage added (the seeded `Bool` among
/// them), and every sort `KItem` injects into already has the injection of `KItem`, so none of
/// them is judged sole here. Nothing after this stage removes the `function`, `macro`
/// or `bracket` attribute that keeps a production out of the alternatives. A cell sort's
/// projection is total for a different reason (its one cell production), which
/// `TotalityWitness::cell_projection` names.
fn sole_generator(
    main_generators: &mut MainSortGenerators<'_, '_>,
    source: ProductionIdentity,
    parameters: &[Sort],
    sort: &Sort,
) -> Option<SoleGenerator> {
    if !parameters.is_empty() {
        return None;
    }
    let source = main_generators
        .views
        .production_catalog(main_generators.main)
        .lookup(&source)?;
    (main_generators.sole_generator(sort) == Some(source)).then_some(SoleGenerator(()))
}

/// Why a module has no sort predicate `isS` for a sort that a sentence names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MissingSortPredicate {
    /// The module has no sort `S`, and declaring it would give it a sort predicate.
    UnknownSort,
    /// `S`'s role has no sort predicate: it has no K terms, declared or not.
    NoKTerms,
}

impl MissingSortPredicate {
    /// What the definition can do about the missing `predicate_label` of `sort`.
    ///
    /// Every remedy is one compilation accepts: declaring a sort whose role has a sort predicate
    /// generates `isS`, and a declared `isS` production of a sort without one conflicts with no
    /// generated predicate (the definition checks read the same role predicate).
    pub(crate) fn remedy(self, sort: &str, predicate_label: &str) -> String {
        match self {
            Self::UnknownSort => format!(
                "Please either declare sort {sort} or declare 'syntax Bool ::= {predicate_label}(K) [symbol({predicate_label}), function]'"
            ),
            Self::NoKTerms => format!(
                "Sort {sort} has no sort predicate because it has no K terms; name a sort of K terms instead or declare 'syntax Bool ::= {predicate_label}(K) [symbol({predicate_label}), function]'"
            ),
        }
    }
}

/// Whether the module of `productions` and `sorts` has the sort predicate `isS` of the sort
/// spelled `sort`, so that a generated sentence may mention it.
///
/// `isS` exists when a production of the module carries its label (declared in the definition or
/// already generated), or when `S` is a sort of the module whose role has a sort predicate: the
/// predicate generator declares `isS` for exactly those sorts. Reading the same role predicate as
/// the generator lets a pass that runs before it, or standalone, decide the same way, so a sentence
/// mentions `isS` only when compilation declares it.
///
/// A caller that generates sentences for the compiled definition passes the main module's
/// catalogs: the compiled definition is the main module's import closure, so that is where `isS`
/// has to be declared, wherever in the closure the sentence that asks for it sits.
pub(crate) fn sort_predicate_in_module(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    sort: &str,
) -> Result<(), MissingSortPredicate> {
    let label = Label::sort_predicate(&Sort::new(sort)).name;
    if !productions
        .productions_for(&LabelHead::new(label))
        .is_empty()
    {
        return Ok(());
    }
    // The role reads the head's spelling, so a sort without a predicate is reported as such
    // whether or not it is declared: declaring it would not give it one.
    let parsed = parse_sort(sort).unwrap_or_else(|_| Sort::new(sort));
    if !parsed.role().has_sort_predicate() {
        Err(MissingSortPredicate::NoKTerms)
    } else if sorts.all_sorts().contains(&parsed) {
        Ok(())
    } else {
        Err(MissingSortPredicate::UnknownSort)
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn sort_json(sort: &Sort) -> Value {
    json!({
        "node": "KSort",
        "name": sort.name,
        "params": sort.parameters.iter().map(sort_json).collect::<Vec<_>>(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::FlatModule;

    fn attributes(keys: &[AttributeKey]) -> Attributes {
        let mut attributes = Attributes::default();
        for key in keys {
            attributes.insert(key.as_str(), Value::String(String::new()));
        }
        attributes
    }

    fn sort_declaration(sort: &str, keys: &[AttributeKey]) -> Sentence {
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new(sort),
            attributes: attributes(keys),
        }
    }

    fn named(sort: &str, name: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: Some(name.into()),
        }
    }

    fn production(
        label: &str,
        sort: &str,
        items: Vec<ProductionItem>,
        keys: &[AttributeKey],
    ) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items,
            attributes: attributes(keys),
        }
    }

    /// `mk(field: Int)` of sort `S`, next to `others`.
    fn source_and(others: Vec<Sentence>) -> Vec<Sentence> {
        let mut sentences = vec![
            sort_declaration("Int", &[]),
            production(
                "mk",
                "S",
                vec![
                    ProductionItem::Terminal("mk".into()),
                    ProductionItem::Terminal("(".into()),
                    named("Int", "field"),
                    ProductionItem::Terminal(")".into()),
                ],
                &[],
            ),
        ];
        sentences.extend(others);
        sentences
    }

    /// The generated field projections of `sentences` in a one-module definition, with whether
    /// each declares `total`.
    fn field_projections(sentences: Vec<Sentence>) -> Vec<(String, bool)> {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        };
        let definition = generate_sort_predicate_syntax(&definition).unwrap();
        let generated = generate_sort_projections(&definition).unwrap();
        generated.modules[0]
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } if label.name.starts_with("project:") && label.name.matches(':').count() == 2 => {
                    Some((label.name.clone(), attributes.has(AttributeKey::Total)))
                }
                _ => None,
            })
            .collect()
    }

    /// A one-module definition of `sentences`.
    fn one_module(sentences: Vec<Sentence>) -> Definition {
        Definition {
            main_module: "MAIN".into(),
            modules: vec![FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: sentences.into_iter().map(Arc::new).collect(),
                attributes: Attributes::default(),
            }],
            attributes: Attributes::default(),
        }
    }

    /// The labels of the productions of `definition`'s module that carry `key`.
    fn labels_with(definition: &Definition, key: AttributeKey) -> Vec<String> {
        definition.modules[0]
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } if attributes.has(key) => Some(label.name.clone()),
                _ => None,
            })
            .collect()
    }

    /// F13: a numeral (the width argument of `MInt{8}`) and a `#`-prefixed parser sort are no
    /// sets of K terms, so no sort predicate is built for them, while a defined sort, a declared
    /// instance and the kernel sorts of K terms get one.
    #[test]
    fn no_sort_predicate_is_built_for_a_numeral_or_a_scaffolding_sort() {
        let definition = one_module(vec![
            sort_declaration("8", &[]),
            sort_declaration("#RuleBody", &[]),
            sort_declaration("#Layout", &[]),
            sort_declaration("Exp", &[]),
            sort_declaration("KItem", &[]),
            sort_declaration("KConfigVar", &[]),
            Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::with_parameters("MInt", vec![Sort::new("8")]),
                attributes: Attributes::default(),
            },
        ]);

        let predicates = labels_with(
            &generate_sort_predicate_syntax(&definition).unwrap(),
            AttributeKey::Predicate,
        );

        for absent in ["is8", "is#RuleBody", "is#Layout"] {
            assert!(
                !predicates.iter().any(|label| label == absent),
                "{absent} in {predicates:?}"
            );
        }
        for present in ["isExp", "isKItem", "isKConfigVar", "isMInt{8}"] {
            assert!(
                predicates.iter().any(|label| label == present),
                "{present} not in {predicates:?}"
            );
        }
    }

    /// The projection generator reads the same role predicate as the rule grammar: `K`, `KItem`
    /// and a defined sort get `project:S`; `KConfigVar`, `KList`, the cell structure sorts `Bag`
    /// and `Cell`, a numeral and a parser sort do not.
    #[test]
    fn sort_projections_are_built_for_the_sorts_whose_role_has_one() {
        let definition = one_module(
            [
                "K",
                "KItem",
                "KConfigVar",
                "KList",
                "Bag",
                "Cell",
                "8",
                "#RuleBody",
                "Exp",
            ]
            .into_iter()
            .map(|sort| sort_declaration(sort, &[]))
            .collect(),
        );
        let definition = generate_sort_predicate_syntax(&definition).unwrap();

        let projections = labels_with(
            &generate_sort_projections(&definition).unwrap(),
            AttributeKey::Projection,
        );

        assert_eq!(
            projections,
            ["project:Bool", "project:Exp", "project:K", "project:KItem"]
        );
    }

    /// The source is the sort's only production, but the sort's `token` attribute adds `\top`
    /// to its no-junk axiom, so a value of the sort need not be an application of `mk` and
    /// `field` is undefined on it.
    #[test]
    fn a_token_sort_with_one_labelled_production_gets_no_total_field_projection() {
        assert_eq!(
            field_projections(source_and(vec![sort_declaration(
                "S",
                &[AttributeKey::Token]
            )])),
            [("project:mk:field".to_owned(), false)]
        );
        // Control: the same sort without `token` has `mk` as its only alternative.
        assert_eq!(
            field_projections(source_and(vec![sort_declaration("S", &[])])),
            [("project:mk:field".to_owned(), true)]
        );
    }

    /// A macro production of the sort is expanded away, so it is no alternative of the sort's
    /// no-junk axiom and leaves `mk` the only one.
    #[test]
    fn a_macro_production_of_the_sort_leaves_the_source_its_sole_generator() {
        let other = |keys: &[AttributeKey]| {
            production(
                "other",
                "S",
                vec![ProductionItem::Terminal("other".into())],
                keys,
            )
        };
        assert_eq!(
            field_projections(source_and(vec![
                sort_declaration("S", &[]),
                other(&[AttributeKey::Macro]),
            ])),
            [("project:mk:field".to_owned(), true)]
        );
        // Control: a base production of the sort is a second alternative.
        assert_eq!(
            field_projections(source_and(vec![sort_declaration("S", &[]), other(&[])])),
            [("project:mk:field".to_owned(), false)]
        );
    }

    /// A strict subsort of the sort contributes its injection to the sort's no-junk axiom.
    #[test]
    fn a_subsort_of_the_sort_is_a_second_alternative() {
        let subsort = Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("S"),
            items: vec![ProductionItem::NonTerminal {
                sort: Sort::new("Int"),
                name: None,
            }],
            attributes: Attributes::default(),
        };
        assert_eq!(
            field_projections(source_and(vec![sort_declaration("S", &[]), subsort])),
            [("project:mk:field".to_owned(), false)]
        );
    }
}
