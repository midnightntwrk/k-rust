//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Remove semantic-cast applications while retaining their inferred sorts.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{Definition, PartialOrder, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::{Label, Sort, Term},
    provenance::GeneratingPass,
};

#[derive(Default)]
struct VariableBounds {
    explicit: Option<(Sort, Term)>,
    casts: Vec<(Sort, Term)>,
}

// The order of `subsort_kitem::implicit_less_than_eq`, shared with sort injection: this pass runs
// before `subsort_kitem` adds the implicit `KItem` edges.
fn below(actual: &Sort, expected: &Sort, subsorts: &PartialOrder<Sort>) -> bool {
    super::subsort_kitem::implicit_less_than_eq(actual, expected, subsorts)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveSemanticCastsError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveSemanticCastsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(diagnostic) = self.diagnostics.first() {
            write!(formatter, "{}", diagnostic.message)
        } else {
            write!(formatter, "semantic-cast resolution failed")
        }
    }
}

impl std::error::Error for ResolveSemanticCastsError {}

fn error(message: impl Into<String>, sentence: &Sentence) -> ResolveSemanticCastsError {
    ResolveSemanticCastsError {
        diagnostics: vec![Diagnostic::error(
            DiagnosticCode::InvalidSemanticCast,
            message,
            sentence,
        )],
    }
}

fn sentence_error(message: impl Into<String>, sentence: &Sentence) -> ResolveSemanticCastsError {
    let label = sentence
        .attributes()
        .string(AttributeKey::Label)
        .unwrap_or("<unlabelled>");
    error(format!("sentence {label}: {}", message.into()), sentence)
}

fn unlocated_error(message: impl Into<String>) -> ResolveSemanticCastsError {
    ResolveSemanticCastsError {
        diagnostics: vec![Diagnostic {
            severity: crate::diagnostic::Severity::Error,
            code: DiagnosticCode::InvalidSemanticCast,
            message: message.into(),
            source: None,
            location: None,
        }],
    }
}

/// Apply the KORE backend form of Java's `ResolveSemanticCasts` pass.
///
/// The backend requests `skipSortPredicates = true`, so casts become compiler sort metadata but do
/// not add redundant `isSort` side conditions. Casted variables retain their inferred sort in the
/// public variable node as well.
pub fn resolve_semantic_casts(
    definition: &Definition,
) -> Result<Definition, ResolveSemanticCastsError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_semantic_casts_pass,
        Some(GeneratingPass::SemanticCasts),
    )
}

pub(crate) fn resolve_semantic_casts_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveSemanticCastsError> {
    let resolved = input
        .resolved_raw()
        .map_err(|error| unlocated_error(error.to_string()))?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let subsorts = views.subsorts(module_id).map_err(|cycle| {
            let message = format!("module {} has cyclic subsorts: {cycle}", module.name);
            module.local_sentences.first().map_or_else(
                || unlocated_error(&message),
                |sentence| sentence_error(&message, sentence),
            )
        })?;
        for sentence in &mut module.local_sentences {
            resolve_semantic_casts_in_sentence_mut(
                crate::definition::sentence_mut(sentence),
                false,
                subsorts,
            )?;
        }
    }
    Ok(output)
}

/// Resolve semantic casts across all term-bearing roots of one sentence.
///
/// `subsorts` must be the visible subsort order of the sentence's module. Callers resolving
/// several sentences from one module should obtain it once from the same `DefinitionViews`.
pub fn resolve_semantic_casts_in_sentence(
    subsorts: &PartialOrder<Sort>,
    mut sentence: Sentence,
) -> Result<Sentence, ResolveSemanticCastsError> {
    resolve_semantic_casts_in_sentence_mut(&mut sentence, false, subsorts)?;
    Ok(sentence)
}

/// Resolve semantic casts and add their sort predicates to the sentence condition.
///
/// This is Java's `ResolveSemanticCasts(false)` mode used for standalone patterns. Macro and
/// alias sentences suppress predicates because their casts describe matching syntax rather than
/// runtime side conditions. `subsorts` is the visible order of the sentence's module.
pub fn resolve_semantic_casts_with_predicates_in_sentence(
    subsorts: &PartialOrder<Sort>,
    mut sentence: Sentence,
) -> Result<Sentence, ResolveSemanticCastsError> {
    resolve_semantic_casts_in_sentence_mut(&mut sentence, true, subsorts)?;
    Ok(sentence)
}

fn resolve_semantic_casts_in_sentence_mut(
    sentence: &mut Sentence,
    add_predicates: bool,
    subsorts: &PartialOrder<Sort>,
) -> Result<(), ResolveSemanticCastsError> {
    let roots = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        _ => return Ok(()),
    };

    let (casts, typed_variables, errors) = {
        let shared = roots.iter().map(|root| &**root).collect::<Vec<&Term>>();
        collect_cast_bounds(&shared, subsorts)
    };
    if !errors.is_empty() {
        drop(roots);
        return Err(ResolveSemanticCastsError {
            diagnostics: errors
                .into_iter()
                .flat_map(|message| sentence_error(message, sentence).diagnostics)
                .collect(),
        });
    }
    for root in roots {
        let taken = std::mem::replace(root, Term::Sequence(Vec::new()));
        *root = transform(taken, &casts, &typed_variables);
    }

    if !add_predicates
        || casts.is_empty()
        || sentence.attributes().has_any(&AttributeKey::MACRO_LIKE)
    {
        return Ok(());
    }

    let predicate = casts
        .iter()
        .map(|cast| {
            let Term::Apply { label, .. } = cast else {
                unreachable!("only semantic-cast applications were collected")
            };
            let sort = label
                .semantic_cast_sort()
                .expect("the cast set contains semantic-cast applications");
            Term::Apply {
                label: Label::sort_predicate(&sort),
                arguments: vec![transform(cast.clone(), &casts, &typed_variables)],
            }
        })
        .reduce(|left, right| Term::apply("_andBool_", vec![left, right]))
        .expect("at least one semantic cast was collected");

    let requires = match sentence {
        Sentence::Rule { requires, .. }
        | Sentence::Claim { requires, .. }
        | Sentence::Context { requires, .. }
        | Sentence::ContextAlias { requires, .. } => requires,
        _ => return Ok(()),
    };
    let prior = std::mem::replace(requires, bool_true());
    *requires = if is_true(&prior) {
        predicate
    } else {
        Term::apply("_andBool_", vec![predicate, prior])
    };
    Ok(())
}

/// The sort semantic-cast resolution gives each named variable of a sentence with the term roots
/// `roots`: its explicit sort, or else the least of its direct cast bounds.
///
/// Returns the semantic casts seen, the variable sorts, and one message per conflict (an explicit
/// sort outside a cast bound, conflicting explicit sorts, or cast bounds without a least one).
fn collect_cast_bounds(
    roots: &[&Term],
    subsorts: &PartialOrder<Sort>,
) -> (BTreeSet<Term>, BTreeMap<String, Sort>, Vec<String>) {
    let mut casts = BTreeSet::new();
    let mut variables = BTreeMap::<String, VariableBounds>::new();
    let mut errors = Vec::new();
    // Invariant: `casts` holds semantic casts seen so far, and `variables` holds every explicit sort and direct cast bound of each named variable in the visited roots.
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable {
                name,
                sort: Some(sort),
            } = term.unannotated()
                && !is_anonymous(name)
            {
                let variable = variables.entry(name.clone()).or_default();
                if let Some((previous, occurrence)) = &variable.explicit {
                    if previous != sort {
                        errors.push(format!(
                            "variable {name} has conflicting explicit sorts {previous} and {sort} at {occurrence} and {term}"
                        ));
                    }
                } else {
                    variable.explicit = Some((sort.clone(), term.clone()));
                }
            }
            let Term::Apply { label, arguments } = term.unannotated() else {
                return;
            };
            let Some(sort) = label.semantic_cast_sort() else {
                return;
            };
            let [argument] = arguments.as_slice() else {
                return;
            };
            casts.insert(term.unannotated().clone());
            if let Term::Variable {
                name,
                sort: existing,
            } = argument.unannotated()
            {
                if is_anonymous(name) {
                    if let Some(existing) = existing
                        && !below(existing, &sort, subsorts)
                    {
                        errors.push(format!(
                            "variable {name} has sort {existing} outside semantic cast sort {sort} at {term}"
                        ));
                    }
                } else {
                    variables
                        .entry(name.clone())
                        .or_default()
                        .casts
                        .push((sort, term.clone()));
                }
            }
        });
    }
    let mut typed_variables = BTreeMap::<String, Sort>::new();
    for (name, bounds) in variables {
        if let Some((explicit, occurrence)) = bounds.explicit {
            for (cast, cast_occurrence) in &bounds.casts {
                if !below(&explicit, cast, subsorts) {
                    errors.push(format!(
                        "variable {name} has explicit sort {explicit} outside semantic cast sort {cast} at {occurrence} and {cast_occurrence}"
                    ));
                }
            }
            typed_variables.insert(name, explicit);
            continue;
        }
        if bounds.casts.is_empty() {
            continue;
        }
        if let Some((least, _)) = bounds.casts.iter().find(|(candidate, _)| {
            bounds
                .casts
                .iter()
                .all(|(bound, _)| below(candidate, bound, subsorts))
        }) {
            typed_variables.insert(name, least.clone());
        } else {
            if let Some(((left, left_occurrence), (right, right_occurrence))) =
                bounds.casts.iter().enumerate().find_map(|(index, left)| {
                    bounds.casts[index + 1..].iter().find_map(|right| {
                        (!below(&left.0, &right.0, subsorts) && !below(&right.0, &left.0, subsorts))
                            .then_some((left, right))
                    })
                })
            {
                errors.push(format!(
                    "variable {name} has incomparable cast bounds {left} and {right} at {left_occurrence} and {right_occurrence}"
                ));
            } else {
                let bounds = bounds
                    .casts
                    .iter()
                    .map(|(sort, _)| sort.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                errors.push(format!(
                    "variable {name} has no least cast bound among {bounds}"
                ));
            }
        }
    }
    (casts, typed_variables, errors)
}

/// The sorts semantic-cast resolution gives the named variables of a rule-like sentence, or the
/// resolution's error when its variables' annotations and casts disagree.
///
/// `subsorts` is the visible subsort order of the sentence's module. A variable with neither an
/// explicit sort nor a direct cast has no entry; anonymous variables have none either, since each
/// occurrence is a distinct variable.
pub(crate) fn semantic_cast_variable_sorts(
    sentence: &Sentence,
    subsorts: &PartialOrder<Sort>,
) -> Result<BTreeMap<String, Sort>, ResolveSemanticCastsError> {
    let roots: Vec<&Term> = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. } => vec![body, requires],
        _ => return Ok(BTreeMap::new()),
    };
    let (_, typed_variables, errors) = collect_cast_bounds(&roots, subsorts);
    if errors.is_empty() {
        Ok(typed_variables)
    } else {
        Err(ResolveSemanticCastsError {
            diagnostics: errors
                .into_iter()
                .flat_map(|message| sentence_error(message, sentence).diagnostics)
                .collect(),
        })
    }
}

/// Whether `name` is an anonymous variable, each of whose occurrences is a distinct variable.
pub(crate) fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn bool_true() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort.is_builtin(BuiltinSort::Bool)
    )
}

// Invariant: each call replaces an application in `casts` by its transformed argument carrying the cast sort, gives a variable its sort from `typed_variables`, and otherwise recurses into the immediate subterms of `term`; the finite `term` bounds the recursion.
fn transform(term: Term, casts: &BTreeSet<Term>, typed_variables: &BTreeMap<String, Sort>) -> Term {
    let source_metadata = term.metadata().cloned();
    if casts.contains(term.unannotated()) {
        let Term::Apply { label, arguments } = term.into_unannotated() else {
            unreachable!("the cast set contains applications only")
        };
        let sort = label
            .semantic_cast_sort()
            .expect("the cast set contains semantic casts");
        let [argument] = arguments
            .try_into()
            .unwrap_or_else(|_| unreachable!("only unary semantic casts enter the cast set"));
        return attach_sort(transform(argument, casts, typed_variables), sort);
    }

    let rebuilt = match term.into_unannotated() {
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(transform(*left, casts, typed_variables)),
            right: Box::new(transform(*right, casts, typed_variables)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(transform(*pattern, casts, typed_variables)),
            alias: Box::new(transform(*alias, casts, typed_variables)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .into_iter()
                .map(|item| transform(item, casts, typed_variables))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments
                .into_iter()
                .map(|argument| transform(argument, casts, typed_variables))
                .collect(),
        },
        Term::Variable { name, sort } => Term::Variable {
            sort: typed_variables.get(&name).cloned().or(sort),
            name,
        },
        leaf @ (Term::InjectedLabel(_) | Term::Token { .. }) => leaf,
        Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
    };
    source_metadata.map_or(rebuilt.clone(), |metadata| rebuilt.with_metadata(metadata))
}

fn attach_sort(term: Term, sort: Sort) -> Term {
    let metadata = term.metadata().cloned();
    match term.into_unannotated() {
        Term::Variable {
            name,
            sort: existing,
        } => {
            let variable = Term::Variable {
                name,
                sort: existing.or(Some(sort)),
            };
            metadata.map_or(variable.clone(), |metadata| {
                variable.with_metadata(metadata)
            })
        }
        term => {
            let mut metadata = metadata.unwrap_or_default();
            metadata.sort = Some(sort);
            term.with_metadata(metadata)
        }
    }
}
