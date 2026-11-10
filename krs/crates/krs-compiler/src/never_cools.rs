//! The lint on an evaluation position whose hole can never be a result
//! (`warning[krs::analysis::never-cools]`).
//!
//! A context (`#[k::context(hole = h)]`) and each position a strict
//! production names (`#[k::strict]`, `#[k::seqstrict]`) heat their hole while
//! it is not a result and cool it once it is: K adds
//! `requires notBool isR(HOLE)` to the heating and `requires isR(HOLE)` to the
//! cooling, where `R` is the step's result sort (`result = R`, `KResult` when
//! a context names none). A strict position with `using = a` is heated and
//! cooled by one context per context alias of `a`'s name, whose result sort
//! is that alias's `result = R` when it names one and the production's
//! otherwise. Both rules match the hole at its sort `H`, so the
//! cooling applies to a term exactly when the term's sort is below both `H`
//! and `R`. Where no sort that has terms is below both, no term at that
//! position is ever a result: the heating moves whatever the pattern matches
//! to the front of the computation and nothing ever plugs it back, which
//! buries the computation under a freezer for good. That is well defined, so
//! it is a warning, never a refusal.
//!
//! The lint is decided by sorts alone. A sort counts as having terms unless it
//! is one of the framework's sorts (`KItem`, `KResult`) and no production
//! builds terms of it: the framework declares them with no productions, so
//! `KResult` holds nothing but the terms of the sorts declared below it, and a
//! definition that declares none has no results at all. Every other sort may
//! have terms (a builtin's values, a hooked sort's, a token sort's), so a hole
//! whose sort could hold a result is never warned, whatever the rules reach.

use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    BuiltinSort, EvaluationKind, NodeOrigin, ProductionAttribute, ProductionContextAliasReference,
    StableItemId,
};
use krs_ir_levels::definedness::{Sorts, builds_values, is_framework_sort};
use krs_ir_levels::{SemanticContextAlias, SemanticModule, SemanticProduction, SemanticSortRef};

use crate::coverage::display_name;

/// The `warning[krs::analysis::never-cools]` diagnostics of a lowered
/// theory's modules: each context, and each position of a strict production,
/// whose hole's sort shares no sort that has terms with the step's result
/// sort (the module documentation), in module and declaration order.
#[must_use]
pub fn never_cooling_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let judge = Judge::of(modules);
    let mut warnings = Vec::new();
    for module in modules {
        for production in module.productions() {
            for attribute in production.attributes() {
                let ProductionAttribute::Strictness {
                    using,
                    fields,
                    result_sort,
                    ..
                } = attribute
                else {
                    continue;
                };
                let steps = judge.strict_steps(using.as_ref(), result_sort.sort());
                for field in fields {
                    let Some(hole) = field_sort(production, field.field()) else {
                        continue;
                    };
                    for (alias, result) in &steps {
                        if judge.may_cool(hole, result) {
                            continue;
                        }
                        let through = alias
                            .map(|name| format!(" through the context alias `{name}`"))
                            .unwrap_or_default();
                        warnings.push(warning(
                            &format!(
                                "the strict position `{}` of `{}`{through}",
                                field.field().as_str(),
                                display_name(production.id()),
                            ),
                            "its heating moves the argument",
                            hole,
                            result,
                            &judge,
                            field.origin(),
                        ));
                    }
                }
            }
        }
        for rule in module.rules() {
            let Some(step) = rule.evaluation() else {
                continue;
            };
            if step.kind() != EvaluationKind::Context {
                continue;
            }
            let Some(hole) = rule
                .variables()
                .iter()
                .find(|variable| variable.id() == step.hole())
                .map(krs_ir_levels::SemanticVariable::sort)
            else {
                continue;
            };
            let Some(result) = step
                .result()
                .map(krs_ir_levels::IrEvaluationResult::sort)
                .or(judge.k_result.as_ref())
            else {
                continue;
            };
            if judge.may_cool(hole, result) {
                continue;
            }
            warnings.push(warning(
                &format!(
                    "the hole `{}` of the context `{}`",
                    step.hole().as_str(),
                    rule.id().item_name(),
                ),
                "the context moves the hole",
                hole,
                result,
                &judge,
                step.hole_origin(),
            ));
        }
    }
    warnings
}

/// The sorts a hole and a result sort are judged by.
struct Judge<'m> {
    sorts: Sorts,
    /// The framework's `KResult`, a context's result sort when it names none.
    k_result: Option<SemanticSortRef>,
    /// Every sort the theory names in a declaration, a subsort edge or a
    /// production's result.
    universe: BTreeSet<SemanticSortRef>,
    /// The framework sorts some production builds terms of.
    inhabited_framework: BTreeSet<SemanticSortRef>,
    /// Every context alias of the theory, by name.
    aliases: BTreeMap<&'m str, Vec<&'m SemanticContextAlias>>,
    /// The name of each context alias, by declaration.
    alias_names: BTreeMap<&'m StableItemId, &'m str>,
}

impl<'m> Judge<'m> {
    /// The judge of `modules`.
    ///
    /// A theory that names no framework sort has no framework module, and
    /// then no context without `result = S` either (its conditions name
    /// `KResult`); a strict production's result sort is still judged, with
    /// the sorts' stand-in for `KItem`, which no hole has
    /// ([`Sorts::of_modules`]).
    fn of(modules: &'m [SemanticModule]) -> Self {
        let sorts = Sorts::of_modules(modules);
        let k_result = modules
            .iter()
            .flat_map(SemanticModule::sorts)
            .map(krs_ir_levels::SemanticSort::id)
            .find(|id| is_framework_sort(id) && id.item_name() == "KResult")
            .cloned()
            .map(SemanticSortRef::Declared);
        let mut universe = BTreeSet::new();
        let mut inhabited_framework = BTreeSet::new();
        let mut aliases = BTreeMap::<_, Vec<_>>::new();
        let mut alias_names = BTreeMap::new();
        for module in modules {
            universe.extend(
                module
                    .sorts()
                    .iter()
                    .map(|sort| SemanticSortRef::Declared(sort.id().clone())),
            );
            for edge in module.subsorts() {
                universe.insert(edge.subsort().clone());
                universe.insert(edge.supersort().clone());
            }
            for production in module.productions() {
                universe.insert(production.result_sort().clone());
                if builds_values(production) && is_framework(production.result_sort()) {
                    inhabited_framework.insert(production.result_sort().clone());
                }
            }
            for alias in module.context_aliases() {
                aliases.entry(alias.name()).or_default().push(alias);
                alias_names.insert(alias.id(), alias.name());
            }
        }
        Self {
            sorts,
            k_result,
            universe,
            inhabited_framework,
            aliases,
            alias_names,
        }
    }

    /// The steps a strict position is heated and cooled by, each with the
    /// name of the context alias it instantiates and its result sort.
    ///
    /// Without `using`, the one step is the production's own, whose result
    /// sort is the production's. With `using = a`, the position gets one
    /// context per context alias named as `a` is, the production placed at
    /// the alias's `here`; each context's result sort is the alias's
    /// `result = S` when it names one and the production's otherwise. Steps
    /// with the same result sort are judged once.
    fn strict_steps<'s>(
        &'s self,
        using: Option<&ProductionContextAliasReference>,
        production_result: &'s SemanticSortRef,
    ) -> Vec<(Option<&'m str>, &'s SemanticSortRef)> {
        let Some(name) = using.and_then(|using| self.alias_names.get(using.alias()).copied())
        else {
            return vec![(None, production_result)];
        };
        let mut seen = BTreeSet::new();
        self.aliases
            .get(name)
            .into_iter()
            .flatten()
            .map(|alias| {
                alias
                    .result()
                    .map_or(production_result, krs_ir_levels::IrEvaluationResult::sort)
            })
            .filter(|result| seen.insert(*result))
            .map(|result| (Some(name), result))
            .collect()
    }

    /// Whether some term of sort `hole` may be a result of sort `result`:
    /// some sort with terms is below both. A sort parameter is never judged.
    fn may_cool(&self, hole: &SemanticSortRef, result: &SemanticSortRef) -> bool {
        if matches!(hole, SemanticSortRef::Parameter(_))
            || matches!(result, SemanticSortRef::Parameter(_))
        {
            return true;
        }
        self.universe
            .iter()
            .chain([hole, result])
            .any(|sort| self.has_terms(sort) && self.below(sort, result) && self.below(sort, hole))
    }

    /// Whether a term of `sort` may stand where `expected` is required; a
    /// computation (`K`) holds a term of every sort as its one item.
    fn below(&self, sort: &SemanticSortRef, expected: &SemanticSortRef) -> bool {
        matches!(expected, SemanticSortRef::Builtin(BuiltinSort::KSequence))
            || self.sorts.is_subsort(sort, expected)
    }

    /// Whether `sort` may have terms of its own (the module documentation).
    fn has_terms(&self, sort: &SemanticSortRef) -> bool {
        !is_framework(sort) || self.inhabited_framework.contains(sort)
    }

    /// What makes a term a result of sort `result`, said for the warning.
    fn result_reason(&self, hole: &SemanticSortRef, result: &SemanticSortRef) -> String {
        let hole = sort_name(hole);
        let name = sort_name(result);
        let declared_below = self
            .universe
            .iter()
            .any(|sort| sort != result && self.has_terms(sort) && self.below(sort, result));
        if self.k_result.as_ref() == Some(result) && !declared_below {
            "a term is a result when its sort is below `KResult`, and the definition declares no sort below `KResult`, so nothing is a result".to_owned()
        } else {
            format!(
                "a term is a result there when its sort is below `{name}`, and no sort with terms is below both `{hole}` and `{name}`"
            )
        }
    }
}

/// The warning at `origin` for the step `subject`, whose hole has sort `hole`
/// and whose cooling asks for sort `result`.
fn warning(
    subject: &str,
    moves: &str,
    hole: &SemanticSortRef,
    result: &SemanticSortRef,
    judge: &Judge,
    origin: &NodeOrigin,
) -> Diagnostic {
    let mut warning = Diagnostic::error(
        codes::analysis::NEVER_COOLS,
        format!(
            "{subject} has sort `{}`, which can never be a result: {}; {moves} to the front of the computation and no cooling ever plugs it back, so a run that reaches it stays stuck under the freezer; declare the sorts of evaluated values below `{}` (or name the `result = S` whose values end the evaluation)",
            sort_name(hole),
            judge.result_reason(hole, result),
            sort_name(result),
        ),
        origin
            .origin()
            .exact_authored_range()
            .map_or(Location::None, Location::Source),
    );
    warning.severity = Severity::Warning;
    warning
}

/// The sort of the argument `field` of `production`.
fn field_sort<'p>(
    production: &'p SemanticProduction,
    field: &krs_ir::ProductionFieldId,
) -> Option<&'p SemanticSortRef> {
    production
        .items()
        .iter()
        .find_map(|item| match item.kind() {
            krs_ir::GrammarProductionItemKind::NonTerminal { field: name, sort }
                if name == field =>
            {
                Some(sort)
            }
            _ => None,
        })
}

/// Whether `sort` is one of the framework's sorts (`KItem`, `KResult`).
fn is_framework(sort: &SemanticSortRef) -> bool {
    matches!(sort, SemanticSortRef::Declared(id) if is_framework_sort(id))
}

fn sort_name(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Declared(id) => id.item_name().to_owned(),
        SemanticSortRef::Builtin(sort) => sort.k_name().to_owned(),
        SemanticSortRef::Cell(id) => format!("{}Cell", id.item_name()),
        SemanticSortRef::LeafCell(_) => crate::LEAF_CELL_SORT.to_owned(),
        SemanticSortRef::CellCollection(_) => crate::CELL_COLLECTION_SORT.to_owned(),
        SemanticSortRef::Parameter(name) => name.as_str().to_owned(),
    }
}
