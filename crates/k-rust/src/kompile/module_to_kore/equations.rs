//! ```toml algorithm
//! id = "kompile.kore.rules"
//! name = "KORE rule, claim, and equation emission"
//! sites = ["emit_rule_or_claim", "resolve_equation_production"]
//! variable = "R = rules; I = sort-injection work; C = term-conversion work"
//! counters = []
//! no_counter = "ordinary KORE rule emission has no dedicated counter; the sort injection it calls bumps KompileInjectionsInserted and the owise path bumps KompileOwiseCompetitorScans, each owned by its own card"
//! consumes = [{ type = "k_rust_kore::kore::ast::Pattern", role = "converted term" }]
//! produces = [{ type = "k_rust_kore::kore::ast::Sentence", role = "rule sentence" }]
//!
//! [[cost]]
//! mode = "one module"
//! bound = "O(R x (I + C))"
//! ```
//!
//! ```toml algorithm
//! id = "kompile.kore.owise"
//! name = "construction of owise competitor predicates"
//! sites = ["emit_owise_equation", "OwiseCompetitors"]
//! variable = "R = module rules; O = owise equations; I = sort-injection and equation-shape work per rule; m = competitors sharing an owise equation's label and argument sorts; c = per-competitor refresh, matching and conversion work"
//! counters = ["KompileOwiseCompetitorScans"]
//!
//! [[cost]]
//! mode = "one module"
//! bound = "O(R x (I + log R) + O x (m x c + log R))"
//! ```
//!
//! ```toml algorithm-site
//! id = "kompile.fresh_names.mint"
//! role = "part"
//! sites = ["refresh_variables"]
//! ```
//!
//! Rule, claim, macro, equation, and owise emission.
//! Complexity: O(R(inject + convert)), plus one O(R) competitor scan per module with an owise equation and O(m) same-signature competitors per owise equation; `KompileOwiseCompetitorScans` counts the scanned rules and the visited competitors.

use super::binders::generated_exists_all;
use super::roles::{EmittedEquation, SymbolRoles};
use super::*;
use crate::kast::binding;
use crate::kompile::sort_injections::SentenceSortVariables;
use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::DEFAULT_RULE_PRIORITY;

pub(super) struct RuleEmissionContext<'a, 'definition> {
    pub valued: &'a BTreeSet<String>,
    pub productions: &'a ProductionCatalog<'definition>,
    pub injector: &'a SortInjector<'definition, 'definition>,
    pub converter: &'a TermConverter<'definition, 'definition>,
    pub module_rules: &'a [Sentence],
    pub default_reachability: Option<ReachabilityMode>,
    /// The claims of every production of `productions`; the equation-head check reads them.
    pub roles: &'a SymbolRoles,
    /// How the target writes conditions.
    pub condition_form: ConditionForm,
}

pub(super) fn emit_rule_or_claim(
    sentence: &Sentence,
    claim: bool,
    context: &RuleEmissionContext<'_, '_>,
    owise_competitors: &mut OwiseCompetitors,
) -> Result<KoreSentence, ModuleToKoreError> {
    let RuleEmissionContext {
        valued,
        productions,
        injector,
        converter,
        module_rules,
        default_reachability,
        roles,
        condition_form,
    } = context;
    let (injected, sort_variables) = injector.inject_sentence_bound(sentence)?;
    let converter = converter.with_sort_variables(&sort_variables);
    let converter = &converter;
    let (body, requires, ensures, attributes) = match &injected {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => (body, requires, ensures, attributes),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("only rules and claims are emitted"),
    };
    let body_sort = injector.term_sort(body, None)?;
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    let (left, right) = match body.unannotated() {
        Term::Rewrite { left, right } => (left.as_ref(), right.as_ref()),
        _ if claim => (body, body),
        _ => {
            return Err(ModuleToKoreError::ExpectedRewrite { sentence: "rule" });
        }
    };
    let existentials = existential_variables(right, ensures, converter)?;
    let equation = equation_info(left, attributes, productions)?;
    if equation.is_some() && !existentials.is_empty() {
        return Err(ModuleToKoreError::EquationExistentials {
            variables: existential_names(right, ensures),
        });
    }
    if let Some(equation) = equation {
        if cfg!(debug_assertions)
            && !claim
            && !attributes.has(AttributeKey::Simplification)
            && let Some(production) = equation.production
        {
            roles.debug_assert_heads_equation(
                production,
                equation.label,
                if attributes.has(AttributeKey::Anywhere) {
                    EmittedEquation::Anywhere
                } else {
                    EmittedEquation::Function
                },
                right,
            );
        }
        return emit_equation(
            equation,
            left,
            right,
            requires,
            ensures,
            attributes,
            claim,
            valued,
            converter,
            productions,
            injector,
            module_rules,
            owise_competitors,
            &sort_variables,
            *condition_form,
        );
    }
    if is_macro_rule(&injected) {
        // Resolving the head is work the macro axiom does not need, so it runs only when the
        // check does, and a head that does not resolve to one production skips the check.
        if cfg!(debug_assertions) {
            let application = peel_alias(left);
            if let Term::Apply { label, .. } = application.unannotated()
                && !label.is(WellKnownSymbol::Inj)
                && let Ok(production) =
                    resolve_equation_production_id(application, label, productions)
            {
                roles.debug_assert_heads_equation(production, label, EmittedEquation::Macro, right);
            }
        }
        return emit_macro_axiom(
            left,
            right,
            existentials,
            attributes,
            valued,
            injector,
            converter,
            &sort_variables,
        );
    }
    if !claim && !body_sort.is_builtin(BuiltinSort::GeneratedTopCell) {
        return Err(ModuleToKoreError::ExpectedGeneratedTopCell {
            actual: body_sort,
            rule: body.to_string(),
        });
    }
    let result_sort = converter.convert_sort(&body_sort)?;
    let left = converter.convert(left)?;
    let right = converter.convert(right)?;
    let sentence = || located_sentence(claim, attributes);
    let requires = side_condition(
        requires,
        &result_sort,
        converter,
        *condition_form,
        &sentence,
    )?;
    let ensures = side_condition(ensures, &result_sort, converter, *condition_form, &sentence)?;
    // `concrete` and `symbolic` carry lists of free variables, not string
    // values.  For rewrite rules and claims K resolves those names against
    // the left-hand side and its requires condition only (variables that are
    // introduced by the right-hand side/ensures are not in scope).
    let attribute_pattern = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![left.clone(), requires.clone()],
    };
    let attribute_overrides = variable_list_attribute_overrides(attributes, &attribute_pattern)?;
    let mut right = generated_exists_all(
        &result_sort,
        existentials,
        Pattern::And {
            sort: result_sort.clone(),
            arguments: vec![right, ensures],
        },
    );
    let requires = if claim {
        requires
    } else {
        quantify_condition_only(requires, &result_sort, attributes, || {
            Ok(free_names([&left, &right]))
        })?
    };
    if let Some(mode) = reachability_mode(attributes).or(*default_reachability) {
        right = Pattern::Application {
            symbol: Symbol {
                name: match mode {
                    ReachabilityMode::OnePath => InternalLabel::WeakExistsFinally.as_str(),
                    ReachabilityMode::AllPath => InternalLabel::WeakAlwaysFinally.as_str(),
                }
                .into(),
                sort_parameters: vec![result_sort.clone()],
            },
            arguments: vec![right],
        };
    }
    let pattern = if claim {
        Pattern::Implies {
            sort: result_sort.clone(),
            left: Box::new(Pattern::And {
                sort: result_sort,
                arguments: vec![requires, left],
            }),
            right: Box::new(right),
        }
    } else {
        Pattern::Rewrites {
            sort: result_sort.clone(),
            left: Box::new(Pattern::And {
                sort: result_sort,
                arguments: vec![left, requires],
            }),
            right: Box::new(right),
        }
    };
    let attributes = emit_attributes(attributes.semantic_entries(), valued, &attribute_overrides);
    Ok(if claim {
        KoreSentence::Claim {
            parameters: sort_variables.names().map(str::to_owned).collect(),
            pattern: Box::new(pattern),
            attributes,
        }
    } else {
        KoreSentence::Axiom {
            parameters: sort_variables.names().map(str::to_owned).collect(),
            pattern: Box::new(pattern),
            attributes,
        }
    })
}

/// The axiom `m(params) = right` of a macro rule. A macro is textual substitution, so a `?`
/// variable of its right side that no parameter receives is an existential variable of the
/// macro's text, a fresh one at each use (`expand macros`); the axiom states that by quantifying
/// it existentially around the right side (`existentials`, the free `?` variables of the right
/// side and `ensures`, of which those free in the right side are bound).
#[allow(clippy::too_many_arguments)]
fn emit_macro_axiom(
    left: &Term,
    right: &Term,
    existentials: Vec<Variable>,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    injector: &SortInjector<'_, '_>,
    converter: &TermConverter<'_, '_>,
    sort_variables: &SentenceSortVariables,
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = std::iter::once("R")
        .chain(sort_variables.names())
        .map(str::to_owned)
        .collect();
    let result_sort = converter.convert_sort(&injector.term_sort(left, None)?)?;
    let right = converter.convert(right)?;
    let free = right.free_variables();
    let existentials = existentials
        .into_iter()
        .filter(|variable| free.contains(variable))
        .collect();
    let pattern = Pattern::Equals {
        operand_sort: Box::new(result_sort.clone()),
        result_sort: KoreSort::Variable("R".into()),
        left: Box::new(converter.convert(left)?),
        right: Box::new(generated_exists_all(&result_sort, existentials, right)),
    };
    // The axiom states the rule's rank in macro expansion. An `owise` rule's rank is its `owise`
    // attribute, which places it after every rank a priority names, so no priority is added
    // beside it; every other rule states its priority, the default when it names none.
    let mut attributes = attributes.clone();
    if !attributes.has(AttributeKey::Owise) {
        let priority = attributes
            .value(AttributeKey::Priority)
            .map(|value| attribute_value_string(AttributeKey::Priority.as_str(), value))
            .filter(|value| !value.is_empty())
            .unwrap_or_else(|| DEFAULT_RULE_PRIORITY.to_string());
        attributes.set(AttributeKey::Priority, Value::String(priority));
    }
    equation_sentence(false, pattern, &attributes, valued, parameters)
}

#[derive(Clone, Debug)]
struct EquationInfo<'a> {
    label: &'a Label,
    children: &'a [Term],
    argument_sorts: Vec<Sort>,
    result_sort: Sort,
    direct: bool,
    /// The production the head resolves to; `None` for a sort injection, which no production
    /// of the module declares.
    production: Option<ProductionId>,
}

fn equation_info<'a>(
    left: &'a Term,
    attributes: &KAttributes,
    productions: &ProductionCatalog<'_>,
) -> Result<Option<EquationInfo<'a>>, ModuleToKoreError> {
    let application = peel_alias(left);
    let Term::Apply { label, arguments } = application.unannotated() else {
        return Ok(None);
    };
    let simplification = attributes.has(AttributeKey::Simplification);
    let anywhere = attributes.has(AttributeKey::Anywhere);
    // `inj` is declared by the KORE prelude as a polymorphic symbol, not by a production of the
    // compiled K module, so its equations are handled here rather than through the catalog.
    if label.is(WellKnownSymbol::Inj) {
        if !simplification && !anywhere {
            return Ok(None);
        }
        let [from, to] = label.parameters.as_slice() else {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: "synthetic".into(),
                message: "sort injection labels must carry source and destination sorts".into(),
            });
        };
        if arguments.len() != 1 {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: "synthetic".into(),
                message: format!(
                    "sort injections take one argument but the equation has {}",
                    arguments.len()
                ),
            });
        }
        return Ok(Some(EquationInfo {
            label,
            children: arguments,
            argument_sorts: vec![from.clone()],
            result_sort: to.clone(),
            direct: simplification,
            production: None,
        }));
    }
    let production_id = resolve_equation_production_id(application, label, productions)?;
    let production = productions.production(production_id);
    let Sentence::Production {
        parameters,
        sort,
        items,
        attributes: production_attributes,
        ..
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    if !production_attributes.has(AttributeKey::Function) && !simplification && !anywhere {
        return Ok(None);
    }
    let substitution = parameters
        .iter()
        .cloned()
        .zip(label.parameters.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    let argument_sorts = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => {
                Some(substitute_equation_sort(sort, &substitution))
            }
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    if argument_sorts.len() != arguments.len() {
        return Err(ModuleToKoreError::InvalidEquationProduction {
            production: application
                .metadata()
                .and_then(|metadata| metadata.production)
                .map_or_else(|| "unknown".into(), |id| id.to_hex()),
            message: format!(
                "expected {} arguments but the equation has {}",
                argument_sorts.len(),
                arguments.len()
            ),
        });
    }
    Ok(Some(EquationInfo {
        label,
        children: arguments,
        argument_sorts,
        result_sort: substitute_equation_sort(sort, &substitution),
        direct: simplification,
        production: Some(production_id),
    }))
}

pub(super) fn resolve_equation_production<'a>(
    application: &Term,
    label: &Label,
    productions: &'a ProductionCatalog<'a>,
) -> Result<&'a Sentence, ModuleToKoreError> {
    resolve_equation_production_id(application, label, productions)
        .map(|id| productions.production(id))
}

/// The production of `productions` that the equation head `application`, labelled `label`,
/// resolves to: the production identity the term carries, which must be labelled `label`, or
/// else the only production of the label head.
pub(super) fn resolve_equation_production_id(
    application: &Term,
    label: &Label,
    productions: &ProductionCatalog<'_>,
) -> Result<ProductionId, ModuleToKoreError> {
    if let Some(identity) = application
        .metadata()
        .and_then(|metadata| metadata.production)
    {
        let Some(production_id) = productions.lookup(&identity) else {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: identity.to_hex(),
                message: "the resolved production is absent from this module's catalog".into(),
            });
        };
        let production = productions.production(production_id);
        if !matches!(
            production,
            Sentence::Production { label: Some(candidate), .. } if candidate.name == label.name
        ) {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: identity.to_hex(),
                message: format!("its label does not match {:?}", label.name),
            });
        }
        return Ok(production_id);
    }
    let candidates = productions.productions_for(&LabelHead::from(label));
    match candidates {
        [] => Err(ModuleToKoreError::MissingEquationProduction {
            label: label.name.clone(),
        }),
        [id] => Ok(*id),
        candidates => Err(ModuleToKoreError::AmbiguousEquationProduction {
            label: label.name.clone(),
            productions: candidates.len(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_equation(
    equation: EquationInfo<'_>,
    left: &Term,
    right: &Term,
    requires: &Term,
    ensures: &Term,
    attributes: &KAttributes,
    claim: bool,
    valued: &BTreeSet<String>,
    converter: &TermConverter<'_, '_>,
    productions: &ProductionCatalog<'_>,
    injector: &SortInjector<'_, '_>,
    module_rules: &[Sentence],
    owise_competitors: &mut OwiseCompetitors,
    sort_variables: &SentenceSortVariables,
    condition_form: ConditionForm,
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = std::iter::once("R")
        .chain(sort_variables.names())
        .map(str::to_owned)
        .collect();
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort)?;
    // Every name of the rule, bound or free: its owise axiom holds them all beside the names of
    // its competitors.
    let avoid_variables = variable_names([left, right, requires, ensures]);
    let sentence = || located_sentence(claim, attributes);
    let requires = side_condition(
        requires,
        &predicate_sort,
        converter,
        condition_form,
        &sentence,
    )?;
    let ensures = side_condition(ensures, &result_sort, converter, condition_form, &sentence)?;
    let right = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![converter.convert(right)?, ensures],
    };
    let requires = if claim {
        requires
    } else {
        quantify_condition_only(requires, &predicate_sort, attributes, || {
            Ok(free_names([&converter.convert(left)?, &right]))
        })?
    };
    if attributes.has(AttributeKey::Owise) {
        if claim {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "owise claim".into(),
            });
        }
        return emit_owise_equation(
            equation,
            right,
            requires,
            attributes,
            valued,
            converter,
            productions,
            injector,
            module_rules,
            owise_competitors,
            sort_variables,
            &avoid_variables,
            condition_form,
        );
    }
    let equals = if equation.direct || claim {
        Pattern::Equals {
            operand_sort: Box::new(result_sort),
            result_sort: predicate_sort.clone(),
            left: Box::new(converter.convert(left)?),
            right: Box::new(right),
        }
    } else {
        let variables = equation
            .argument_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                Ok(Variable {
                    kind: VariableKind::Element,
                    name: format!("X{index}"),
                    sort: converter.convert_sort(sort)?,
                })
            })
            .collect::<Result<Vec<_>, TermConversionError>>()?;
        let application = Pattern::Application {
            symbol: converter.convert_label(equation.label)?,
            arguments: variables.iter().cloned().map(Pattern::Variable).collect(),
        };
        let mut matches = Pattern::Top {
            sort: predicate_sort.clone(),
        };
        // Invariant: `matches` is the conjunction, ending in top, of the `\in` constraints of the argument positions after the current one; the zip is traversed in reverse and each iteration prepends one position.
        for ((variable, child), sort) in variables
            .iter()
            .zip(equation.children)
            .zip(&equation.argument_sorts)
            .rev()
        {
            matches = Pattern::And {
                sort: predicate_sort.clone(),
                arguments: vec![
                    Pattern::In {
                        operand_sort: Box::new(converter.convert_sort(sort)?),
                        result_sort: predicate_sort.clone(),
                        left: Box::new(Pattern::Variable(variable.clone())),
                        right: Box::new(converter.convert(child)?),
                    },
                    matches,
                ],
            };
        }
        return equation_sentence(
            claim,
            Pattern::Implies {
                sort: predicate_sort.clone(),
                left: Box::new(Pattern::And {
                    sort: predicate_sort.clone(),
                    arguments: vec![requires, matches],
                }),
                right: Box::new(Pattern::Equals {
                    operand_sort: Box::new(result_sort),
                    result_sort: predicate_sort,
                    left: Box::new(application),
                    right: Box::new(right),
                }),
            },
            attributes,
            valued,
            parameters,
        );
    };
    equation_sentence(
        claim,
        Pattern::Implies {
            sort: predicate_sort,
            left: Box::new(requires),
            right: Box::new(equals),
        },
        attributes,
        valued,
        parameters,
    )
}

#[allow(clippy::too_many_arguments)]
fn emit_owise_equation(
    equation: EquationInfo<'_>,
    right: Pattern,
    requires: Pattern,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    converter: &TermConverter<'_, '_>,
    productions: &ProductionCatalog<'_>,
    injector: &SortInjector<'_, '_>,
    module_rules: &[Sentence],
    owise_competitors: &mut OwiseCompetitors,
    sort_variables: &SentenceSortVariables,
    avoid_variables: &BTreeSet<String>,
    condition_form: ConditionForm,
) -> Result<KoreSentence, ModuleToKoreError> {
    owise_competitors.scan_once(module_rules, injector, productions);
    let (candidates, failure) = owise_competitors.candidates(&equation);
    // Each competitor's classified variables are predicate sorts, so equal names may share a
    // binder without identifying symbol instances or term carriers.
    let sort_variables = candidates
        .iter()
        .fold(sort_variables.clone(), |variables, &index| {
            let (_, competitor_variables) = owise_competitors.injected[index]
                .as_ref()
                .expect("indexed competitors are injected rules");
            variables.union(competitor_variables)
        });
    let parameters = std::iter::once("R")
        .chain(sort_variables.names())
        .map(str::to_owned)
        .collect();
    let converter = converter.with_sort_variables(&sort_variables);
    let converter = &converter;
    // O1: bind one fresh KORE variable per argument and match the equation's own children.
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort)?;
    let variables = equation_variables(&equation, converter)?;
    let own_matches = equation_matches(
        &variables,
        equation.children,
        &equation.argument_sorts,
        &predicate_sort,
        converter,
    )?;

    // O2: reserve caller variables.
    let mut fresh = FreshNames::default();
    // Invariant: `fresh` has reserved every name of `avoid_variables` before `name`; each name is visited once.
    for name in avoid_variables {
        fresh.reserve(name.clone());
    }
    // O3: visit each executable same-signature competitor once in rule-catalog order.
    let mut competitors = Vec::new();
    // Invariant: `competitors` contains exactly the accepted rules before `index`, each with
    // refreshed variables.
    for &index in candidates {
        measure::bump(Counter::KompileOwiseCompetitorScans);
        let Some((
            Sentence::Rule {
                body,
                requires: competitor_requires,
                ensures: competitor_ensures,
                attributes: competitor_attributes,
            },
            _,
        )) = &owise_competitors.injected[index]
        else {
            unreachable!("indexed competitors are injected rules")
        };
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is not a sentence kind; only the listed variants are special here"
        )]
        let (competitor_left, competitor_right) = match body.unannotated() {
            Term::Rewrite { left, right } => (left.as_ref(), right.as_ref()),
            _ => (body, body),
        };
        // The axiom is one scope for names: `fresh` holds every name in use in it so far (the
        // owise rule's variables, every name minted, and the bound names of the competitors
        // before this one), compared by name whatever the sort. The refresh renames the
        // competitor's free variables to minted names. A variable a quantifier of the
        // competitor binds is local to that quantifier (`kast::binding`): it keeps its name
        // unless the name is in use, and is otherwise renamed, binder and bound occurrences
        // alike, to a fresh name. Every bound name is reserved before any name is minted for
        // this competitor or a later one, so no minted name captures a bound one and no bound
        // name meets another variable of its name.
        // A variable of the competitor's condition alone is bound inside the condition, as in the
        // competitor's own axiom (`quantify_condition_only`), so it is a bound name here too.
        let condition_only = condition_only_names(
            competitor_requires,
            [competitor_left, competitor_right, competitor_ensures],
            competitor_attributes,
        );
        let bound = binding::bound_names(competitor_left)
            .into_iter()
            .chain(binding::bound_names(competitor_requires))
            .chain(condition_only.iter().cloned())
            .collect::<BTreeSet<_>>();
        let taken = bound
            .iter()
            .filter(|name| fresh.contains(name))
            .cloned()
            .collect::<Vec<_>>();
        // Invariant: `fresh` has reserved every bound name before `name`.
        for name in &bound {
            fresh.reserve(name.clone());
        }
        let mut bound_renames = BTreeMap::new();
        // Invariant: `bound_renames` maps every taken name before `name` to a name `fresh`
        // minted for it, after reserving every bound name.
        for name in taken {
            let renamed = fresh.mint(&name);
            bound_renames.insert(name, renamed);
        }
        let mut renames = BTreeMap::new();
        let refreshed_left = refresh_variables(
            competitor_left,
            &BinderScope::default(),
            &bound_renames,
            &mut fresh,
            &mut renames,
        );
        let refreshed_requires = refresh_variables(
            competitor_requires,
            &BinderScope {
                named: condition_only.iter().cloned().collect(),
            },
            &bound_renames,
            &mut fresh,
            &mut renames,
        );
        let Term::Apply {
            arguments: competitor_children,
            ..
        } = peel_alias(&refreshed_left).unannotated()
        else {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "non-application function competitor for owise".into(),
            });
        };
        // A competitor's condition is its own: a refusal of it names the competitor.
        let condition = side_condition(
            &refreshed_requires,
            &predicate_sort,
            converter,
            condition_form,
            &|| located_sentence(false, competitor_attributes),
        )?;
        let matches = equation_matches(
            &variables,
            competitor_children,
            &equation.argument_sorts,
            &predicate_sort,
            converter,
        )?;
        // The competitor's condition as its own axiom states it (`quantify_condition_only`):
        // quantified inside over each variable of the condition alone, under the name the
        // refresh kept or gave it, in the order of first occurrence.
        let condition_only = condition_only
            .iter()
            .map(|name| {
                identifier::encode_variable(
                    bound_renames.get(name).unwrap_or(name),
                    VariableKind::Element,
                )
            })
            .collect::<BTreeSet<_>>();
        let wrapped = free_element_variables_in_order(&condition)
            .into_iter()
            .filter(|variable| condition_only.contains(&variable.name))
            .collect();
        let condition = generated_exists_all(&predicate_sort, wrapped, condition);
        let candidate = Pattern::And {
            sort: predicate_sort.clone(),
            arguments: vec![condition, matches],
        };
        // The competitor holds where some instance of its free variables matches and satisfies
        // it. Its free variables are those of the converted pattern, whose binders are the ones
        // the backend reads; a variable a quantifier of the competitor binds has its binder. They
        // are bound in the order of their sorts and, within a sort, of their first occurrences in
        // the refreshed left side and condition, never of their spellings: the order of nested
        // existentials does not change what they state, so it must not change with a renaming.
        let free = candidate.free_variables();
        let terms = variable_terms([&refreshed_left, &refreshed_requires]);
        let (mut first_occurrences, mut seen) = (Vec::new(), BTreeSet::new());
        // Invariant: `first_occurrences` lists, in preorder, every variable name met so far once,
        // and `seen` holds the same names.
        for root in [&refreshed_left, &refreshed_requires] {
            root.visit_preorder(&mut |node| {
                if let Term::Variable { name, .. } = node.unannotated()
                    && seen.insert(name.clone())
                {
                    first_occurrences.push(name.clone());
                }
            });
        }
        let mut quantified = Vec::new();
        // Invariant: `quantified` holds the key and the KORE variable of every refreshed
        // variable before `name` whose conversion is free in `candidate`.
        for (index, name) in first_occurrences.iter().enumerate() {
            let term = &terms[name];
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "Term is not a sentence kind; only the listed variants are special here"
            )]
            let key = match term.unannotated() {
                Term::Variable { sort, .. } => (sort.clone(), index),
                _ => unreachable!("variable_terms returns variables"),
            };
            let Some(variable) = take_kore_variable(converter.convert(term)?) else {
                unreachable!("collected terms are variables")
            };
            if free.contains(&variable) {
                quantified.push((key, variable));
            }
        }
        quantified.sort_by(|(left, _), (right, _)| left.cmp(right));
        // The first sorted variable is the outermost binder.
        competitors.push(generated_exists_all(
            &predicate_sort,
            quantified
                .into_iter()
                .map(|(_, variable)| variable)
                .collect(),
            candidate,
        ));
    }

    // A rule before which the scan stopped fails the equation after every earlier competitor.
    if let Some(error) = failure {
        return Err(error.clone());
    }
    // O4: preserve competitor order in a right-associated disjunction ending in bottom.
    competitors.push(Pattern::Bottom {
        sort: predicate_sort.clone(),
    });
    let mut competitors = competitors.into_iter().rev();
    let mut any_competitor = competitors
        .next()
        .expect("the competitor disjunction always ends in bottom");
    // Invariant: `any_competitor` is the disjunction of the already folded suffix.
    for competitor in competitors {
        any_competitor = Pattern::Or {
            sort: predicate_sort.clone(),
            arguments: vec![competitor, any_competitor],
        };
    }
    // O5: guard the equation with the negated competitor predicate and its own side conditions.
    let negative_match = Pattern::Not {
        sort: predicate_sort.clone(),
        argument: Box::new(any_competitor),
    };
    let application = Pattern::Application {
        symbol: converter.convert_label(equation.label)?,
        arguments: variables.iter().cloned().map(Pattern::Variable).collect(),
    };
    equation_sentence(
        false,
        Pattern::Implies {
            sort: predicate_sort.clone(),
            left: Box::new(Pattern::And {
                sort: predicate_sort.clone(),
                arguments: vec![
                    negative_match,
                    Pattern::And {
                        sort: predicate_sort.clone(),
                        arguments: vec![requires, own_matches],
                    },
                ],
            }),
            right: Box::new(Pattern::Equals {
                operand_sort: Box::new(result_sort),
                result_sort: predicate_sort,
                left: Box::new(application),
                right: Box::new(right),
            }),
        },
        attributes,
        valued,
        parameters,
    )
}

/// The executable competitors of a module's owise equations, grouped by head label and argument
/// sorts.
///
/// Whether a rule competes with an owise equation depends only on the rule and on the equation's
/// label and argument sorts, and the module's rule list is fixed during emission, so one scan of
/// the rules serves every owise equation of the module. The scan runs when the first owise
/// equation needs it and stops at the first rule whose injection or equation shape fails; that
/// rule's error is reported after the competitors that precede it, where a full scan would meet it.
#[derive(Default)]
pub(super) struct OwiseCompetitors {
    scanned: bool,
    injected: Vec<Option<(Sentence, SentenceSortVariables)>>,
    by_signature: BTreeMap<(Label, Vec<Sort>), Vec<usize>>,
    failure: Option<ModuleToKoreError>,
}

impl OwiseCompetitors {
    fn scan_once(
        &mut self,
        module_rules: &[Sentence],
        injector: &SortInjector<'_, '_>,
        productions: &ProductionCatalog<'_>,
    ) {
        if !self.scanned {
            self.scan(module_rules, injector, productions);
        }
    }

    /// The indices of the competitors of `equation` in rule order, and the error of the rule at
    /// which the scan stopped; every returned index precedes that rule.
    fn candidates(&self, equation: &EquationInfo<'_>) -> (&[usize], Option<&ModuleToKoreError>) {
        let candidates = self
            .by_signature
            .get(&(equation.label.clone(), equation.argument_sorts.clone()))
            .map_or(&[][..], Vec::as_slice);
        (candidates, self.failure.as_ref())
    }

    fn scan(
        &mut self,
        module_rules: &[Sentence],
        injector: &SortInjector<'_, '_>,
        productions: &ProductionCatalog<'_>,
    ) {
        self.scanned = true;
        self.injected = vec![None; module_rules.len()];
        // Invariant: `by_signature` holds, in rule order, every rule before `index` that is an
        // executable equation, and no earlier rule failed.
        for (index, sentence) in module_rules.iter().enumerate() {
            measure::bump(Counter::KompileOwiseCompetitorScans);
            let (injected, sort_variables) = match injector.inject_sentence_bound(sentence) {
                Ok(injected) => injected,
                Err(error) => {
                    self.failure = Some(error.into());
                    return;
                }
            };
            let Sentence::Rule { body, .. } = &injected else {
                continue;
            };
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "Term is not a sentence kind; only the listed variants are special here"
            )]
            let competitor_left = match body.unannotated() {
                Term::Rewrite { left, .. } => left.as_ref(),
                _ => body,
            };
            let signature = match equation_info(competitor_left, sentence.attributes(), productions)
            {
                Ok(Some(competitor)) => {
                    (competitor.label.clone(), competitor.argument_sorts.clone())
                }
                Ok(None) => continue,
                Err(error) => {
                    self.failure = Some(error);
                    return;
                }
            };
            if ignore_owise_competitor(sentence) {
                continue;
            }
            self.by_signature.entry(signature).or_default().push(index);
            self.injected[index] = Some((injected, sort_variables));
        }
    }
}

fn ignore_owise_competitor(sentence: &Sentence) -> bool {
    sentence.attributes().has_any(&[
        AttributeKey::Owise,
        AttributeKey::Simplification,
        AttributeKey::NonExecutable,
    ])
}

fn equation_variables(
    equation: &EquationInfo<'_>,
    converter: &TermConverter<'_, '_>,
) -> Result<Vec<Variable>, TermConversionError> {
    equation
        .argument_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            Ok(Variable {
                kind: VariableKind::Element,
                name: format!("X{index}"),
                sort: converter.convert_sort(sort)?,
            })
        })
        .collect()
}

fn equation_matches(
    variables: &[Variable],
    children: &[Term],
    sorts: &[Sort],
    predicate_sort: &KoreSort,
    converter: &TermConverter<'_, '_>,
) -> Result<Pattern, TermConversionError> {
    let mut matches = Pattern::Top {
        sort: predicate_sort.clone(),
    };
    // Invariant: `matches` is the conjunction, ending in top, of the `\in` constraints of the positions of `variables`, `children`, and `sorts` after the current one; the zip is traversed in reverse and each iteration prepends one position.
    for ((variable, child), sort) in variables.iter().zip(children).zip(sorts).rev() {
        matches = Pattern::And {
            sort: predicate_sort.clone(),
            arguments: vec![
                Pattern::In {
                    operand_sort: Box::new(converter.convert_sort(sort)?),
                    result_sort: predicate_sort.clone(),
                    left: Box::new(Pattern::Variable(variable.clone())),
                    right: Box::new(converter.convert(child)?),
                },
                matches,
            ],
        };
    }
    Ok(matches)
}

fn variable_names<'a>(roots: impl IntoIterator<Item = &'a Term>) -> BTreeSet<String> {
    variable_terms(roots).into_keys().collect()
}

fn variable_terms<'a>(roots: impl IntoIterator<Item = &'a Term>) -> BTreeMap<String, Term> {
    let mut variables = BTreeMap::new();
    // Invariant: `variables` maps every variable name in the roots before `root` to its first preorder occurrence; each root's preorder traversal visits every node once.
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated() {
                variables
                    .entry(name.clone())
                    .or_insert_with(|| term.clone());
            }
        });
    }
    variables
}

/// The names the quantifiers of a competitor bind where a term stands: a quantifier binds exactly
/// its own variable in its body (`kast::binding`).
#[derive(Clone, Default)]
struct BinderScope {
    named: Vec<String>,
}

impl BinderScope {
    fn binds(&self, name: &str) -> bool {
        self.named.iter().any(|bound| bound == name)
    }

    /// The scope of the body of `term` when it is a quantifier over a variable
    /// (`kast::binding::quantifier`): `None` for any other term.
    fn of_body(&self, term: &Term) -> Option<Self> {
        let (name, _) = binding::quantifier(term)?.variable()?;
        let mut body = self.clone();
        body.named.push(name.to_owned());
        Some(body)
    }
}

/// `variable`, a quantifier's binder or a variable it binds, with the name `bound_renames` gives
/// its name, if any.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is not a sentence kind; only a variable is renamed"
)]
fn rename_bound(variable: &Term, bound_renames: &BTreeMap<String, String>) -> Term {
    match variable.unannotated() {
        Term::Variable { name, sort } => Term::Variable {
            name: bound_renames.get(name).unwrap_or(name).clone(),
            sort: sort.clone(),
        }
        .with_metadata(variable.metadata().cloned().unwrap_or_default()),
        _ => variable.clone(),
    }
}

// Invariant: each call rebuilds one node of `term` and recurses only into its direct subterms, so the finite `term` bounds the calls; `renames` maps every (name, sort) identity of a free variable met so far to the one `_Gen` name `fresh` minted for it.
/// `term` with every free variable renamed to a `_Gen` name `fresh` mints, the same identity to
/// the same name; a variable a quantifier binds (in `scope`, or by a quantifier of `term`), and
/// each quantifier's binder, takes the name `bound_renames` gives its name, or keeps it.
fn refresh_variables(
    term: &Term,
    scope: &BinderScope,
    bound_renames: &BTreeMap<String, String>,
    fresh: &mut FreshNames,
    renames: &mut BTreeMap<(String, Option<Sort>), String>,
) -> Term {
    let refreshed = match term.unannotated() {
        Term::Variable { name, .. } if scope.binds(name) => {
            rename_bound(term.unannotated(), bound_renames)
        }
        Term::Variable { name, sort } => {
            let identity = (name.clone(), sort.clone());
            let name = renames
                .entry(identity)
                .or_insert_with(|| fresh.mint("_Gen"));
            Term::Variable {
                name: name.clone(),
                sort: sort.clone(),
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(refresh_variables(
                left,
                scope,
                bound_renames,
                fresh,
                renames,
            )),
            right: Box::new(refresh_variables(
                right,
                scope,
                bound_renames,
                fresh,
                renames,
            )),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(refresh_variables(
                pattern,
                scope,
                bound_renames,
                fresh,
                renames,
            )),
            alias: Box::new(refresh_variables(
                alias,
                scope,
                bound_renames,
                fresh,
                renames,
            )),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| refresh_variables(item, scope, bound_renames, fresh, renames))
                .collect(),
        ),
        Term::Apply { label, arguments } => match scope.of_body(term.unannotated()) {
            Some(body) => Term::Apply {
                label: label.clone(),
                arguments: vec![
                    rename_bound(&arguments[0], bound_renames),
                    refresh_variables(&arguments[1], &body, bound_renames, fresh, renames),
                ],
            },
            None => Term::Apply {
                label: label.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        refresh_variables(argument, scope, bound_renames, fresh, renames)
                    })
                    .collect(),
            },
        },
        Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
        Term::Token { token, sort } => Term::Token {
            token: token.clone(),
            sort: sort.clone(),
        },
        Term::Annotated { .. } => unreachable!(),
    };
    refreshed.with_metadata(term.metadata().cloned().unwrap_or_default())
}

fn equation_sentence(
    claim: bool,
    pattern: Pattern,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    parameters: Vec<String>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let overrides = variable_list_attribute_overrides(attributes, &pattern)?;
    let attributes = emit_attributes(attributes.semantic_entries(), valued, &overrides);
    Ok(if claim {
        KoreSentence::Claim {
            parameters,
            pattern: Box::new(pattern),
            attributes,
        }
    } else {
        KoreSentence::Axiom {
            parameters,
            pattern: Box::new(pattern),
            attributes,
        }
    })
}

fn variable_list_attribute_overrides(
    attributes: &KAttributes,
    pattern: &Pattern,
) -> Result<BTreeMap<String, Vec<Pattern>>, ModuleToKoreError> {
    let mut variables = BTreeMap::new();
    collect_pattern_variables(pattern, &mut variables);
    [AttributeKey::Concrete, AttributeKey::Symbolic]
        .into_iter()
        .filter_map(|key| attributes.string(key).map(|value| (key.as_str(), value)))
        .map(|(key, value)| {
            let arguments = value
                .split(',')
                .map(str::trim)
                .filter(|name| !name.is_empty())
                .map(|name| {
                    let name = name.trim_start_matches('@');
                    let candidates = [
                        identifier::encode_variable(name, VariableKind::Element),
                        identifier::encode_variable(name, VariableKind::Set),
                    ];
                    candidates
                        .iter()
                        .find_map(|name| variables.get(name).cloned())
                        .map(Pattern::Variable)
                        .ok_or_else(|| ModuleToKoreError::UnsupportedRuleKind {
                            kind: format!(
                                "{key} attribute refers to missing free variable {name:?}"
                            ),
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok((key.to_owned(), arguments))
        })
        .collect()
}

fn collect_pattern_variables(pattern: &Pattern, variables: &mut BTreeMap<String, Variable>) {
    visit_pattern_variables(pattern, &mut |variable| {
        variables
            .entry(variable.name.clone())
            .or_insert_with(|| variable.clone());
    });
}

pub(super) fn check_variable_sorts(
    sentence: &KoreSentence,
    describe: &dyn Fn() -> String,
) -> Result<(), ModuleToKoreError> {
    let pattern = match sentence {
        KoreSentence::Axiom { pattern, .. } | KoreSentence::Claim { pattern, .. } => pattern,
        KoreSentence::Import { .. }
        | KoreSentence::SortDeclaration { .. }
        | KoreSentence::SymbolDeclaration { .. }
        | KoreSentence::AliasDeclaration { .. } => return Ok(()),
    };
    let mut by_name = BTreeMap::<String, BTreeSet<KoreSort>>::new();
    visit_pattern_variables(pattern, &mut |variable| {
        by_name
            .entry(variable.name.clone())
            .or_default()
            .insert(variable.sort.clone());
    });
    let Some((name, sorts)) = by_name.into_iter().find(|(_, sorts)| sorts.len() > 1) else {
        return Ok(());
    };
    Err(ModuleToKoreError::InconsistentVariableSorts {
        sentence: describe(),
        name,
        sorts: sorts.into_iter().map(|sort| sort.to_string()).collect(),
    })
}

// stack-accepted(emission-width): emission turns a rule's arity, `[owise]` competitors and flat cells into nesting the term-depth measure does not count; 32,000 arguments or competitors and 4,000 flat cells pass on 8 MiB, after time or memory has run out. See docs/backend-port.md#stack-bounds.
fn visit_pattern_variables<'a>(pattern: &'a Pattern, visitor: &mut impl FnMut(&'a Variable)) {
    match pattern {
        Pattern::Variable(variable) => visitor(variable),
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                visit_pattern_variables(argument, visitor);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => visit_pattern_variables(argument, visitor),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            visit_pattern_variables(left, visitor);
            visit_pattern_variables(right, visitor);
        }
        Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. }
        | Pattern::Mu { variable, body }
        | Pattern::Nu { variable, body } => {
            visitor(variable);
            visit_pattern_variables(body, visitor);
        }
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

pub(super) fn substitute_equation_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_equation_sort(parameter, substitution))
                .collect(),
        )
    })
}

/// How a sentence's `requires` and `ensures` are written in the emitted KORE.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionForm {
    /// The predicate the condition states ([`predicate_at`]): the Rust target, whose backend
    /// reads a condition as a predicate.
    Predicate,
    /// The whole condition as one Bool term, `\equals{SortBool{}, R}(c, true)`: the LLVM
    /// target, whose interpreter evaluates a side condition as a Bool term. A predicate condition
    /// has no evaluation there in either form, so that target keeps its output.
    BoolTerm,
}

impl ConditionForm {
    pub(super) fn for_backend(backend: CompilationBackend) -> Self {
        match backend {
            CompilationBackend::Llvm => ConditionForm::BoolTerm,
            CompilationBackend::Rust => ConditionForm::Predicate,
        }
    }
}

/// The condition `condition` of a rule, at `sort`, quantified existentially inside the condition
/// over each element variable free in it and free nowhere else in the rule (`elsewhere`, the
/// names of the free variables of the rest of the rule, computed only when the condition has a
/// free variable; one name has one sort in an axiom),
/// in the order of their first free occurrences, the first outermost. A variable a `concrete` or
/// `symbolic` attribute names is left free: the attribute reads it.
///
/// A rule's free variables are universally quantified over the whole rule. A variable `Z` of the
/// condition alone does not occur in the conclusion, so `∀Z. (c(Z) → φ)` is `(∃Z. c(Z)) → φ`:
/// the rule means the same, and it applies where some value of `Z` satisfies the condition,
/// which can be decided without the value matching gives the variables of the left side. A
/// claim's condition means the same in either form, and is left as written so that a claim keeps
/// its bytes.
fn quantify_condition_only(
    condition: Pattern,
    sort: &KoreSort,
    attributes: &KAttributes,
    elsewhere: impl FnOnce() -> Result<BTreeSet<String>, TermConversionError>,
) -> Result<Pattern, TermConversionError> {
    let free = free_element_variables_in_order(&condition);
    if free.is_empty() {
        return Ok(condition);
    }
    let elsewhere = elsewhere()?;
    let named = [AttributeKey::Concrete, AttributeKey::Symbolic]
        .into_iter()
        .filter_map(|key| attributes.string(key))
        .flat_map(|value| value.split(','))
        .map(str::trim)
        .map(|name| identifier::encode_variable(name, VariableKind::Element))
        .collect::<BTreeSet<_>>();
    let only = free
        .into_iter()
        .filter(|variable| !elsewhere.contains(&variable.name) && !named.contains(&variable.name))
        .collect::<Vec<_>>();
    Ok(generated_exists_all(sort, only, condition))
}

/// The names of the element variables free in `condition` and in none of `elsewhere`, nor named by a
/// `concrete` or `symbolic` attribute: the variables [`quantify_condition_only`] quantifies,
/// read on the rule's terms.
fn condition_only_names<'t>(
    condition: &Term,
    elsewhere: impl IntoIterator<Item = &'t Term>,
    attributes: &KAttributes,
) -> BTreeSet<String> {
    // A set variable is left free, as `quantify_condition_only` leaves it.
    let mut names = binding::free_variables(condition);
    names.retain(|name| !name.starts_with('@'));
    for term in elsewhere {
        for name in binding::free_variables(term) {
            names.remove(&name);
        }
    }
    for key in [AttributeKey::Concrete, AttributeKey::Symbolic] {
        for name in attributes
            .string(key)
            .into_iter()
            .flat_map(|value| value.split(','))
        {
            names.remove(name.trim());
        }
    }
    names
}

/// The names of the variables free in any of `patterns`.
fn free_names<'p>(patterns: impl IntoIterator<Item = &'p Pattern>) -> BTreeSet<String> {
    patterns
        .into_iter()
        .flat_map(Pattern::free_variables)
        .map(|variable| variable.name)
        .collect()
}

/// The element variables free in `pattern`, each once, in the order of their first free
/// occurrence in preorder.
fn free_element_variables_in_order(pattern: &Pattern) -> Vec<Variable> {
    // Invariant: `variables` holds, in order, the element variables met free so far; `bound`
    // the variables of the binders enclosing `pattern`, innermost last.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "only variables and binders are special; every other pattern is walked through"
    )]
    fn walk<'a>(
        pattern: &'a Pattern,
        bound: &mut Vec<&'a Variable>,
        variables: &mut Vec<Variable>,
    ) {
        match pattern {
            Pattern::Variable(variable) => {
                if variable.kind == VariableKind::Element
                    && !bound.contains(&variable)
                    && !variables.contains(variable)
                {
                    variables.push(variable.clone());
                }
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                bound.push(variable);
                walk(body, bound, variables);
                bound.pop();
            }
            other => {
                for child in crate::kore::walk::children(other) {
                    walk(child, bound, variables);
                }
            }
        }
    }
    let mut variables = Vec::new();
    walk(pattern, &mut Vec::new(), &mut variables);
    variables
}

/// The condition `condition` of the sentence `sentence` names, at `result_sort`, in the form
/// `form`.
///
/// In the predicate form, a condition whose spine holds an author's `#Equals` whose operands are
/// not both terms and not both predicates ([`mixed_spine_equality`]) is refused: it states no
/// condition (a predicate is all of its sort or nothing, and a connective over terms a set of
/// values), and written as a predicate, `{P #Equals true}` would be the pattern
/// `\equals{SortBool{}, R}(P, \dv{SortBool{}}("true"))`, the form in which KORE written by other
/// tools states that a whole condition P holds, which k-rust's backend reads as P.
fn side_condition(
    condition: &Term,
    result_sort: &KoreSort,
    converter: &TermConverter<'_, '_>,
    form: ConditionForm,
    sentence: &dyn Fn() -> String,
) -> Result<Pattern, ModuleToKoreError> {
    if is_true(condition) {
        return Ok(Pattern::Top {
            sort: result_sort.clone(),
        });
    }
    let bool_sort = encode_kore_sort(&Sort::builtin(BuiltinSort::Bool));
    let converted = converter.convert(condition)?;
    Ok(match form {
        ConditionForm::Predicate => {
            if mixed_spine_equality(&converted) {
                return Err(ModuleToKoreError::MixedConditionEquality {
                    sentence: sentence(),
                });
            }
            predicate_at(&converted, result_sort, &bool_sort)
        }
        ConditionForm::BoolTerm => bool_leaf(converted, result_sort, &bool_sort),
    })
}

/// A sentence as a compile refusal names it: its kind, its label and its source position.
fn located_sentence(claim: bool, attributes: &KAttributes) -> String {
    let kind = if claim { "claim" } else { "rule" };
    let label = attributes
        .string(AttributeKey::Label)
        .map(|label| format!(" [{label}]"));
    let position = match (attributes.source(), attributes.location()) {
        (Some(source), Some(location)) => Some(format!(
            " at {source}:{}:{}",
            location.start_line, location.start_column
        )),
        (Some(source), None) => Some(format!(" in {source}")),
        (None, Some(location)) => Some(format!(
            " at line {}, column {}",
            location.start_line, location.start_column
        )),
        (None, None) => None,
    };
    match (label, position) {
        (None, None) => match attributes.string(AttributeKey::UniqueId) {
            Some(id) => format!("{kind} {id}"),
            None => format!("{kind} with no label or position"),
        },
        (label, position) => format!(
            "{kind}{}{}",
            label.unwrap_or_default(),
            position.unwrap_or_default()
        ),
    }
}

/// The shape of an operand of an `#Equals` on a condition's spine ([`mixed_spine_equality`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OperandShape {
    /// A term: it denotes one value.
    Term,
    /// A predicate: a pattern that is not a term and has no term directly below its spine
    /// (`{X #Equals 1}`, `#Ceil(..)`, `#Not` of one). It denotes all of its sort or nothing.
    Predicate,
    /// A matching-logic connective with a term directly below its spine
    /// (`(X ==Int 1) #Or (X ==Int 2)`, `1 #Or 2`): the set of values its connectives build from
    /// the terms.
    Connective,
}

/// The shape of an operand, read through its sort injections: `inj` is the identity on values, so
/// an injected connective or predicate has the shape of what it injects.
fn operand_shape(pattern: &Pattern) -> OperandShape {
    let pattern = without_injections(pattern);
    if is_term(pattern) {
        OperandShape::Term
    } else if has_term_below_spine(pattern) {
        OperandShape::Connective
    } else {
        OperandShape::Predicate
    }
}

/// Whether the spine of `condition` (the condition as converted) holds an `#Equals` whose
/// operands are not both terms and not both predicates ([`OperandShape`]).
///
/// The spine is the condition's root and every operand of a connective (`\and`, `\or`, `\not`,
/// `\implies`, `\iff`, `\exists`, `\forall`) on it; the operands of an atom (`\equals`,
/// `\ceil`, `\floor`, `\in`) and of a term are not on it. On the spine an `#Equals` of two terms
/// is an equality of values and one of two predicates their `\iff`, and both are conditions. Any
/// other pair states none: a predicate denotes all of its sort or nothing, so it never equals one
/// value, and a connective over terms denotes a set of values, so an equality with it compares
/// sets (`{(A #Or B) #Equals true}` holds only where A and B are both true).
fn mixed_spine_equality(condition: &Pattern) -> bool {
    match condition {
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().any(mixed_spine_equality)
        }
        Pattern::Not { argument, .. } => mixed_spine_equality(argument),
        Pattern::Implies { left, right, .. } | Pattern::Iff { left, right, .. } => {
            mixed_spine_equality(left) || mixed_spine_equality(right)
        }
        Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => mixed_spine_equality(body),
        Pattern::Equals { left, right, .. } => !matches!(
            (operand_shape(left), operand_shape(right)),
            (OperandShape::Term, OperandShape::Term)
                | (OperandShape::Predicate, OperandShape::Predicate)
        ),
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::In { .. }
        | Pattern::Next { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Mu { .. }
        | Pattern::Nu { .. }
        | Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Application { .. }
        | Pattern::AssociativeApplication { .. }
        | Pattern::DomainValue { .. } => false,
    }
}

/// Whether `pattern` is a term: no matching-logic connective or atom at its root.
fn is_term(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Application { .. }
        | Pattern::AssociativeApplication { .. }
        | Pattern::DomainValue { .. } => true,
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::And { .. }
        | Pattern::Or { .. }
        | Pattern::Not { .. }
        | Pattern::Next { .. }
        | Pattern::Implies { .. }
        | Pattern::Iff { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Exists { .. }
        | Pattern::Forall { .. }
        | Pattern::Mu { .. }
        | Pattern::Nu { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. } => false,
    }
}

/// `pattern` without the sort injections `inj{_, _}(..)` wrapped around it.
fn without_injections(mut pattern: &Pattern) -> &Pattern {
    while let Pattern::Application { symbol, arguments } = pattern
        && symbol.name == "inj"
        && let [argument] = arguments.as_slice()
    {
        pattern = argument;
    }
    pattern
}

/// Whether a term stands directly below the spine of `pattern` (`pattern` itself included),
/// reading through sort injections.
fn has_term_below_spine(pattern: &Pattern) -> bool {
    match without_injections(pattern) {
        Pattern::And { arguments, .. } | Pattern::Or { arguments, .. } => {
            arguments.iter().any(has_term_below_spine)
        }
        Pattern::Not { argument, .. } => has_term_below_spine(argument),
        Pattern::Implies { left, right, .. } | Pattern::Iff { left, right, .. } => {
            has_term_below_spine(left) || has_term_below_spine(right)
        }
        Pattern::Exists { body, .. } | Pattern::Forall { body, .. } => has_term_below_spine(body),
        Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. }
        | Pattern::Next { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Mu { .. }
        | Pattern::Nu { .. } => false,
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Application { .. }
        | Pattern::AssociativeApplication { .. }
        | Pattern::DomainValue { .. } => true,
    }
}

/// `\equals{SortBool{}, R}(term, \dv{SortBool{}}("true"))`: the predicate "term is true".
fn bool_leaf(term: Pattern, result_sort: &KoreSort, bool_sort: &KoreSort) -> Pattern {
    Pattern::Equals {
        operand_sort: Box::new(bool_sort.clone()),
        result_sort: result_sort.clone(),
        left: Box::new(term),
        right: Box::new(Pattern::DomainValue {
            sort: bool_sort.clone(),
            value: "true".into(),
        }),
    }
}

/// A condition as the predicate it states, at the sentence's sort `result_sort`.
///
/// A condition is a matching-logic spine over Bool terms. The spine's connectives (`\top`,
/// `\bottom`, `\and`, `\or`, `\not`, `\implies`, `\iff`, `\exists`, `\forall`) are predicate
/// connectives, re-sorted at `result_sort` with their operands rebuilt the same way; its atoms
/// (`\equals`, `\ceil`, `\floor`, `\in`) keep their operand sort and operands and take
/// `result_sort`; any other pattern directly below the spine is a Bool term t, which stands for
/// the predicate `t = true` ([`bool_leaf`]). Writing the whole condition as one Bool term
/// instead would state something else whenever its root is a connective: a predicate at sort
/// Bool is all of Bool or empty, never `{true}`, and `\exists{Bool}(Y, t)` and
/// `\implies{Bool}(a, b)` are sets of Bool values, not the conditions `exists Y. t` and
/// `a implies b`. A plain Bool condition is one leaf, written as before.
///
/// The operands of an atom are terms and are not rebuilt: a connective there is a set
/// operation on values, which the definition checks refuse.
pub(crate) fn predicate_at(
    pattern: &Pattern,
    result_sort: &KoreSort,
    bool_sort: &KoreSort,
) -> Pattern {
    let at = |pattern: &Pattern| predicate_at(pattern, result_sort, bool_sort);
    let sort = result_sort.clone();
    match pattern {
        Pattern::Top { .. } => Pattern::Top { sort },
        Pattern::Bottom { .. } => Pattern::Bottom { sort },
        Pattern::And { arguments, .. } => Pattern::And {
            sort,
            arguments: arguments.iter().map(at).collect(),
        },
        Pattern::Or { arguments, .. } => Pattern::Or {
            sort,
            arguments: arguments.iter().map(at).collect(),
        },
        Pattern::Not { argument, .. } => Pattern::Not {
            sort,
            argument: Box::new(at(argument)),
        },
        Pattern::Implies { left, right, .. } => Pattern::Implies {
            sort,
            left: Box::new(at(left)),
            right: Box::new(at(right)),
        },
        Pattern::Iff { left, right, .. } => Pattern::Iff {
            sort,
            left: Box::new(at(left)),
            right: Box::new(at(right)),
        },
        Pattern::Exists { variable, body, .. } => Pattern::Exists {
            sort,
            variable: variable.clone(),
            body: Box::new(at(body)),
        },
        Pattern::Forall { variable, body, .. } => Pattern::Forall {
            sort,
            variable: variable.clone(),
            body: Box::new(at(body)),
        },
        Pattern::Equals {
            operand_sort,
            left,
            right,
            ..
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: sort,
            left: left.clone(),
            right: right.clone(),
        },
        Pattern::Ceil {
            operand_sort,
            argument,
            ..
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: sort,
            argument: argument.clone(),
        },
        Pattern::Floor {
            operand_sort,
            argument,
            ..
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: sort,
            argument: argument.clone(),
        },
        Pattern::In {
            operand_sort,
            left,
            right,
            ..
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: sort,
            left: left.clone(),
            right: right.clone(),
        },
        term @ (Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Application { .. }
        | Pattern::AssociativeApplication { .. }
        | Pattern::DomainValue { .. }
        | Pattern::Next { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Mu { .. }
        | Pattern::Nu { .. }) => bool_leaf(term.clone(), result_sort, bool_sort),
    }
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort.is_builtin(BuiltinSort::Bool)
    )
}

fn take_kore_variable(mut pattern: Pattern) -> Option<Variable> {
    let Pattern::Variable(variable) = &mut pattern else {
        return None;
    };
    Some(std::mem::replace(
        variable,
        Variable {
            kind: VariableKind::Element,
            name: String::new(),
            sort: KoreSort::Variable(String::new()),
        },
    ))
}

/// The variables a rule's or claim's right side quantifies existentially: the `?` variables that
/// occur free in `right` or in `ensures`, in the order of their first free occurrences (`right`
/// first, each in preorder), each converted from that occurrence. The order of nested
/// existentials does not change what they state, so it follows positions, never spellings: a
/// renaming leaves it as it is.
///
/// A `?` variable is existential over the right side and the `ensures` together, so it is
/// quantified once around both. A quantifier inside either binds its own variable there and
/// nowhere else (`kast::binding`); its binder and bound occurrences are not free, so it is not
/// quantified again outside, and every binder built over these variables has its variable free
/// in its body (K3). `right` and `ensures` are separate terms: a quantifier in one binds nothing
/// in the other.
fn free_existentials<'t>(right: &'t Term, ensures: &'t Term) -> Vec<(&'t str, &'t Term)> {
    let (mut found, mut seen) = (Vec::new(), BTreeSet::new());
    // Invariant: `found` lists, in the order of their first free occurrences in the roots already
    // walked (`right`, then `ensures`, each in preorder), every `?` name with a free occurrence
    // there, with that occurrence; `seen` holds the same names.
    for root in [right, ensures] {
        for occurrence in binding::occurrences(root) {
            if occurrence.role == binding::Role::Free
                && occurrence.name.starts_with('?')
                && seen.insert(occurrence.name)
            {
                found.push((occurrence.name, occurrence.node));
            }
        }
    }
    found
}

fn existential_variables(
    right: &Term,
    ensures: &Term,
    converter: &TermConverter<'_, '_>,
) -> Result<Vec<Variable>, TermConversionError> {
    free_existentials(right, ensures)
        .into_iter()
        .map(
            |(_, term)| match take_kore_variable(converter.convert(term)?) {
                Some(variable) => Ok(variable),
                None => unreachable!("collected terms are variables"),
            },
        )
        .collect()
}

fn existential_names(right: &Term, ensures: &Term) -> Vec<String> {
    free_existentials(right, ensures)
        .into_iter()
        .map(|(name, _)| name.to_owned())
        .collect()
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use indoc::indoc;
    use serde_json::json;

    use super::*;

    #[test]
    fn equation_selection_requires_exact_metadata_or_a_unique_label() {
        let parsed = crate::outer::parse(
            "overloaded-equation.k",
            indoc! {r#"
                module MAIN
                  syntax X ::= "fx(" X ")" [function, symbol(f)]
                  syntax Y ::= "fy(" Y ")" [function, symbol(f)]
                  syntax X ::= "other" [symbol(other)]
                endmodule
            "#},
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let label = Label::new("f");
        let argument = Term::Variable {
            name: "ARG".into(),
            sort: None,
        };
        let candidates = catalog.productions_for(&LabelHead::from(&label));
        assert_eq!(candidates.len(), 2);
        for &selected in candidates {
            let application = annotated_application(
                label.clone(),
                vec![argument.clone()],
                catalog.identity(selected),
            );
            assert_eq!(
                resolve_equation_production(&application, &label, &catalog).unwrap(),
                catalog.production(selected),
                "same-label overloads must retain their selected argument and result sorts"
            );
        }
        let other = catalog.productions_for(&LabelHead::new("other"))[0];
        let unique = Term::apply("other", Vec::new());
        assert_eq!(
            resolve_equation_production(&unique, &Label::new("other"), &catalog).unwrap(),
            catalog.production(other)
        );
        for stale in [
            catalog.identity(other),
            crate::kast::ProductionIdentity::from_hex(&"ff".repeat(16)).unwrap(),
        ] {
            let application = annotated_application(label.clone(), vec![argument.clone()], stale);
            assert!(matches!(
                resolve_equation_production(&application, &label, &catalog),
                Err(ModuleToKoreError::InvalidEquationProduction { .. })
            ));
        }
        let ambiguous = Term::Apply {
            label: label.clone(),
            arguments: vec![argument],
        };
        assert!(matches!(
            resolve_equation_production(&ambiguous, &label, &catalog),
            Err(ModuleToKoreError::AmbiguousEquationProduction { productions: 2, .. })
        ));
    }

    /// `predicate_at` of a KORE pattern written at sort Bool, at sort `R`.
    fn predicate(condition: &str) -> String {
        let pattern = crate::kore::parser::parse_pattern(condition).unwrap();
        let bool_sort = encode_kore_sort(&Sort::builtin(BuiltinSort::Bool));
        let predicate = predicate_at(&pattern, &KoreSort::Variable("R".into()), &bool_sort);
        crate::kore::printer::Printer::compact().print_pattern(&predicate)
    }

    fn printed(pattern: &str) -> String {
        crate::kore::printer::Printer::compact()
            .print_pattern(&crate::kore::parser::parse_pattern(pattern).unwrap())
    }

    const A: &str = r#"Lbla{}(VarX:SortInt{})"#;
    const B: &str = r#"Lblb{}(VarX:SortInt{})"#;

    fn leaf_at_r(term: &str) -> String {
        format!(r#"\equals{{SortBool{{}}, R}}({term}, \dv{{SortBool{{}}}}("true"))"#)
    }

    #[test]
    fn predicate_at_reads_a_bool_term_as_one_leaf() {
        assert_eq!(predicate(A), printed(&leaf_at_r(A)));
    }

    #[test]
    fn predicate_at_resorts_every_connective_of_the_spine() {
        let (a, b) = (leaf_at_r(A), leaf_at_r(B));
        for (condition, expected) in [
            (r"\top{SortBool{}}()".to_owned(), r"\top{R}()".to_owned()),
            (
                r"\bottom{SortBool{}}()".to_owned(),
                r"\bottom{R}()".to_owned(),
            ),
            (
                format!(r"\and{{SortBool{{}}}}({A}, {B})"),
                format!(r"\and{{R}}({a}, {b})"),
            ),
            (
                format!(r"\or{{SortBool{{}}}}({A}, {B})"),
                format!(r"\or{{R}}({a}, {b})"),
            ),
            (
                format!(r"\not{{SortBool{{}}}}({A})"),
                format!(r"\not{{R}}({a})"),
            ),
            (
                format!(r"\implies{{SortBool{{}}}}({A}, {B})"),
                format!(r"\implies{{R}}({a}, {b})"),
            ),
            (
                format!(r"\iff{{SortBool{{}}}}({A}, {B})"),
                format!(r"\iff{{R}}({a}, {b})"),
            ),
            (
                format!(r"\exists{{SortBool{{}}}}(VarX:SortInt{{}}, {A})"),
                format!(r"\exists{{R}}(VarX:SortInt{{}}, {a})"),
            ),
            (
                format!(r"\forall{{SortBool{{}}}}(VarX:SortInt{{}}, {A})"),
                format!(r"\forall{{R}}(VarX:SortInt{{}}, {a})"),
            ),
        ] {
            assert_eq!(predicate(&condition), printed(&expected), "{condition}");
        }
    }

    #[test]
    fn predicate_at_resorts_atoms_and_keeps_their_operands() {
        for (condition, expected) in [
            (
                r#"\equals{SortInt{}, SortBool{}}(VarX:SortInt{}, \dv{SortInt{}}("1"))"#,
                r#"\equals{SortInt{}, R}(VarX:SortInt{}, \dv{SortInt{}}("1"))"#,
            ),
            (
                r"\ceil{SortInt{}, SortBool{}}(Lblf{}(VarX:SortInt{}))",
                r"\ceil{SortInt{}, R}(Lblf{}(VarX:SortInt{}))",
            ),
            (
                r"\floor{SortInt{}, SortBool{}}(Lblf{}(VarX:SortInt{}))",
                r"\floor{SortInt{}, R}(Lblf{}(VarX:SortInt{}))",
            ),
            (
                r"\in{SortInt{}, SortBool{}}(VarX:SortInt{}, Lblf{}(VarX:SortInt{}))",
                r"\in{SortInt{}, R}(VarX:SortInt{}, Lblf{}(VarX:SortInt{}))",
            ),
        ] {
            assert_eq!(predicate(condition), printed(expected), "{condition}");
        }
    }

    #[test]
    fn predicate_at_rebuilds_a_nested_spine_and_quantified_leaves() {
        let condition = format!(
            r#"\not{{SortBool{{}}}}(\or{{SortBool{{}}}}(\exists{{SortBool{{}}}}(VarY:SortInt{{}}, {A}), \ceil{{SortInt{{}}, SortBool{{}}}}(Lblf{{}}(VarY:SortInt{{}}))))"#
        );
        let expected = format!(
            r#"\not{{R}}(\or{{R}}(\exists{{R}}(VarY:SortInt{{}}, {}), \ceil{{SortInt{{}}, R}}(Lblf{{}}(VarY:SortInt{{}}))))"#,
            leaf_at_r(A)
        );
        assert_eq!(predicate(&condition), printed(&expected));
    }

    /// A connective inside an atom's operand is a set operation on values, not part of the
    /// spine: it is left as written.
    #[test]
    fn predicate_at_leaves_a_connective_inside_an_atom_operand() {
        let operand = format!(r"\or{{SortBool{{}}}}({A}, {B})");
        let condition = format!(
            r#"\equals{{SortBool{{}}, SortBool{{}}}}({operand}, \dv{{SortBool{{}}}}("true"))"#
        );
        let expected =
            format!(r#"\equals{{SortBool{{}}, R}}({operand}, \dv{{SortBool{{}}}}("true"))"#);
        assert_eq!(predicate(&condition), printed(&expected));
    }

    #[test]
    fn equation_sort_parameters_are_declared_but_not_emitted_as_attributes() {
        let mut entries = BTreeMap::new();
        entries.insert(
            "sortParams".into(),
            json!({
                "node": "KSort",
                "name": "#SortParam",
                "params": [
                    { "node": "KSort", "name": "Q0", "params": [] },
                    { "node": "KSort", "name": "Q1", "params": [] }
                ]
            }),
        );
        let attributes = KAttributes::new(entries);
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        let sentence = Sentence::Claim {
            body: truth.clone(),
            requires: truth.clone(),
            ensures: truth,
            attributes: attributes.clone(),
        };
        let valued = valued_attributes(&[&sentence]);
        assert!(!valued.contains("sortParams"));
        assert_eq!(
            emit_attributes(attributes.semantic_entries(), &valued, &BTreeMap::new()),
            Attributes::default()
        );
    }

    #[test]
    fn owise_binds_predicate_sort_variables_from_its_selected_competitors() {
        let parsed = crate::outer::parse(
            "owise-predicate-sorts.k",
            indoc! {r#"
                module MAIN
                  syntax Bool
                  syntax Int ::= "f(" Int ")" [function, total, symbol(f)]
                endmodule
            "#},
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let converter = TermConverter::new(&resolved, "MAIN").unwrap();
        let int = Sort::new("Int");
        let bool_sort = Sort::new("Bool");
        let x = Term::Variable {
            name: "X".into(),
            sort: Some(int.clone()),
        };
        let left = Term::apply("f", vec![x.clone()]);
        let predicate_at = |name| {
            let variable = Sort::with_parameters("#SortParam", vec![Sort::new(name)]);
            Term::Apply {
                label: Label::with_parameters(
                    InternalLabel::Equals.as_str(),
                    vec![variable.clone(), bool_sort.clone()],
                ),
                arguments: vec![
                    Term::Apply {
                        label: Label::with_parameters(
                            InternalLabel::Equals.as_str(),
                            vec![int.clone(), variable.clone()],
                        ),
                        arguments: vec![x.clone(), x.clone()],
                    },
                    Term::Apply {
                        label: Label::with_parameters(InternalLabel::Top.as_str(), vec![variable]),
                        arguments: Vec::new(),
                    },
                ],
            }
        };
        let requires = Term::Apply {
            label: Label::with_parameters(InternalLabel::And.as_str(), vec![bool_sort.clone()]),
            arguments: vec![predicate_at("Q1"), predicate_at("Q2")],
        };
        let unused_requires = predicate_at("Q9");
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        let competitor = |requires| Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(left.clone()),
                right: Box::new(x.clone()),
            },
            requires,
            ensures: truth.clone(),
            attributes: KAttributes::default(),
        };
        let mut cache = OwiseCompetitors {
            scanned: true,
            injected: vec![
                Some((
                    competitor(requires.clone()),
                    injector.sentence_sort_variables([&requires]).unwrap(),
                )),
                Some((
                    competitor(unused_requires.clone()),
                    injector
                        .sentence_sort_variables([&unused_requires])
                        .unwrap(),
                )),
            ],
            by_signature: BTreeMap::from([((Label::new("f"), vec![int]), vec![0])]),
            failure: None,
        };
        let attributes = KAttributes::default();
        let equation = equation_info(&left, &attributes, &catalog)
            .unwrap()
            .unwrap();
        let predicate_sort = KoreSort::Variable("R".into());
        let emitted = emit_owise_equation(
            equation,
            converter.convert(&x).unwrap(),
            Pattern::Top {
                sort: predicate_sort,
            },
            &attributes,
            &BTreeSet::new(),
            &converter,
            &catalog,
            &injector,
            &[],
            &mut cache,
            &SentenceSortVariables::default(),
            &BTreeSet::from(["X".into()]),
            ConditionForm::Predicate,
        )
        .unwrap();
        let KoreSentence::Axiom { parameters, .. } = &emitted else {
            panic!("an owise equation must emit an axiom");
        };
        assert_eq!(parameters, &["R", "Q1", "Q2"]);
        let kore = crate::kore::printer::Printer::pretty(100)
            .print_sentence(&emitted)
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect::<String>();
        assert!(kore.contains("\\equals{SortInt{},Q1}"), "{kore}");
        assert!(kore.contains("\\equals{SortInt{},Q2}"), "{kore}");
        assert!(!kore.contains("Sort'Hash'SortParam"), "{kore}");
    }

    /// A competitor's quantified variables are its free variables: a variable that an `#Exists`
    /// or `#Forall` in its arguments binds already has its binder, so the owise axiom binds only
    /// the free ones, and every binder over a generated variable binds a variable of its body
    /// (K3). The competitor here is `f(#Exists Y . Y) => 0` and `f(#Forall Y . Y) => 0` beside
    /// `f(X) => 1 [owise]`, as structured input or a generated competitor can state it.
    #[test]
    fn owise_quantifies_only_the_free_variables_of_a_competitor() {
        let parsed = crate::outer::parse(
            "owise-binder.k",
            indoc! {r#"
                module MAIN
                  syntax Bool
                  syntax Int ::= "f(" Int ")" [function, total, symbol(f)]
                endmodule
            "#},
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let converter = TermConverter::new(&resolved, "MAIN").unwrap();
        let int = Sort::new("Int");
        let variable = |name: &str| Term::Variable {
            name: name.into(),
            sort: Some(int.clone()),
        };
        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        for quantifier in [InternalLabel::Exists, InternalLabel::Forall] {
            // `f` is unary, so the competitor's free variable is its condition `requires Z`, a
            // Bool variable, and its argument is the quantified `Y . Y`.
            let quantified = Term::Apply {
                label: Label::with_parameters(quantifier.as_str(), vec![int.clone()]),
                arguments: vec![variable("Y"), variable("Y")],
            };
            let competitor_left = Term::apply("f", vec![quantified]);
            let competitor = Sentence::Rule {
                body: Term::Rewrite {
                    left: Box::new(competitor_left),
                    right: Box::new(Term::Token {
                        token: "0".into(),
                        sort: int.clone(),
                    }),
                },
                requires: Term::Variable {
                    name: "Z".into(),
                    sort: Some(Sort::new("Bool")),
                },
                ensures: truth.clone(),
                attributes: KAttributes::default(),
            };
            let mut cache = OwiseCompetitors {
                scanned: true,
                injected: vec![Some((competitor, SentenceSortVariables::default()))],
                by_signature: BTreeMap::from([((Label::new("f"), vec![int.clone()]), vec![0])]),
                failure: None,
            };
            let left = Term::apply("f", vec![variable("X")]);
            let attributes = KAttributes::default();
            let equation = equation_info(&left, &attributes, &catalog)
                .unwrap()
                .unwrap();
            let emitted = emit_owise_equation(
                equation,
                converter.convert(&variable("X")).unwrap(),
                Pattern::Top {
                    sort: KoreSort::Variable("R".into()),
                },
                &attributes,
                &BTreeSet::new(),
                &converter,
                &catalog,
                &injector,
                &[],
                &mut cache,
                &SentenceSortVariables::default(),
                &BTreeSet::from(["X".into()]),
                ConditionForm::Predicate,
            )
            .unwrap();
            let KoreSentence::Axiom { pattern, .. } = &emitted else {
                panic!("an owise equation must emit an axiom");
            };
            let mut binders = Vec::new();
            collect_binders(pattern, &mut binders);
            let kore = crate::kore::printer::Printer::compact().print_sentence(&emitted);
            for (name, binds_free) in &binders {
                assert!(
                    binds_free,
                    "{quantifier:?}: {name} is bound vacuously in {kore}"
                );
            }
            // One binder for `Z`, a variable of the competitor's condition alone, which the
            // condition binds as the competitor's own axiom does, under its own name, and the
            // argument's quantifier, which keeps its authored `Y`.
            let generated = binders
                .iter()
                .filter(|(name, _)| name.starts_with("Var'Unds'Gen"))
                .count();
            assert_eq!((binders.len(), generated), (2, 0), "{quantifier:?}: {kore}");
            assert!(
                kore.contains(
                    "\\exists{R}(VarZ:SortBool{}, \\equals{SortBool{}, R}(VarZ:SortBool{}"
                ),
                "{quantifier:?}: {kore}"
            );
        }
    }

    /// The owise axiom of `f(X) => 0 [owise]` beside the one competitor `f(left) => 1 requires
    /// requires`, in a module with the constructor `g(Int, Int)` of sort `Pair` and the function
    /// `h(Int)`, as structured input or a generated competitor can state it.
    fn owise_axiom_beside(left: Term, requires: Term) -> Result<KoreSentence, ModuleToKoreError> {
        let parsed = crate::outer::parse(
            "owise-competitor.k",
            indoc! {r#"
                module MAIN
                  syntax Bool
                  syntax Int ::= r"[0-9]+" [token]
                  syntax Pair ::= "g(" Int "," Int ")" [symbol(g)]
                  syntax Int ::= "f(" Pair ")" [function, total, symbol(f)]
                               | "h(" Int ")" [function, total, symbol(h)]
                endmodule
            "#},
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let converter = TermConverter::new(&resolved, "MAIN").unwrap();
        let pair = Sort::new("Pair");
        let competitor = Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("f", vec![left])),
                right: Box::new(Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                }),
            },
            requires,
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: KAttributes::default(),
        };
        let mut cache = OwiseCompetitors {
            scanned: true,
            injected: vec![Some((competitor, SentenceSortVariables::default()))],
            by_signature: BTreeMap::from([((Label::new("f"), vec![pair.clone()]), vec![0])]),
            failure: None,
        };
        let x = Term::Variable {
            name: "X".into(),
            sort: Some(pair),
        };
        let left = Term::apply("f", vec![x.clone()]);
        let attributes = KAttributes::default();
        let equation = equation_info(&left, &attributes, &catalog)
            .unwrap()
            .unwrap();
        emit_owise_equation(
            equation,
            converter.convert(&x).unwrap(),
            Pattern::Top {
                sort: KoreSort::Variable("R".into()),
            },
            &attributes,
            &BTreeSet::new(),
            &converter,
            &catalog,
            &injector,
            &[],
            &mut cache,
            &SentenceSortVariables::default(),
            &BTreeSet::from(["X".into()]),
            ConditionForm::Predicate,
        )
    }

    fn int_variable(name: &str) -> Term {
        Term::Variable {
            name: name.into(),
            sort: Some(Sort::new("Int")),
        }
    }

    fn quantified(quantifier: InternalLabel, sort: &str, binder: Term, body: Term) -> Term {
        Term::Apply {
            label: Label::with_parameters(quantifier.as_str(), vec![Sort::new(sort)]),
            arguments: vec![binder, body],
        }
    }

    /// `{X #Equals h(Y)}`, a predicate condition at Bool.
    fn x_equals_h(y: &str) -> Term {
        Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Equals.as_str(),
                vec![Sort::new("Int"), Sort::new("Bool")],
            ),
            arguments: vec![int_variable("X"), Term::apply("h", vec![int_variable(y)])],
        }
    }

    /// The number of `\exists` wrapping the first competitor of the owise antecedent
    /// `\not(\or(competitor, ..))`.
    fn outer_binders(pattern: &Pattern) -> usize {
        fn first_or(pattern: &Pattern) -> Option<&Pattern> {
            if let Pattern::Or { arguments, .. } = pattern {
                return arguments.first();
            }
            crate::kore::walk::children(pattern)
                .into_iter()
                .find_map(first_or)
        }
        let mut competitor = first_or(pattern).expect("an owise antecedent has a disjunction");
        let mut count = 0;
        // Invariant: `count` binders wrap `competitor`.
        while let Pattern::Exists { body, .. } = competitor {
            count += 1;
            competitor = body;
        }
        count
    }

    /// Every binder of `pattern`, outermost first along each path, with the binders enclosing it.
    fn binders_with_scope(
        pattern: &Pattern,
        enclosing: &mut Vec<String>,
        binders: &mut Vec<(String, bool, bool)>,
    ) {
        let bound = if let Pattern::Exists { variable, body, .. }
        | Pattern::Forall { variable, body, .. } = pattern
        {
            binders.push((
                variable.name.clone(),
                body.free_variables().contains(variable.as_ref()),
                enclosing.contains(&variable.name),
            ));
            enclosing.push(variable.name.clone());
            true
        } else {
            false
        };
        for child in crate::kore::walk::children(pattern) {
            binders_with_scope(child, enclosing, binders);
        }
        if bound {
            enclosing.pop();
        }
    }

    /// The owise axiom of each competitor shape: it holds each name at one sort, a binder over a
    /// generated name that the competitor does not write binds a variable free in its body (K3),
    /// no binder rebinds a name an
    /// enclosing binder binds, no competitor variable is left free, and the axiom has
    /// `(binders, generated, outer)` binders: `binders` in all, `generated` of them over
    /// generated names (a variable a quantifier of the competitor binds keeps its authored name,
    /// or takes a fresh name with its name as stem where the authored name is in use, so an
    /// authored binder whose variable does not occur in its body stays the author's), and `outer`
    /// of them wrapping the competitor's match and condition, one per free competitor variable (a
    /// free variable bound inside instead is captured). `tests/owise_binders.rs` checks the class
    /// of these shapes through the full compile route.
    #[test]
    fn owise_binds_each_competitor_variable_once_and_captures_none() {
        let y = || int_variable("Y");
        let truth = || Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        let zero = || Term::Token {
            token: "0".into(),
            sort: Sort::new("Int"),
        };
        let g = |left: Term, right: Term| Term::apply("g", vec![left, right]);
        // `{X #Equals h(0)}`, a condition in which the quantified Y does not occur.
        let x_equals_h_zero = || Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Equals.as_str(),
                vec![Sort::new("Int"), Sort::new("Bool")],
            ),
            arguments: vec![int_variable("X"), Term::apply("h", vec![zero()])],
        };
        let g_x_anonymous = || g(int_variable("X"), int_variable("_Gen0"));
        let shapes = [
            (
                "#Exists Y . g(Y, Z)",
                quantified(
                    InternalLabel::Exists,
                    "Pair",
                    y(),
                    g(y(), int_variable("Z")),
                ),
                truth(),
                (2, 1, 1),
            ),
            (
                "#Exists _ . g(_, 0)",
                quantified(
                    InternalLabel::Exists,
                    "Pair",
                    int_variable("_Gen0"),
                    g(int_variable("_Gen1"), zero()),
                ),
                truth(),
                (2, 2, 1),
            ),
            (
                "g(X, _) requires #Forall Y . {X #Equals h(Y)}",
                g_x_anonymous(),
                quantified(InternalLabel::Forall, "Bool", y(), x_equals_h("Y")),
                (3, 2, 2),
            ),
            (
                "g(X, _) requires #Exists Y . {X #Equals h(Y)}",
                g_x_anonymous(),
                quantified(InternalLabel::Exists, "Bool", y(), x_equals_h("Y")),
                (3, 2, 2),
            ),
            (
                "#Exists Y . #Exists W . g(Y, W)",
                quantified(
                    InternalLabel::Exists,
                    "Pair",
                    y(),
                    quantified(
                        InternalLabel::Exists,
                        "Pair",
                        int_variable("W"),
                        g(y(), int_variable("W")),
                    ),
                ),
                truth(),
                (2, 0, 0),
            ),
            // An authored binder whose variable does not occur in its body, in the arguments and
            // in the condition: the binder stays the author's.
            (
                "#Exists Y . g(0, 0)",
                quantified(InternalLabel::Exists, "Pair", y(), g(zero(), zero())),
                truth(),
                (1, 0, 0),
            ),
            (
                "g(X, _) requires #Exists Y . {X #Equals h(0)}",
                g_x_anonymous(),
                quantified(InternalLabel::Exists, "Bool", y(), x_equals_h_zero()),
                (3, 2, 2),
            ),
            (
                "g(X, _) requires #Forall Y . {X #Equals h(0)}",
                g_x_anonymous(),
                quantified(InternalLabel::Forall, "Bool", y(), x_equals_h_zero()),
                (3, 2, 2),
            ),
            // Shadowing both ways: a bound name equal to the owise rule's own variable `X` (at
            // Pair), which the binder must not keep, since one name has one sort in an axiom, and
            // a free competitor variable beside an anonymous binder: the binder `_Gen0` binds
            // nothing, and `_Gen1` is a free competitor variable like `Z`, each refreshed.
            (
                "#Exists X . g(X, Z), X the owise rule's variable",
                quantified(
                    InternalLabel::Exists,
                    "Pair",
                    int_variable("X"),
                    g(int_variable("X"), int_variable("Z")),
                ),
                truth(),
                (2, 1, 1),
            ),
            (
                "#Exists _ . g(_, Z)",
                quantified(
                    InternalLabel::Exists,
                    "Pair",
                    int_variable("_Gen0"),
                    g(int_variable("_Gen1"), int_variable("Z")),
                ),
                truth(),
                (3, 3, 2),
            ),
        ];
        // Every shape is checked, and every problem of every shape reported.
        let mut problems = Vec::new();
        for (shape, left, requires, expected) in shapes {
            // The competitor's own binders, which may bind nothing: a quantifier binds exactly
            // its own variable, so `#Exists _ . g(_, 0)` (`_Gen0` over `g(_Gen1, 0)`) binds none.
            let authored = binding::bound_names(&left)
                .into_iter()
                .chain(binding::bound_names(&requires))
                .map(|name| identifier::encode_variable(&name, VariableKind::Element))
                .collect::<BTreeSet<_>>();
            let emitted = match owise_axiom_beside(left, requires) {
                Ok(emitted) => emitted,
                Err(error) => {
                    problems.push(format!("{shape}: {error}"));
                    continue;
                }
            };
            let kore = crate::kore::printer::Printer::compact().print_sentence(&emitted);
            // The public path refuses an axiom that holds one name at two sorts.
            if let Err(error) = check_variable_sorts(&emitted, &|| "P.o".into()) {
                problems.push(format!("{shape}: {error}"));
            }
            let KoreSentence::Axiom { pattern, .. } = &emitted else {
                panic!("{shape}: an owise equation must emit an axiom");
            };
            let mut binders = Vec::new();
            binders_with_scope(pattern, &mut Vec::new(), &mut binders);
            let is_generated = |name: &str| name.starts_with("Var'Unds'Gen");
            for (name, binds_free, rebinds) in &binders {
                if is_generated(name) && !binds_free && !authored.contains(name) {
                    problems.push(format!("{shape}: {name} is bound vacuously in {kore}"));
                }
                if *rebinds {
                    problems.push(format!(
                        "{shape}: {name} is bound twice on one path in {kore}"
                    ));
                }
            }
            let generated = binders
                .iter()
                .filter(|(name, _, _)| is_generated(name))
                .count();
            let found = (binders.len(), generated, outer_binders(pattern));
            if found != expected {
                problems.push(format!(
                    "{shape}: (binders, generated, outer) {found:?}, expected {expected:?}, in {kore}"
                ));
            }
            if pattern
                .free_variables()
                .iter()
                .any(|variable| is_generated(&variable.name))
            {
                problems.push(format!("{shape}: a competitor variable is free in {kore}"));
            }
        }
        assert!(problems.is_empty(), "{}", problems.join("\n"));
    }

    /// Every `\exists` and `\forall` of `pattern`: its variable's name and whether that variable
    /// occurs free in its body.
    fn collect_binders(pattern: &Pattern, binders: &mut Vec<(String, bool)>) {
        if let Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } =
            pattern
        {
            binders.push((
                variable.name.clone(),
                body.free_variables().contains(variable.as_ref()),
            ));
        }
        for child in crate::kore::walk::children(pattern) {
            collect_binders(child, binders);
        }
    }

    /// An owise equation reads its competitors' conditions itself: a competitor that is not
    /// among the emitted rules (`module_rules` is empty) and whose condition is a mixed equality
    /// is refused by the owise route, which names the competitor.
    #[test]
    fn the_owise_route_refuses_a_competitor_condition_with_a_mixed_equality() {
        let parsed = crate::outer::parse(
            "owise-mixed.k",
            indoc! {r#"
                module MAIN
                  syntax Bool
                  syntax Int ::= "f(" Int ")" [function, total, symbol(f)]
                endmodule
            "#},
        )
        .unwrap();
        let definition = crate::outer::lower(&parsed, "MAIN").unwrap();
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let injector = SortInjector::new(&resolved, "MAIN").unwrap();
        let converter = TermConverter::new(&resolved, "MAIN").unwrap();
        let int = Sort::new("Int");
        let bool_sort = Sort::new("Bool");
        let x = Term::Variable {
            name: "X".into(),
            sort: Some(int.clone()),
        };
        let left = Term::apply("f", vec![x.clone()]);
        let truth = Term::Token {
            token: "true".into(),
            sort: bool_sort.clone(),
        };
        // `{ {X #Equals X} #Equals true }`: a predicate against a Bool term.
        let requires = Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Equals.as_str(),
                vec![bool_sort.clone(), bool_sort.clone()],
            ),
            arguments: vec![
                Term::Apply {
                    label: Label::with_parameters(
                        InternalLabel::Equals.as_str(),
                        vec![int.clone(), bool_sort.clone()],
                    ),
                    arguments: vec![x.clone(), x.clone()],
                },
                truth.clone(),
            ],
        };
        let mut competitor_attributes = KAttributes::default();
        competitor_attributes.insert(AttributeKey::Label.as_str(), json!("MAIN.c"));
        let competitor = Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(left.clone()),
                right: Box::new(x.clone()),
            },
            requires: requires.clone(),
            ensures: truth,
            attributes: competitor_attributes,
        };
        let mut cache = OwiseCompetitors {
            scanned: true,
            injected: vec![Some((
                competitor,
                injector.sentence_sort_variables([&requires]).unwrap(),
            ))],
            by_signature: BTreeMap::from([((Label::new("f"), vec![int]), vec![0])]),
            failure: None,
        };
        let attributes = KAttributes::default();
        let equation = equation_info(&left, &attributes, &catalog)
            .unwrap()
            .unwrap();
        let error = emit_owise_equation(
            equation,
            converter.convert(&x).unwrap(),
            Pattern::Top {
                sort: KoreSort::Variable("R".into()),
            },
            &attributes,
            &BTreeSet::new(),
            &converter,
            &catalog,
            &injector,
            &[],
            &mut cache,
            &SentenceSortVariables::default(),
            &BTreeSet::from(["X".into()]),
            ConditionForm::Predicate,
        )
        .unwrap_err();
        let ModuleToKoreError::MixedConditionEquality { sentence } = &error else {
            panic!("expected a mixed condition equality, got {error}");
        };
        assert_eq!(sentence, "rule [MAIN.c]");
    }

    #[test]
    fn uses_the_builtin_polymorphic_injection_production_for_equations() {
        let definition = KDefinition {
            main_module: "MAIN".into(),
            modules: vec![crate::definition::FlatModule {
                name: "MAIN".into(),
                imports: Vec::new(),
                local_sentences: Vec::new(),
                attributes: KAttributes::default(),
            }],
            attributes: KAttributes::default(),
        };
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let from = Sort::new("Int");
        let to = Sort::new("KItem");
        let left = Term::Apply {
            label: Label::with_parameters("inj", vec![from.clone(), to.clone()]),
            arguments: vec![Term::variable("X")],
        };
        let mut attributes = KAttributes::default();
        attributes.insert("simplification", json!(""));

        let equation = equation_info(&left, &attributes, &productions)
            .unwrap()
            .unwrap();

        assert_eq!(equation.argument_sorts, [from]);
        assert_eq!(equation.result_sort, to);
        assert!(equation.direct);
    }

    #[test]
    fn rejects_axioms_that_use_one_name_at_two_sorts() {
        let generated_top = KoreSort::Application {
            name: "SortGeneratedTopCell".into(),
            arguments: Vec::new(),
        };
        let int = KoreSort::Application {
            name: "SortInt".into(),
            arguments: Vec::new(),
        };
        let k_cell = KoreSort::Application {
            name: "SortKCell".into(),
            arguments: Vec::new(),
        };
        let variable = |sort| Variable {
            kind: VariableKind::Element,
            name: "Var'Unds'Gen0".into(),
            sort,
        };
        let sentence = KoreSentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(Pattern::And {
                sort: generated_top,
                arguments: vec![
                    Pattern::Variable(variable(int)),
                    Pattern::Exists {
                        sort: k_cell.clone(),
                        variable: Box::new(variable(k_cell.clone())),
                        body: Box::new(Pattern::Top { sort: k_cell }),
                    },
                ],
            }),
            attributes: Attributes::default(),
        };

        let error = check_variable_sorts(&sentence, &|| "TEST.collision".into()).unwrap_err();
        assert_eq!(
            error,
            ModuleToKoreError::InconsistentVariableSorts {
                sentence: "TEST.collision".into(),
                name: "Var'Unds'Gen0".into(),
                sorts: vec!["SortInt{}".into(), "SortKCell{}".into()],
            }
        );
        assert_eq!(
            error.to_string(),
            "variable Var'Unds'Gen0 occurs with sorts SortInt{} and SortKCell{} in one axiom (TEST.collision); this can result from an authored sortless variable used at positions of different sorts or from a kompile pass reusing a variable name"
        );
    }

    #[test]
    fn refreshes_same_named_variables_at_distinct_sorts_independently() {
        let term = Term::apply(
            "pair",
            vec![
                Term::Variable {
                    name: "X".into(),
                    sort: Some(Sort::new("A")),
                },
                Term::Variable {
                    name: "X".into(),
                    sort: Some(Sort::new("B")),
                },
            ],
        );
        let refreshed = refresh_variables(
            &term,
            &BinderScope::default(),
            &BTreeMap::new(),
            &mut FreshNames::default(),
            &mut BTreeMap::new(),
        );
        let variables = variable_terms([&refreshed]);

        assert_eq!(
            variables.keys().cloned().collect::<Vec<_>>(),
            ["_Gen0", "_Gen1"]
        );
        assert_eq!(
            variables
                .values()
                .map(|term| match term.unannotated() {
                    Term::Variable { sort, .. } => sort.clone().unwrap(),
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>(),
            [Sort::new("A"), Sort::new("B")]
        );
    }
}
