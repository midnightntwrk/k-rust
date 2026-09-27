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

use super::*;
use k_rust_kore::measure::{self, Counter};

pub(super) struct RuleEmissionContext<'a, 'definition> {
    pub valued: &'a BTreeSet<String>,
    pub productions: &'a ProductionCatalog<'definition>,
    pub injector: &'a SortInjector<'definition, 'definition>,
    pub converter: &'a TermConverter<'definition, 'definition>,
    pub module_rules: &'a [Sentence],
    pub default_reachability: Option<ReachabilityMode>,
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
    } = context;
    let injected = injector.inject_sentence(sentence)?;
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
        _ => unreachable!("only rules and claims are emitted"),
    };
    let body_sort = injector.term_sort(body, None)?;
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
        );
    }
    if is_macro_rule(&injected) {
        if !existentials.is_empty() {
            return Err(ModuleToKoreError::EquationExistentials {
                variables: existential_names(right, ensures),
            });
        }
        return emit_macro_axiom(left, right, attributes, valued, injector, converter);
    }
    if !claim && !body_sort.is_builtin(BuiltinSort::GeneratedTopCell) {
        return Err(ModuleToKoreError::ExpectedGeneratedTopCell {
            actual: body_sort,
            rule: body.to_string(),
        });
    }
    let result_sort = encode_kore_sort(&body_sort);
    let left = converter.convert(left)?;
    let right = converter.convert(right)?;
    let requires = side_condition(requires, &result_sort, converter)?;
    let ensures = side_condition(ensures, &result_sort, converter)?;
    // `concrete` and `symbolic` carry lists of free variables, not string
    // values.  For rewrite rules and claims K resolves those names against
    // the left-hand side and its requires condition only (variables that are
    // introduced by the right-hand side/ensures are not in scope).
    let attribute_pattern = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![left.clone(), requires.clone()],
    };
    let attribute_overrides = variable_list_attribute_overrides(attributes, &attribute_pattern)?;
    let mut right = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![right, ensures],
    };
    for variable in existentials.into_iter().rev() {
        right = Pattern::Exists {
            sort: result_sort.clone(),
            variable: Box::new(variable),
            body: Box::new(right),
        };
    }
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
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes,
        }
    } else {
        KoreSentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes,
        }
    })
}

fn emit_macro_axiom(
    left: &Term,
    right: &Term,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    injector: &SortInjector<'_, '_>,
    converter: &TermConverter<'_, '_>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = equation_parameters(attributes);
    let converter = converter.with_sort_variables(parameters.iter().skip(1).cloned());
    let result_sort = converter.convert_sort(&injector.term_sort(left, None)?);
    let pattern = Pattern::Equals {
        operand_sort: Box::new(result_sort),
        result_sort: KoreSort::Variable("R".into()),
        left: Box::new(converter.convert(left)?),
        right: Box::new(converter.convert(right)?),
    };
    let mut attributes = attributes.clone();
    let priority = attributes
        .value(AttributeKey::Priority)
        .map(|value| attribute_value_string(AttributeKey::Priority.as_str(), value))
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| {
            if attributes.has(AttributeKey::Owise) {
                "200".into()
            } else {
                "50".into()
            }
        });
    attributes.set(AttributeKey::Priority, Value::String(priority));
    equation_sentence(false, pattern, &attributes, valued, parameters)
}

#[derive(Clone, Debug)]
struct EquationInfo<'a> {
    label: &'a Label,
    children: &'a [Term],
    argument_sorts: Vec<Sort>,
    result_sort: Sort,
    direct: bool,
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
    // Java's ModuleToKORE supplies a synthetic polymorphic production for `inj`; it is part of
    // the KORE prelude rather than the compiled K module's production catalog.
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
        }));
    }
    let production = resolve_equation_production(application, label, productions)?;
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
    }))
}

pub(super) fn resolve_equation_production<'a>(
    application: &Term,
    label: &Label,
    productions: &'a ProductionCatalog<'a>,
) -> Result<&'a Sentence, ModuleToKoreError> {
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
        return Ok(production);
    }
    let candidates = productions.productions_for(&LabelHead::from(label));
    match candidates {
        [] => Err(ModuleToKoreError::MissingEquationProduction {
            label: label.name.clone(),
        }),
        [id] => Ok(productions.production(*id)),
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
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = equation_parameters(attributes);
    let converter = converter.with_sort_variables(parameters.iter().skip(1).cloned());
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort);
    let avoid_variables = variable_names([left, requires]);
    let requires = side_condition(requires, &predicate_sort, &converter)?;
    let ensures = side_condition(ensures, &result_sort, &converter)?;
    let right = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![converter.convert(right)?, ensures],
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
            &converter,
            productions,
            injector,
            module_rules,
            owise_competitors,
            parameters,
            &avoid_variables,
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
            .map(|(index, sort)| Variable {
                kind: VariableKind::Element,
                name: format!("X{index}"),
                sort: converter.convert_sort(sort),
            })
            .collect::<Vec<_>>();
        let application = Pattern::Application {
            symbol: converter.convert_label(equation.label),
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
                        operand_sort: Box::new(converter.convert_sort(sort)),
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
    parameters: Vec<String>,
    avoid_variables: &BTreeSet<String>,
) -> Result<KoreSentence, ModuleToKoreError> {
    // O1: bind one fresh KORE variable per argument and match the equation's own children.
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort);
    let variables = equation_variables(&equation, converter);
    let own_matches = equation_matches(
        &variables,
        equation.children,
        &equation.argument_sorts,
        &predicate_sort,
        converter,
    )?;

    // O2: reserve caller variables and allocate the per-module injection cache lazily.
    let mut fresh = FreshNames::default();
    // Invariant: `fresh` has reserved every name of `avoid_variables` before `name`; each name is visited once.
    for name in avoid_variables {
        fresh.reserve(name.clone());
    }
    // O3: visit each executable same-signature competitor once in rule-catalog order.
    owise_competitors.scan_once(module_rules, injector, productions);
    let (candidates, failure) = owise_competitors.candidates(&equation);
    let mut competitors = Vec::new();
    // Invariant: `competitors` contains exactly the accepted rules before `index`, each with
    // refreshed variables.
    for &index in candidates {
        measure::bump(Counter::KompileOwiseCompetitorScans);
        let Some(Sentence::Rule {
            body,
            requires: competitor_requires,
            ..
        }) = &owise_competitors.injected[index]
        else {
            unreachable!("indexed competitors are injected rules")
        };
        let competitor_left = match body.unannotated() {
            Term::Rewrite { left, .. } => left.as_ref(),
            _ => body,
        };
        let mut renames = BTreeMap::new();
        let refreshed_left = refresh_variables(competitor_left, &mut fresh, &mut renames);
        let refreshed_requires = refresh_variables(competitor_requires, &mut fresh, &mut renames);
        let Term::Apply {
            arguments: competitor_children,
            ..
        } = peel_alias(&refreshed_left).unannotated()
        else {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "non-application function competitor for owise".into(),
            });
        };
        let condition = side_condition(&refreshed_requires, &predicate_sort, converter)?;
        let matches = equation_matches(
            &variables,
            competitor_children,
            &equation.argument_sorts,
            &predicate_sort,
            converter,
        )?;
        let mut candidate = Pattern::And {
            sort: predicate_sort.clone(),
            arguments: vec![condition, matches],
        };
        let mut quantified = variable_terms([&refreshed_left, &refreshed_requires])
            .into_values()
            .collect::<Vec<_>>();
        quantified.sort_by(|left, right| {
            let key = |term: &Term| match term.unannotated() {
                Term::Variable { name, sort } => (sort.clone(), name.clone()),
                _ => unreachable!("variable_terms returns variables"),
            };
            key(left).cmp(&key(right))
        });
        // Invariant: `candidate` is wrapped in one existential per variable of `quantified` after `term`, so after the reverse traversal the first sorted variable is the outermost binder; each iteration consumes one variable.
        for term in quantified.into_iter().rev() {
            let Some(variable) = take_kore_variable(converter.convert(&term)?) else {
                unreachable!("collected terms are variables")
            };
            candidate = Pattern::Exists {
                sort: predicate_sort.clone(),
                variable: Box::new(variable),
                body: Box::new(candidate),
            };
        }
        competitors.push(candidate);
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
        symbol: converter.convert_label(equation.label),
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
    injected: Vec<Option<Sentence>>,
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
            let injected = match injector.inject_sentence(sentence) {
                Ok(injected) => injected,
                Err(error) => {
                    self.failure = Some(error.into());
                    return;
                }
            };
            let Sentence::Rule { body, .. } = &injected else {
                continue;
            };
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
            self.injected[index] = Some(injected);
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
) -> Vec<Variable> {
    equation
        .argument_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| Variable {
            kind: VariableKind::Element,
            name: format!("X{index}"),
            sort: converter.convert_sort(sort),
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
                    operand_sort: Box::new(converter.convert_sort(sort)),
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

// Invariant: each call rebuilds one node of `term` and recurses only into its direct subterms, so the finite `term` bounds the calls; `renames` maps every (name, sort) identity met so far to the one `_Gen` name `fresh` minted for it.
fn refresh_variables(
    term: &Term,
    fresh: &mut FreshNames,
    renames: &mut BTreeMap<(String, Option<Sort>), String>,
) -> Term {
    let refreshed = match term.unannotated() {
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
            left: Box::new(refresh_variables(left, fresh, renames)),
            right: Box::new(refresh_variables(right, fresh, renames)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(refresh_variables(pattern, fresh, renames)),
            alias: Box::new(refresh_variables(alias, fresh, renames)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| refresh_variables(item, fresh, renames))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| refresh_variables(argument, fresh, renames))
                .collect(),
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
        _ => return Ok(()),
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

fn equation_parameters(attributes: &KAttributes) -> Vec<String> {
    let mut parameters = vec!["R".into()];
    let Some(sort_parameters) = attributes
        .value(AttributeKey::SortParams)
        .and_then(Value::as_object)
        .and_then(|sort| sort.get("params"))
        .and_then(Value::as_array)
    else {
        return parameters;
    };
    parameters.extend(sort_parameters.iter().filter_map(|sort| {
        sort.as_object()
            .and_then(|sort| sort.get("name"))
            .and_then(Value::as_str)
            .map(str::to_owned)
    }));
    parameters
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

fn side_condition(
    condition: &Term,
    result_sort: &KoreSort,
    converter: &TermConverter<'_, '_>,
) -> Result<Pattern, TermConversionError> {
    if is_true(condition) {
        return Ok(Pattern::Top {
            sort: result_sort.clone(),
        });
    }
    let bool_sort = encode_kore_sort(&Sort::builtin(BuiltinSort::Bool));
    Ok(Pattern::Equals {
        operand_sort: Box::new(bool_sort.clone()),
        result_sort: result_sort.clone(),
        left: Box::new(converter.convert(condition)?),
        right: Box::new(Pattern::DomainValue {
            sort: bool_sort,
            value: "true".into(),
        }),
    })
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

fn existential_variables(
    right: &Term,
    ensures: &Term,
    converter: &TermConverter<'_, '_>,
) -> Result<Vec<Variable>, TermConversionError> {
    let mut terms = BTreeMap::<String, Term>::new();
    // Invariant: `terms` maps every `?`-prefixed variable name in the roots already traversed (`right`, then `ensures`) to its first preorder occurrence; each root is traversed once.
    for root in [right, ensures] {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated()
                && name.starts_with('?')
            {
                terms.entry(name.clone()).or_insert_with(|| term.clone());
            }
        });
    }
    terms
        .into_values()
        .map(|term| match take_kore_variable(converter.convert(&term)?) {
            Some(variable) => Ok(variable),
            None => unreachable!("collected terms are variables"),
        })
        .collect()
}

fn existential_names(right: &Term, ensures: &Term) -> Vec<String> {
    let mut names = BTreeSet::new();
    // Invariant: `names` holds every `?`-prefixed variable name in the roots already traversed (`right`, then `ensures`); each root is traversed once.
    for root in [right, ensures] {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated()
                && name.starts_with('?')
            {
                names.insert(name.clone());
            }
        });
    }
    names.into_iter().collect()
}

#[cfg(test)]
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
        assert_eq!(equation_parameters(&attributes), ["R", "Q0", "Q1"]);

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
        let refreshed = refresh_variables(&term, &mut FreshNames::default(), &mut BTreeMap::new());
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
