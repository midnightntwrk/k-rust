//! Local functions where the tools that read a sentence do not lower them (NT-15).
//!
//! A `let` block denotes the term its body computes under the match of its value against its
//! pattern, and `k::matches!` the Bool that says whether its subject matches its pattern. Each is
//! a function of the names it reads, applied to their values: K writes them `#let P = E #in B` and
//! `P :=K E`, and the tools lower that function into a generated production and its equations
//! only in a definition's sentences. Two sentences hold them where nothing lowers them:
//!
//! - a static clause's result, which a program's expansion writes into the program term before
//!   anything evaluates, so `#let` and `:=K` reach the backend as labels no production declares;
//! - a claim, which neither prover lowers.
//!
//! So KRS lifts each outermost such construct `C` of those sentences into a function of its own,
//! `f(x1, .., xn)` over the names `C` reads from its sentence, declared in the sentence's module
//! (the definition's for a static clause and for a claim written beside the definition, an author
//! spec module's for a claim written there, whose sorts and tokens may be the spec module's own)
//! with the one equation `f(x1, .., xn) = C`, and writes the application `f(x1, .., xn)` where `C`
//! stood. The function is `pub` and `internal`: no program writes it, so it is no program syntax,
//! and a claim's spec module, which imports the definition, sees it.
//!
//! The equation's parameters are names, so it applies to every argument, and its result is `C`
//! itself in a definition's sentence, where the construct means what it means in a rule's result:
//! the application has `C`'s value wherever `C` has one, and none elsewhere. That is the meaning
//! of each construct, with no case of its own here:
//! - an irrefutable `let` (its pattern a name, or a record of names of a sort with one
//!   constructor) has a value for every argument: the body's;
//! - a refutable `let` has none where the value does not match the pattern;
//! - `k::matches!` is `true` where the subject matches and `false` elsewhere.
//!
//! The function's name, `krsLocal_<digest>`, is a digest of its identity, which is derived from
//! the sentence's own identity and the construct's place among the sentence's lifted
//! constructs ([`krs_ir::local_function_ids`]): the same sentence gets the same names in every
//! run, and two sentences never share one.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, ExplicitSymbol, GrammarProductionItem, NodeOrigin, ProductionAttribute,
    ProductionFieldId, RustVisibility, SemanticId, SentenceKind, SourceMapKey,
};
use krs_ir_levels::{
    IrTermKind, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef, SemanticTerm,
    SemanticVariable,
};

use super::error::DescriptorLoweringError;
use super::statics::map_children;

/// The modules with every outermost `let` block and `k::matches!` of a static clause or a claim
/// lifted into a function its module declares (the module documentation).
pub(super) fn lift_local_functions(
    modules: Vec<SemanticModule>,
) -> Result<Vec<SemanticModule>, DescriptorLoweringError> {
    modules.into_iter().map(lift_in_module).collect()
}

/// Whether `rule` holds its local functions where no tool lowers them.
fn is_host(rule: &SemanticRule) -> bool {
    matches!(
        rule.kind(),
        SentenceKind::Alias | SentenceKind::Desugar | SentenceKind::Claim
    )
}

fn lift_in_module(module: SemanticModule) -> Result<SemanticModule, DescriptorLoweringError> {
    if !module.rules().iter().any(holds_local_function) {
        return Ok(module);
    }
    let mut productions = module.productions().to_vec();
    let mut rules = Vec::with_capacity(module.rules().len());
    for rule in module.rules() {
        if !holds_local_function(rule) {
            rules.push(rule.clone());
            continue;
        }
        let mut lifter = Lifter::new(rule);
        let rewritten = rule.try_map_terms(&mut |term| lifter.term(term))?;
        let variables = rule
            .variables()
            .iter()
            .filter(|variable| !lifter.local.contains(variable.id()))
            .cloned()
            .collect();
        rules.push(rewritten.with_variables(variables));
        productions.extend(lifter.productions);
        rules.extend(lifter.equations);
    }
    Ok(module.with_productions(productions).with_rules(rules))
}

/// Whether `rule` is a host whose terms hold a `let` block or `k::matches!`.
fn holds_local_function(rule: &SemanticRule) -> bool {
    if !is_host(rule) {
        return false;
    }
    let mut found = false;
    let _ = rule.try_map_terms(&mut |term| {
        found = found || is_or_holds_local_function(term);
        Ok::<_, std::convert::Infallible>(term.clone())
    });
    found
}

fn is_or_holds_local_function(term: &SemanticTerm) -> bool {
    matches!(
        term.kind(),
        IrTermKind::Let { .. } | IrTermKind::Matches { .. }
    ) || term.children().into_iter().any(is_or_holds_local_function)
}

/// The lifting of one host sentence's local functions, in the order its terms are mapped.
struct Lifter<'r> {
    host: &'r SemanticRule,
    sorts: BTreeMap<&'r SemanticId, &'r SemanticSortRef>,
    /// The next lifted construct's place among the host's.
    index: usize,
    /// The names the lifted constructs bind, which leave the host with them.
    local: BTreeSet<SemanticId>,
    productions: Vec<SemanticProduction>,
    equations: Vec<SemanticRule>,
}

impl<'r> Lifter<'r> {
    fn new(host: &'r SemanticRule) -> Self {
        Self {
            host,
            sorts: host
                .variables()
                .iter()
                .map(|variable| (variable.id(), variable.sort()))
                .collect(),
            index: 0,
            local: BTreeSet::new(),
            productions: Vec::new(),
            equations: Vec::new(),
        }
    }

    /// `term` with each outermost local function in it replaced by its lifted function's
    /// application.
    fn term(&mut self, term: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        match term.kind() {
            IrTermKind::Let { .. } | IrTermKind::Matches { .. } => self.lift(term),
            _ => map_children(term, &mut |child| self.term(child)),
        }
    }

    /// The application of the function lifted out of `construct`, whose production and equation
    /// it records.
    fn lift(&mut self, construct: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        let mut read = Vec::new();
        let mut bound = BTreeSet::new();
        occurrences(construct, &mut read, &mut bound);
        let parameters = read
            .iter()
            .filter(|name| !bound.contains(*name))
            .map(|name| {
                self.sorts
                    .get(name)
                    .map(|sort| SemanticVariable::new(name.clone(), (*sort).clone()))
                    .ok_or_else(|| {
                        DescriptorLoweringError::unsupported_shape(
                            "local function",
                            format!(
                                "{} reads `{name}`, which it does not declare",
                                self.host.id()
                            ),
                        )
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(parameter) = std::iter::once(construct.sort())
            .chain(parameters.iter().map(SemanticVariable::sort))
            .find(|sort| matches!(sort, SemanticSortRef::Parameter(_)))
        {
            return Err(parametric(self.host, construct, parameter));
        }
        let ids = krs_ir::local_function_ids(self.host.id(), self.index)
            .map_err(|error| shape(&error))?;
        self.index += 1;
        let at = |suffix: &str| suffixed(construct.origin(), suffix);
        let production = production(construct, &ids.production, &parameters)?;
        let application = |suffix: &str| {
            SemanticTerm::application(
                at(suffix),
                construct.sort().clone(),
                ApplicationRef::Declared(ids.production.clone()),
                parameters
                    .iter()
                    .enumerate()
                    .map(|(position, parameter)| {
                        SemanticTerm::variable(
                            at(&format!("{suffix}-{position}")),
                            parameter.sort().clone(),
                            parameter.id().clone(),
                        )
                    })
                    .collect(),
            )
        };
        let body = SemanticTerm::rewrite(
            at("~local-function-equation-body"),
            construct.sort().clone(),
            application("~local-function-head"),
            construct.clone(),
        )
        .map_err(|error| shape(&error))?;
        let variables = parameters
            .iter()
            .cloned()
            .chain(bound.iter().filter_map(|name| {
                self.sorts
                    .get(name)
                    .map(|sort| SemanticVariable::new(name.clone(), (*sort).clone()))
            }))
            .collect();
        let equation = SemanticRule::new(
            at("~local-function-equation"),
            ids.equation,
            SentenceKind::Equation,
            variables,
            body,
        )
        .map_err(|error| shape(&error))?;
        self.local.extend(bound);
        self.productions.push(production);
        self.equations.push(equation);
        Ok(application("~local-function-call"))
    }
}

/// The production of the function lifted out of `construct` under `id`, taking `parameters`:
/// `krsLocal_<digest> "(" S1 "," .. ")"`, a function, `pub` and `internal`, whose symbol is its
/// name.
fn production(
    construct: &SemanticTerm,
    id: &krs_ir::StableItemId,
    parameters: &[SemanticVariable],
) -> Result<SemanticProduction, DescriptorLoweringError> {
    let at = |suffix: &str| suffixed(construct.origin(), suffix);
    let symbol = format!(
        "krsLocal_{}",
        crate::lowering::short_hash(&crate::lowering::stable_item_text(id))
    );
    let terminal = |suffix: &str, text: &str| {
        GrammarProductionItem::terminal(at(suffix), text).map_err(|error| shape(&error))
    };
    let mut items = vec![
        terminal("~local-function-name", &symbol)?,
        terminal("~local-function-open", "(")?,
    ];
    for (position, parameter) in parameters.iter().enumerate() {
        if position > 0 {
            items.push(terminal(&format!("~local-function-comma-{position}"), ",")?);
        }
        items.push(GrammarProductionItem::non_terminal(
            at(&format!("~local-function-field-{position}")),
            ProductionFieldId::new(format!("x{position}")).map_err(|error| shape(&error))?,
            parameter.sort().clone(),
        ));
    }
    items.push(terminal("~local-function-close", ")")?);
    SemanticProduction::with_api(
        at("~local-function"),
        id.clone(),
        construct.sort().clone(),
        items,
        vec![
            ProductionAttribute::Function {
                origin: at("~local-function-attribute"),
            },
            ProductionAttribute::Internal {
                origin: at("~local-function-placement"),
            },
        ],
        RustVisibility::Public,
        Some(ExplicitSymbol::new(symbol).map_err(|error| shape(&error))?),
    )
    .map_err(|error| shape(&error))
}

/// An internal error: a lifted function's part that the IR refuses, which KRS built.
fn shape(error: &dyn std::fmt::Display) -> DescriptorLoweringError {
    DescriptorLoweringError::unsupported_shape("local function", error.to_string())
}

/// Collects into `read`, in first-occurrence order, every name `term` reads outside the patterns
/// of its local functions, and into `bound` every name such a pattern binds (its local binders,
/// aliases and wildcards), which only that pattern and its block's body read.
fn occurrences(term: &SemanticTerm, read: &mut Vec<SemanticId>, bound: &mut BTreeSet<SemanticId>) {
    match term.kind() {
        IrTermKind::Variable { variable } => {
            if !read.contains(variable) {
                read.push(variable.clone());
            }
        }
        IrTermKind::Matches {
            subject, pattern, ..
        } => {
            occurrences(subject, read, bound);
            pattern_names(pattern, bound);
        }
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            occurrences(value, read, bound);
            pattern_names(pattern, bound);
            occurrences(body, read, bound);
        }
        _ => {
            for child in term.children() {
                occurrences(child, read, bound);
            }
        }
    }
}

/// Every name `pattern` binds.
fn pattern_names(pattern: &SemanticTerm, bound: &mut BTreeSet<SemanticId>) {
    match pattern.kind() {
        IrTermKind::Variable { variable } => {
            bound.insert(variable.clone());
        }
        IrTermKind::As { alias, .. } => {
            bound.insert(alias.clone());
        }
        _ => {}
    }
    for child in pattern.children() {
        pattern_names(child, bound);
    }
}

/// `origin` under the source-map key `suffix` extends.
fn suffixed(origin: &NodeOrigin, suffix: &str) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(format!("{}{suffix}", origin.key().as_str()))
            .expect("a source-map key extended by a separator-free suffix is a key"),
        origin.origin().clone(),
    )
}

/// The refusal of `construct` in `host`, whose lifted function would take or give `parameter`, a
/// sort parameter's sort.
fn parametric(
    host: &SemanticRule,
    construct: &SemanticTerm,
    parameter: &SemanticSortRef,
) -> DescriptorLoweringError {
    let parameter = match parameter {
        SemanticSortRef::Parameter(parameter) => parameter.as_str().to_owned(),
        _ => String::new(),
    };
    let what = match construct.kind() {
        IrTermKind::Matches { .. } => "`k::matches!`",
        _ => "a `let` block",
    };
    let reason = format!(
        "{what} in {} is lifted into a function of the names it reads, and this one reads or computes a term of sort parameter `{parameter}`, which no lifted function takes: write the term without it, or move it into a fn whose sorts are the instance's",
        host_description(host)
    );
    let item = Box::new(host.id().clone());
    let range = construct
        .origin()
        .origin()
        .exact_authored_range()
        .map(Box::new);
    match construct.kind() {
        IrTermKind::Matches { .. } => DescriptorLoweringError::InvalidMatches {
            item,
            reason,
            range,
        },
        _ => DescriptorLoweringError::InvalidLet {
            item,
            reason,
            range,
        },
    }
}

fn host_description(host: &SemanticRule) -> String {
    let what = match host.kind() {
        SentenceKind::Alias => "the result of alias clause",
        SentenceKind::Desugar => "the result of desugar clause",
        _ => "claim",
    };
    format!("{what} `{}`", host.id().item_name())
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_sentence_s_lifted_functions_are_named_by_its_identity_and_their_place() {
        let host = krs_ir::testing::item("claims", "loads", krs_ir::ItemKind::Claim);
        let first = krs_ir::local_function_ids(&host, 0).unwrap();
        assert_eq!(first, krs_ir::local_function_ids(&host, 0).unwrap());
        let second = krs_ir::local_function_ids(&host, 1).unwrap();
        assert_ne!(first.production, second.production);
        assert_ne!(first.production, first.equation);
        let other = krs_ir::testing::item("claims", "stores", krs_ir::ItemKind::Claim);
        assert_ne!(
            first.production,
            krs_ir::local_function_ids(&other, 0).unwrap().production
        );
        assert!(first.production.is_generated_production());
        assert_eq!(first.equation.item_kind(), krs_ir::ItemKind::Equation);
    }
}
