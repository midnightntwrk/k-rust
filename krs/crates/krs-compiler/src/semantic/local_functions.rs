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
//! So KRS lifts each outermost `let` block of those sentences, and every `k::matches!` wherever
//! it stands, into a function of its own, `f(x1, .., xn)` over the names the construct reads from
//! its sentence, declared in the sentence's module, and writes the application `f(x1, .., xn)`
//! where the construct stood. For a static clause and a claim written beside the definition, that
//! module is the definition's: K takes no syntax declaration in a proof module, so a claim's
//! function cannot be declared beside the claim in the generated `-SPEC` module. (A claim in an
//! author spec module puts its functions there, which no prover takes: finding NT-15-1.) The
//! function is `pub` and `internal`: no program writes it, so it is no program syntax, and a
//! claim's spec module, which imports the definition, sees it.
//!
//! The equations' parameters are names, so they apply to every argument, and each construct's
//! meaning is stated in a definition's sentence, where the tools lower it as in a rule:
//! - a block `C` has the one equation `f(X1, .., Xn) => C`, whose result has `C`'s value wherever
//!   `C` has one, and none elsewhere: an irrefutable `let` (its pattern a name, or a record of
//!   names of a sort with one constructor) has a value for every argument, the body's; a
//!   refutable one has none where the value does not match the pattern;
//! - a test `k::matches!(t, P)` has two: `f(X1, .., Xn) => true requires t matches P`, and
//!   `f(X1, .., Xn) => false requires not (t matches P)`, so the function is `true` where the
//!   subject matches and `false` elsewhere. Its pattern stays a pattern, in a condition, where
//!   `name @ pattern` means what it means in any condition; in a result K takes no `#as`. A test
//!   inside a lifted block is lifted first, on its own, for that reason. The `false` equation
//!   states its condition rather than taking `owise`, which KRS emits as `priority(200)`: K's
//!   Haskell backend reads a priority as an order, and applies the lower equation to a symbolic
//!   argument whose match against the higher one's pattern it cannot establish, so `false`
//!   would hold where the test is undetermined.
//!
//! The function's name, `krsLocal_<digest>`, is a digest of its identity, which is derived from
//! the sentence's own identity and the construct's place among the sentence's lifted
//! constructs ([`krs_ir::local_function_ids`]): the same sentence gets the same names in every
//! run, and two sentences never share one.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ExplicitSymbol, GrammarProductionItem,
    NodeOrigin, ProductionAttribute, ProductionFieldId, RustVisibility, SemanticId, SentenceKind,
    SourceMapKey,
};
use krs_ir_levels::{
    IrRuleCondition, IrTermKind, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef,
    SemanticTerm, SemanticVariable,
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

    /// `term` with each outermost `let` block and every `k::matches!` in it replaced by its lifted
    /// function's application.
    fn term(&mut self, term: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        match term.kind() {
            IrTermKind::Matches { .. } => self.lift_test(term),
            IrTermKind::Let { .. } => {
                let block = map_children(term, &mut |child| self.tests(child))?;
                self.lift_block(&block)
            }
            _ => map_children(term, &mut |child| self.term(child)),
        }
    }

    /// `term` with every `k::matches!` in it replaced by its lifted function's application, and
    /// its `let` blocks kept: inside a block that is lifted itself, a block is lowered where the
    /// enclosing one is, but a test's pattern must stay a pattern.
    fn tests(&mut self, term: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        match term.kind() {
            IrTermKind::Matches { .. } => self.lift_test(term),
            _ => map_children(term, &mut |child| self.tests(child)),
        }
    }

    /// The application of the function lifted out of the `let` block `block`, whose one equation
    /// `f(X1, .., Xn) => block` it records.
    fn lift_block(
        &mut self,
        block: &SemanticTerm,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let function = self.function(block)?;
        let body = SemanticTerm::rewrite(
            function.at("~local-function-equation-body"),
            block.sort().clone(),
            function.head("~local-function-head"),
            block.clone(),
        )
        .map_err(|error| shape(&error))?;
        let equation = SemanticRule::new(
            function.at("~local-function-equation"),
            function.ids.equation.clone(),
            SentenceKind::Equation,
            function.variables(),
            body,
        )
        .map_err(|error| shape(&error))?;
        self.equations.push(equation);
        self.declare(&function)
    }

    /// The application of the function lifted out of the test `test`, `k::matches!(t, P)`, whose
    /// two equations it records: `f(X1, .., Xn) => true requires t matches P`, and
    /// `f(X1, .., Xn) => false requires not (t matches P)`. The pattern stays a pattern, in a
    /// condition, where `name @ pattern` means what it means in any condition. The conditions are
    /// each other's negation and the test is total, so exactly one equation applies wherever the
    /// test has a value: neither depends on an order among them, which a prover reading `owise`
    /// as a lower priority would try before it knows the first does not apply.
    fn lift_test(&mut self, test: &SemanticTerm) -> Result<SemanticTerm, DescriptorLoweringError> {
        let function = self.function(test)?;
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let negated = SemanticTerm::application(
            function.at("~local-function-negation"),
            bool_sort.clone(),
            ApplicationRef::Builtin(BuiltinOperation::BoolNot),
            // A copy of the test under keys of its own: a source-map key names one node.
            vec![test.map_origins(&mut |origin| suffixed(origin, "~local-function-negated"))],
        );
        let equation =
            |id: &krs_ir::StableItemId, part: &str, value: &str, condition: SemanticTerm| {
                SemanticRule::new(
                    function.at(&format!("~local-function-{part}")),
                    id.clone(),
                    SentenceKind::Equation,
                    function.variables(),
                    SemanticTerm::rewrite(
                        function.at(&format!("~local-function-{part}-body")),
                        bool_sort.clone(),
                        function.head(&format!("~local-function-{part}-head")),
                        SemanticTerm::token(
                            function.at(&format!("~local-function-{part}-{value}")),
                            bool_sort.clone(),
                            value,
                        )
                        .map_err(|error| shape(&error))?,
                    )
                    .map_err(|error| shape(&error))?,
                )
                .and_then(|rule| {
                    rule.with_requires(Some(
                        IrRuleCondition::new(
                            function.at(&format!("~local-function-{part}-requires")),
                            condition,
                        )
                        .into(),
                    ))
                })
                .map_err(|error| shape(&error))
            };
        let holds = equation(&function.ids.equation, "equation", "true", test.clone())?;
        let otherwise = equation(&function.ids.otherwise, "otherwise", "false", negated)?;
        self.equations.push(holds);
        self.equations.push(otherwise);
        self.declare(&function)
    }

    /// The function lifted out of `construct`, the next of the host's: its identities, and its
    /// parameters, the names `construct` reads outside its patterns, in first-occurrence order.
    fn function(
        &mut self,
        construct: &SemanticTerm,
    ) -> Result<LocalFunction, DescriptorLoweringError> {
        let mut read = Vec::new();
        let mut bound = BTreeSet::new();
        occurrences(construct, &mut read, &mut bound);
        let declared = |name: &SemanticId| {
            self.sorts
                .get(name)
                .map(|sort| SemanticVariable::new(name.clone(), (*sort).clone()))
                .ok_or_else(|| {
                    shape(&format!(
                        "{} reads `{name}`, which it does not declare",
                        self.host.id()
                    ))
                })
        };
        let parameters = read
            .iter()
            .filter(|name| !bound.contains(*name))
            .map(declared)
            .collect::<Result<Vec<_>, _>>()?;
        let bound = bound
            .iter()
            .filter_map(|name| declared(name).ok())
            .collect();
        // A term's sort is a sort, never a sort parameter, which only a production's declaration
        // and its fields name: so is every name's a term reads, and the construct's own.
        if let Some(parameter) = std::iter::once(construct.sort())
            .chain(parameters.iter().map(SemanticVariable::sort))
            .find(|sort| matches!(sort, SemanticSortRef::Parameter(_)))
        {
            return Err(shape(&format!(
                "{} lifts a function of sort parameter {parameter:?}, which no term has",
                self.host.id()
            )));
        }
        let ids = krs_ir::local_function_ids(self.host.id(), self.index)
            .map_err(|error| shape(&error))?;
        self.index += 1;
        Ok(LocalFunction {
            origin: construct.origin().clone(),
            sort: construct.sort().clone(),
            ids,
            parameters,
            bound,
        })
    }

    /// Records `function`'s production, and returns its application where the construct stood.
    fn declare(
        &mut self,
        function: &LocalFunction,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        self.productions.push(production(
            &function.origin,
            &function.sort,
            &function.ids.production,
            &function.parameters,
        )?);
        self.local
            .extend(function.bound.iter().map(|name| name.id().clone()));
        Ok(function.head("~local-function-call"))
    }
}

/// One function lifted out of a construct of a host sentence.
struct LocalFunction {
    /// The construct's origin, which the function's parts extend.
    origin: NodeOrigin,
    /// The construct's sort, the function's result sort.
    sort: SemanticSortRef,
    ids: krs_ir::LocalFunctionIds,
    /// The names the construct reads outside its patterns, in first-occurrence order.
    parameters: Vec<SemanticVariable>,
    /// The names the construct's patterns bind, which only its own equation holds.
    bound: Vec<SemanticVariable>,
}

impl LocalFunction {
    fn at(&self, suffix: &str) -> NodeOrigin {
        suffixed(&self.origin, suffix)
    }

    /// The function's application to its parameters, `f(X1, .., Xn)`.
    fn head(&self, suffix: &str) -> SemanticTerm {
        self.application(suffix, &self.parameters)
    }

    /// The function's application to `arguments`, names of its parameters' sorts.
    fn application(&self, suffix: &str, arguments: &[SemanticVariable]) -> SemanticTerm {
        SemanticTerm::application(
            self.at(suffix),
            self.sort.clone(),
            ApplicationRef::Declared(self.ids.production.clone()),
            arguments
                .iter()
                .enumerate()
                .map(|(position, argument)| {
                    SemanticTerm::variable(
                        self.at(&format!("{suffix}-{position}")),
                        argument.sort().clone(),
                        argument.id().clone(),
                    )
                })
                .collect(),
        )
    }

    /// The binders of the function's equation: its parameters, then its construct's own names.
    fn variables(&self) -> Vec<SemanticVariable> {
        self.parameters.iter().chain(&self.bound).cloned().collect()
    }
}

/// The production of the function lifted out of a construct at `origin` of sort `sort` under
/// `id`, taking `parameters`:
/// `krsLocal_<digest> "(" S1 "," .. ")"`, a function, `pub` and `internal`, whose symbol is its
/// name.
fn production(
    origin: &NodeOrigin,
    sort: &SemanticSortRef,
    id: &krs_ir::StableItemId,
    parameters: &[SemanticVariable],
) -> Result<SemanticProduction, DescriptorLoweringError> {
    let at = |suffix: &str| suffixed(origin, suffix);
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
        sort.clone(),
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
