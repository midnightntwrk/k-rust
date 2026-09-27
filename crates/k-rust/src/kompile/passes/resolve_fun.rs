//! ```toml algorithm
//! id = "kompile.functions.lift"
//! name = "lifting of local functions into generated productions and rules"
//! sites = ["resolve_fun", "resolve_fun_pass", "closure_variables"]
//! variable = "N = traversed term nodes; G = generated sentences; L = local sentences per module; S = visible sentences of a module; P = visible productions; R = sentences of the definition"
//! counters = []
//! no_counter = "local-function lifting has no dedicated counter; the shared pass scaffolding bumps KompileResolveCalls, KompileSentenceCopies and KompilePartialOrdersBuilt, and KompileSentencesTransformed is added once per compile"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N + (L + G) x G) plus one SortInjector::with_views per module, and, in a module where a lambda body applies a partial function, one O(S) pass over its visible rules with O(P) per configuration-context cell level, and one O(R) count of the rule heads of the whole definition per pass"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Lower local `#fun`, `#let`, and K-matching expressions into generated functions.

use crate::provenance::extend_unique_sentences as extend_unique;
use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use crate::definition::{AttributeKey, LabelHead, ModuleId, ProductionCatalog, ResolvedDefinition};
use crate::names::BuiltinSort;
use crate::{
    definition::{Attributes, Definition, ProductionItem, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{GeneratedCell, GeneratedLabel, InternalLabel, Label, Sort, Term},
    kompile::{SortInjectionError, SortInjector, fresh_names::FreshNames},
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveFunError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ResolveFunError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "local function resolution produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ResolveFunError {}

/// Resolve Java's local-function and K-matching constructs.
///
/// Each occurrence gets a definition-wide-unused `#lambda...` label, a generated function
/// production, and one or more defining rules. Variables used only on the pattern RHS become
/// explicit closure arguments. A generated production is declared `total` only when its pattern
/// is a variable and its body is defined for every value of its variables. Generated sentences remain local to the module containing the
/// expression, exactly as in Java's `ResolveFun` module transformer.
pub fn resolve_fun(definition: &Definition) -> Result<Definition, ResolveFunError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_fun_pass,
        Some(GeneratingPass::ResolveFun),
    )
}

pub(crate) fn resolve_fun_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveFunError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveFunError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    let rule_heads = OnceCell::new();
    let mut labels = input
        .definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();

    // Invariant: every module of `output.modules` before `module` has its sentences transformed and its generated lambda productions and rules appended without duplicates, `labels` holds every label name taken so far, and `diagnostics` their errors; each iteration consumes one module.
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let injector = match SortInjector::with_views(&views, module_id) {
            Ok(injector) => injector,
            Err(error) => {
                diagnostics.push(sort_error(error));
                continue;
            }
        };
        let mut resolver = Resolver {
            injector,
            catalog: views.production_catalog(module_id),
            resolved,
            module_id,
            defined_by_equation: OnceCell::new(),
            definition: input.definition,
            rule_heads: &rule_heads,
            total_lambdas: BTreeSet::new(),
            labels: &mut labels,
            productions: Vec::new(),
            rules: Vec::new(),
            diagnostics: &mut diagnostics,
        };
        let mut sentences = Vec::with_capacity(module.local_sentences.len());
        // Invariant: `sentences` holds the transformed form of every sentence of `module.local_sentences` before `sentence`, and `resolver.productions` and `resolver.rules` the lambdas generated from them; each iteration consumes one sentence.
        for sentence in &module.local_sentences {
            let (productions, rules) = (resolver.productions.len(), resolver.rules.len());
            let transformed = resolver.transform_sentence((**sentence).clone());
            // The lambda productions and rules lifted out of a sentence derive from it.
            for generated in resolver.productions[productions..]
                .iter_mut()
                .chain(&mut resolver.rules[rules..])
            {
                generated
                    .attributes_mut()
                    .union_input_addresses(transformed.attributes());
            }
            sentences.push(transformed);
        }
        extend_unique(&mut sentences, resolver.productions);
        extend_unique(&mut sentences, resolver.rules);
        module.local_sentences = sentences.into_iter().map(Arc::new).collect();
    }

    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ResolveFunError { diagnostics })
    }
}

struct Resolver<'a, 'view, 'definition> {
    injector: SortInjector<'view, 'definition>,
    /// The productions visible in the module being transformed, as written.
    catalog: &'view ProductionCatalog<'definition>,
    resolved: &'view ResolvedDefinition,
    module_id: ModuleId,
    /// The partial functions visible in the module that an equation defines on every argument
    /// (`Resolver::functions_defined_by_equation`), computed when a lambda body first needs it.
    defined_by_equation: OnceCell<BTreeSet<String>>,
    /// The whole definition being transformed, every module of it.
    definition: &'view Definition,
    /// The number of rules, lemmas aside, headed by each label anywhere in `definition`
    /// (`rule_heads`), computed once per pass when a lambda body first needs it.
    rule_heads: &'view OnceCell<BTreeMap<String, usize>>,
    /// The lambdas generated in this module so far whose production is declared `total`.
    total_lambdas: BTreeSet<String>,
    labels: &'a mut BTreeSet<String>,
    productions: Vec<Sentence>,
    rules: Vec<Sentence>,
    diagnostics: &'a mut Vec<Diagnostic>,
}

impl Resolver<'_, '_, '_> {
    fn transform_sentence(&mut self, sentence: Sentence) -> Sentence {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Sentence::Rule {
                body: self.transform(body),
                requires: self.transform(requires),
                ensures: self.transform(ensures),
                attributes,
            },
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Sentence::Context {
                body: self.transform(body),
                requires: self.transform(requires),
                attributes,
            },
            Sentence::ContextAlias {
                body,
                requires,
                attributes,
            } => Sentence::ContextAlias {
                body: self.transform(body),
                requires: self.transform(requires),
                attributes,
            },
            sentence => sentence,
        }
    }

    fn transform(&mut self, term: Term) -> Term {
        if let Some((label, arguments)) = special_application(&term) {
            return self.resolve_application(label, arguments, Attributes::default());
        }
        match term {
            Term::Annotated { term, metadata } => self.transform(*term).with_metadata(metadata),
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.transform(*left)),
                right: Box::new(self.transform(*right)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.transform(*pattern)),
                alias: Box::new(self.transform(*alias)),
            },
            Term::Sequence(items) => {
                Term::Sequence(items.into_iter().map(|item| self.transform(item)).collect())
            }
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.transform(argument))
                    .collect(),
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        }
    }

    fn resolve_application(
        &mut self,
        source_label: Label,
        arguments: Vec<Term>,
        attributes: Attributes,
    ) -> Term {
        let (body, argument) = match (InternalLabel::of(&source_label.name), arguments.as_slice()) {
            (Some(InternalLabel::Fun3), [left, right, argument]) => (
                Term::Rewrite {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                argument.clone(),
            ),
            (Some(InternalLabel::Let), [left, argument, right]) => (
                Term::Rewrite {
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                argument.clone(),
            ),
            (_, [body, argument]) => (body.clone(), argument.clone()),
            _ => {
                self.diagnostics.push(Diagnostic::error_at(
                    DiagnosticCode::InvalidLocalFunction,
                    format!(
                        "{} has invalid arity {}; expected {}",
                        source_label.name,
                        arguments.len(),
                        if [InternalLabel::Fun3, InternalLabel::Let]
                            .iter()
                            .any(|internal| source_label.is(*internal))
                        {
                            3
                        } else {
                            2
                        }
                    ),
                    &attributes,
                ));
                return Term::Apply {
                    label: source_label,
                    arguments,
                };
            }
        };

        let hint1 = underlying_variable(&argument)
            .map(|(name, _)| name)
            .unwrap_or_default();
        let hint2 = match body.unannotated() {
            Term::Apply { label, .. } => label.name.clone(),
            _ => String::new(),
        };
        let lambda = self.unique_lambda(&hint1, &hint2);
        let left = rewrite_left(&body);
        let right = rewrite_right(&body);
        let lhs_sort = self.term_sort(&left, &attributes);
        let argument_sort = self.term_sort(&argument, &attributes);
        // Java treats an uncast variable pattern as the unknown `K` sort in this LUB, regardless
        // of the concrete argument sort.
        let variable_pattern = underlying_variable(&left).is_some();
        let parameter_sort = match (lhs_sort, argument_sort) {
            _ if matches!(left.unannotated(), Term::Variable { .. }) => {
                Sort::builtin(BuiltinSort::K)
            }
            (Some(lhs), Some(argument)) => self
                .injector
                .least_upper_bound(&[lhs.clone(), argument.clone()], None)
                .unwrap_or_else(|_| common_k_sort(&lhs, &argument)),
            _ => Sort::builtin(BuiltinSort::K),
        };
        let closure = closure_variables(&body);
        let predicate = [InternalLabel::KEqualsK, InternalLabel::KNotEqualsK]
            .iter()
            .any(|internal| source_label.is(*internal));

        // A lambda has no value on an argument its pattern does not match, so only a `#fun` or
        // `#let` whose pattern is a variable can be total; whether the value it binds to every
        // argument is defined is decided from the generated equation's right-hand side below.
        let covering = [InternalLabel::Fun2, InternalLabel::Fun3, InternalLabel::Let]
            .iter()
            .any(|internal| source_label.is(*internal))
            && variable_pattern;
        let result_sort = if predicate {
            Sort::builtin(BuiltinSort::Bool)
        } else {
            self.term_sort(&right, &attributes)
                .unwrap_or_else(|| Sort::builtin(BuiltinSort::K))
        };
        // The production keeps its place before the lambdas nested in its body; it is declared
        // total once the body is known to be defined.
        let production = self.productions.len();
        self.productions.push(lambda_production(
            &lambda,
            &closure,
            parameter_sort.clone(),
            result_sort,
        ));

        if predicate {
            let positive = self.lambda_rule(
                &lambda,
                &body,
                &body,
                attributes.clone(),
                LambdaResult::Constant(bool_token(true)),
            );
            self.rules.push(positive);
            let owise_pattern = Term::Apply {
                label: Label::semantic_cast(&parameter_sort),
                arguments: vec![Term::variable("#Owise")],
            };
            let mut owise = attributes.clone();
            owise.mark(AttributeKey::Owise);
            let negative = self.lambda_rule(
                &lambda,
                &owise_pattern,
                &body,
                owise,
                LambdaResult::Constant(bool_token(false)),
            );
            self.rules.push(negative);
        } else {
            let rule = self.lambda_rule(
                &lambda,
                &body,
                &body,
                attributes,
                LambdaResult::PatternRight,
            );
            if covering && self.equation_right_is_defined(&rule) {
                self.productions[production]
                    .attributes_mut()
                    .mark(AttributeKey::Total);
                self.total_lambdas.insert(lambda.name.clone());
            }
            self.rules.push(rule);
        }

        let mut call_arguments = vec![self.transform(argument)];
        call_arguments.extend(closure.into_iter().map(|variable| variable.term()));
        let call = Term::Apply {
            label: lambda,
            arguments: call_arguments,
        };
        if source_label.is(InternalLabel::KNotEqualsK) {
            Term::apply("notBool_", vec![call])
        } else {
            call
        }
    }

    fn lambda_rule(
        &mut self,
        lambda: &Label,
        pattern: &Term,
        closure_source: &Term,
        attributes: Attributes,
        result: LambdaResult,
    ) -> Sentence {
        let resolved = self.transform(pattern.clone());
        let with_anonymous = resolve_anonymous(resolved);
        let closure = closure_variables(closure_source);
        let mut arguments = vec![rewrite_left(&with_anonymous)];
        arguments.extend(closure.into_iter().map(|variable| variable.term()));
        let right = match result {
            LambdaResult::PatternRight => rewrite_right(&with_anonymous),
            LambdaResult::Constant(term) => term,
        };
        let body = rename_fresh_constants(Term::Rewrite {
            left: Box::new(Term::Apply {
                label: lambda.clone(),
                arguments,
            }),
            right: Box::new(right),
        });
        Sentence::Rule {
            body,
            requires: bool_token(true),
            ensures: bool_token(true),
            attributes,
        }
    }

    /// Whether the right-hand side of the generated equation `rule` is defined for every value of
    /// its variables.
    ///
    /// `total` on a function symbol states that each of its applications denotes exactly one
    /// value. The lambda's only equation equates its application with the body, so the claim is
    /// consistent exactly when the body denotes one value wherever the equation applies; a body
    /// that is undefined for some argument (`10 /Int Y` at `Y = 0`) would make the claim say that
    /// the application both is and is not defined there. This is a sufficient syntactic test: the
    /// body is built from variables, tokens, K sequences and applications of symbols that denote
    /// one value on defined arguments.
    fn equation_right_is_defined(&self, rule: &Sentence) -> bool {
        let Sentence::Rule { body, .. } = rule else {
            return false;
        };
        let Term::Rewrite { right, .. } = body.unannotated() else {
            return false;
        };
        self.is_defined(right, Knowledge::Equations)
    }

    fn is_defined(&self, term: &Term, knowledge: Knowledge) -> bool {
        match term.unannotated() {
            Term::Variable { .. } | Term::Token { .. } | Term::InjectedLabel(_) => true,
            Term::Sequence(items) => items.iter().all(|item| self.is_defined(item, knowledge)),
            Term::Apply { label, arguments } => {
                self.label_is_defined(label, knowledge)
                    && arguments.iter().all(|a| self.is_defined(a, knowledge))
            }
            Term::Rewrite { .. } | Term::As { .. } => false,
            Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
        }
    }

    /// Whether every application of `label` to defined arguments denotes one value in the
    /// compiled definition.
    ///
    /// - A semantic cast is not a symbol: it is erased to its argument, and the sort check it
    ///   implies becomes a condition of the equation, which only restricts where it applies.
    /// - A lambda generated earlier in this module is defined when it was declared `total`.
    /// - Any other compiler-internal label (the matching-logic connectives, `#Bottom` among
    ///   them) is not known to be defined.
    /// - A written label is defined when every production that declares it is a constructor or
    ///   a `total` function, which is the claim the compiled symbol carries; a macro-like
    ///   production is excluded because its application is replaced by the macro's right-hand
    ///   side after this pass, and a label with no visible production yet (a sort projection or
    ///   predicate generated later) is not known to be defined.
    /// - With `Knowledge::Equations`, a partial function is also defined when one of its
    ///   equations defines it on every argument (`functions_defined_by_equation`).
    fn label_is_defined(&self, label: &Label, knowledge: Knowledge) -> bool {
        match label.generated() {
            Some(GeneratedLabel::SemanticCast { .. }) => return true,
            Some(GeneratedLabel::Lambda { .. }) => {
                return knowledge == Knowledge::Equations
                    && self.total_lambdas.contains(&label.name);
            }
            Some(_) => return false,
            None => {}
        }
        if InternalLabel::of(&label.name).is_some() {
            return false;
        }
        let productions = self.catalog.productions_for(&LabelHead::from(label));
        let declared = !productions.is_empty()
            && productions.iter().all(|id| {
                let attributes = self.catalog.production(*id).attributes();
                (!attributes.has(AttributeKey::Function) || attributes.has(AttributeKey::Total))
                    && !attributes.has_any(&AttributeKey::MACRO_LIKE)
                    && !attributes.has(AttributeKey::MlOp)
            });
        declared
            || knowledge == Knowledge::Equations
                && self
                    .defined_by_equation
                    .get_or_init(|| self.functions_defined_by_equation())
                    .contains(&label.name)
    }

    /// The partial functions visible in this module that their equation defines on every
    /// argument.
    ///
    /// When `f`'s only rule is an equation `f(X1, .., Xn) => R` with no condition, pairwise
    /// distinct variables each of the sort `f`'s only production declares at its position, and a
    /// right-hand side defined by declared attributes alone, the compiled definition has the
    /// axiom `f(X1, .., Xn) = R` for all values of the `Xi`; since `R` denotes one value, so does
    /// every application of `f`. A second rule headed by `f` anywhere in the definition, lemmas
    /// aside, could take priority over it or restrict it, so `f` then does not count. The right-hand side is judged without
    /// this set, so no function's definedness rests on its own or another derived function's
    /// equations, and recursion needs no termination argument. An equation the backend applies
    /// only in some cases, or that is not a defining axiom, does not count: `owise`, `priority`,
    /// `concrete`, `symbolic`, `simplification`, `anywhere`. An equation that also inspects the
    /// configuration (`[[ .. ]] <c> V </c>`) counts only when that pattern matches every
    /// configuration (`Resolver::cell_covers`).
    fn functions_defined_by_equation(&self) -> BTreeSet<String> {
        const RESTRICTING: [AttributeKey; 6] = [
            AttributeKey::Owise,
            AttributeKey::Priority,
            AttributeKey::Concrete,
            AttributeKey::Symbolic,
            AttributeKey::Simplification,
            AttributeKey::Anywhere,
        ];
        let mut candidates = BTreeSet::new();
        // Invariant: `candidates` holds the labels whose covering, unconditional equation with a declared-defined right-hand side is among the visible sentences before `sentence`; each iteration consumes one sentence.
        for sentence in self.resolved.sentences(self.module_id) {
            let Some((context, left, right)) = defining_rule(sentence) else {
                continue;
            };
            let Sentence::Rule {
                requires,
                ensures,
                attributes,
                ..
            } = sentence
            else {
                continue;
            };
            let Term::Apply { label, arguments } = left.unannotated() else {
                continue;
            };
            if !is_true(requires) || !is_true(ensures) || attributes.has_any(&RESTRICTING) {
                continue;
            }
            // `[[ f(..) => R ]] <c> V </c>`: the equation also matches the configuration, which
            // is a pattern over every configuration exactly when `self.cell_covers` says so.
            if context.is_some_and(|cell| !self.cell_covers(cell)) {
                continue;
            }
            let [production] = self.catalog.productions_for(&LabelHead::from(label)) else {
                continue;
            };
            let Sentence::Production {
                items, attributes, ..
            } = self.catalog.production(*production)
            else {
                continue;
            };
            if !attributes.has(AttributeKey::Function)
                || attributes.has(AttributeKey::Total)
                || attributes.has_any(&AttributeKey::MACRO_LIKE)
            {
                continue;
            }
            let parameter_sorts = items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            });
            if parameter_sorts.clone().count() != arguments.len() {
                continue;
            }
            let mut names = BTreeSet::new();
            let covering = arguments
                .iter()
                .zip(parameter_sorts)
                .all(|(argument, sort)| {
                    covering_variable(argument, sort)
                        .is_some_and(|name| is_anonymous(name) || names.insert(name.to_owned()))
                });
            if covering && self.is_defined(right, Knowledge::Declared) {
                candidates.insert(label.name.clone());
            }
        }
        // A second rule of `f` anywhere in the definition, even one this module cannot see, is
        // an axiom of the compiled definition that may take priority over the candidate or
        // restrict it.
        let heads = self.rule_heads.get_or_init(|| rule_heads(self.definition));
        candidates.retain(|label| heads.get(label) == Some(&1));
        candidates
    }

    fn term_sort(&mut self, term: &Term, attributes: &Attributes) -> Option<Sort> {
        match self.injector.term_sort(term, None) {
            Ok(sort) => Some(sort),
            Err(error) => {
                self.diagnostics.push(Diagnostic::error_at(
                    DiagnosticCode::InvalidLocalFunction,
                    format!("Could not compute sort of local-function term: {error}"),
                    attributes,
                ));
                None
            }
        }
    }

    fn unique_lambda(&mut self, hint1: &str, hint2: &str) -> Label {
        let mut attempt = 0usize;
        // Invariant: every lambda label for `hint1` and `hint2` with a suffix tried so far is already in `self.labels`, and `attempt` counts those attempts; each iteration tries a new suffix, so the finite `self.labels` bounds the loop to `self.labels.len() + 1` iterations.
        loop {
            let suffix = if attempt == 0 {
                String::new()
            } else {
                (attempt + 1).to_string()
            };
            let name = Label::lambda(hint1, hint2, &suffix).name;
            if self.labels.insert(name.clone()) {
                return Label::new(name);
            }
            attempt += 1;
        }
    }
}

impl Resolver<'_, '_, '_> {
    /// Whether the configuration context `cell` of a `[[ .. ]]` equation matches every
    /// configuration: it is one cell `<c> V </c>` without dots whose content `V` is a variable of
    /// the cell's content sort, and `c` and each cell enclosing it up to `<generatedTop>` occur
    /// exactly once in every configuration. A cell with a multiplicity or an optional cell is
    /// absent from some configurations, so it does not cover them.
    fn cell_covers(&self, cell: &Term) -> bool {
        let Term::Apply { label, arguments } = cell.unannotated() else {
            return false;
        };
        let [before, content, after] = arguments.as_slice() else {
            return false;
        };
        let no_dots = |term: &Term| {
            matches!(term.unannotated(), Term::Apply { label, arguments }
                if label.is(InternalLabel::NoDots) && arguments.is_empty())
        };
        if !no_dots(before) || !no_dots(after) {
            return false;
        }
        let Some((sort, contents)) = self.single_cell(&label.name) else {
            return false;
        };
        let [content_sort] = contents.as_slice() else {
            return false;
        };
        if covering_variable(content, content_sort).is_none() {
            return false;
        }
        let mut sort = sort.clone();
        let mut name = label.name.clone();
        // Invariant: the cell `name` of sort `sort` and every cell below it on the path to the context cell occur exactly once in every configuration of their parent; each iteration moves to the parent, and a chain longer than the number of productions has repeated a cell, so the bound rejects it.
        for _ in 0..=self.catalog.len() {
            if name == GeneratedCell::Top.label() {
                return true;
            }
            let parents = self
                .catalog
                .productions()
                .filter(|(_, production)| {
                    production.attributes().has(AttributeKey::Cell)
                        && matches!(production, Sentence::Production { items, .. }
                            if items.iter().any(|item| matches!(item,
                                ProductionItem::NonTerminal { sort: item_sort, .. }
                                    if *item_sort == sort)))
                })
                .collect::<Vec<_>>();
            let [
                (
                    _,
                    Sentence::Production {
                        label: Some(parent),
                        ..
                    },
                ),
            ] = parents.as_slice()
            else {
                return false;
            };
            let Some((parent_sort, _)) = self.single_cell(&parent.name) else {
                return false;
            };
            sort = parent_sort.clone();
            name = parent.name.clone();
        }
        false
    }

    /// The result sort and the content sorts of the only production of cell `name`, when that
    /// cell occurs exactly once in its parent (no multiplicity, not optional).
    fn single_cell(&self, name: &str) -> Option<(&Sort, Vec<&Sort>)> {
        let [production] = self.catalog.productions_for(&LabelHead::new(name)) else {
            return None;
        };
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = self.catalog.production(*production)
        else {
            return None;
        };
        if !attributes.has(AttributeKey::Cell)
            || (attributes.has(AttributeKey::Multiplicity)
                && attributes.string(AttributeKey::Multiplicity) != Some("1"))
            || attributes.has(AttributeKey::CellOptAbsent)
        {
            return None;
        }
        let contents = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            })
            .collect();
        Some((sort, contents))
    }
}

/// What `Resolver::is_defined` may use to know that an application is defined.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Knowledge {
    /// Only the attributes the productions declare.
    Declared,
    /// Also the total lambdas generated so far and the functions an equation defines everywhere.
    Equations,
}

enum LambdaResult {
    PatternRight,
    Constant(Term),
}

fn special_application(term: &Term) -> Option<(Label, Vec<Term>)> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return None;
    };
    [
        InternalLabel::Fun2,
        InternalLabel::Fun3,
        InternalLabel::Let,
        InternalLabel::KEqualsK,
        InternalLabel::KNotEqualsK,
    ]
    .iter()
    .any(|internal| label.is(*internal))
    .then(|| (label.clone(), arguments.clone()))
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ClosureVariable {
    name: String,
    sort: Option<Sort>,
}

impl ClosureVariable {
    fn term(self) -> Term {
        Term::Variable {
            name: self.name,
            sort: self.sort,
        }
    }
}

fn closure_variables(term: &Term) -> Vec<ClosureVariable> {
    // Java's closure pass is rewrite-aware: every variable occurring in an LHS anywhere in
    // the body (including nested local-function patterns) is bound.  A flat walk over the RHS
    // would otherwise mistake an inner lambda's parameter for an outer closure variable.
    // RewriteAwareVisitor starts a body with isLHS and isRHS both set, so a body without a
    // rewrite (the pattern of a K-matching predicate) binds every variable it mentions.
    let mut bound = BTreeSet::new();
    collect_lhs_variables(term, true, &mut bound);
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    collect_rhs_variables(term, None, Position::BODY, &mut |variable| {
        if variable.name != "THIS_CONFIGURATION"
            && !variable.name.starts_with('?')
            && !bound.contains(&variable.name)
            && seen.insert(variable.name.clone())
        {
            result.push(variable);
        }
    });
    result
}

// Invariant: `bound` holds every non-anonymous variable visited so far with `in_lhs` set, which holds on rewrite left sides and on the first argument of `Fun3` and `Let` applications; each call recurses into the immediate subterms of `term`.
fn collect_lhs_variables(term: &Term, in_lhs: bool, bound: &mut BTreeSet<String>) {
    match term.unannotated() {
        Term::Variable { name, .. } if in_lhs && !is_anonymous(name) => {
            bound.insert(name.clone());
        }
        Term::Variable { .. } => {}
        Term::Apply { label, arguments }
            if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                && arguments.len() == 1 =>
        {
            collect_lhs_variables(&arguments[0], in_lhs, bound);
        }
        Term::Rewrite { left, right } => {
            collect_lhs_variables(left, true, bound);
            collect_lhs_variables(right, false, bound);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun3) && arguments.len() >= 3 =>
        {
            collect_lhs_variables(&arguments[0], true, bound);
            collect_lhs_variables(&arguments[1], false, bound);
            collect_lhs_variables(&arguments[2], in_lhs, bound);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Let) && arguments.len() >= 3 =>
        {
            collect_lhs_variables(&arguments[0], true, bound);
            collect_lhs_variables(&arguments[1], in_lhs, bound);
            collect_lhs_variables(&arguments[2], false, bound);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun2) && arguments.len() >= 2 =>
        {
            collect_lhs_variables(&arguments[0], false, bound);
            collect_lhs_variables(&arguments[1], in_lhs, bound);
        }
        Term::As { pattern, alias } => {
            collect_lhs_variables(pattern, in_lhs, bound);
            collect_lhs_variables(alias, in_lhs, bound);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_lhs_variables(item, in_lhs, bound);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

/// The rewrite-aware position of `ComputeUnboundVariables`: `lhs`/`rhs` follow
/// `RewriteAwareVisitor` (both set outside any rewrite, one of them inside) and `matching_lhs`
/// is its `isInKLhs`, set for the left child of `:=K` and `:/=K` because a matching pattern
/// binds its own variables (the generated predicate rule matches them) instead of closing over
/// them.
#[derive(Clone, Copy)]
struct Position {
    lhs: bool,
    rhs: bool,
    matching_lhs: bool,
}

impl Position {
    const BODY: Self = Self {
        lhs: true,
        rhs: true,
        matching_lhs: false,
    };

    fn left(self) -> Self {
        Self {
            lhs: true,
            rhs: false,
            ..self
        }
    }

    fn right(self) -> Self {
        Self {
            lhs: false,
            rhs: true,
            ..self
        }
    }

    fn matching_pattern(self) -> Self {
        Self {
            matching_lhs: true,
            ..self
        }
    }

    /// `ComputeUnboundVariables.apply(KVariable)`: a variable in RHS position outside a matching
    /// pattern is unbound unless it is an anonymous variable that is also in LHS position.
    fn reports(self, name: &str) -> bool {
        self.rhs && !self.matching_lhs && !(is_anonymous(name) && self.lhs)
    }
}

// Invariant: `visitor` has received every variable visited so far for which `position.reports` holds, with the sort of its nearest enclosing semantic cast when there is one; each call recurses into the immediate subterms of `term`, updating `position` at rewrites and at `Fun3`, `Fun2`, `Let`, and equality applications.
fn collect_rhs_variables(
    term: &Term,
    context: Option<&Sort>,
    position: Position,
    visitor: &mut impl FnMut(ClosureVariable),
) {
    let term = term.unannotated();
    // A unary semantic cast sets the context sort for its argument. It is tested before the
    // `match` because binding the cast's sort text in a match guard needs `if let` guards, which
    // the declared minimum Rust version does not have. Only `Apply` arms could also take such a
    // term, and the cast was already tested before every one of them, so behaviour is unchanged.
    if let Term::Apply { label, arguments } = term
        && let Some(GeneratedLabel::SemanticCast { sort_text }) = label.generated()
        && arguments.len() == 1
    {
        // The cast's sort text is kept as a sort name, as before this vocabulary existed.
        let sort = Sort::new(sort_text);
        collect_rhs_variables(&arguments[0], Some(&sort), position, visitor);
        return;
    }
    match term {
        Term::Variable { name, sort } if position.reports(name) => visitor(ClosureVariable {
            name: name.clone(),
            sort: context.cloned().or_else(|| sort.clone()),
        }),
        Term::Variable { .. } => {}
        Term::Rewrite { left, right } => {
            collect_rhs_variables(left, context, position.left(), visitor);
            collect_rhs_variables(right, context, position.right(), visitor);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun3) && arguments.len() >= 3 =>
        {
            collect_rhs_variables(&arguments[0], context, position.left(), visitor);
            collect_rhs_variables(&arguments[1], context, position.right(), visitor);
            collect_rhs_variables(&arguments[2], context, position, visitor);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Let) && arguments.len() >= 3 =>
        {
            collect_rhs_variables(&arguments[0], context, position.left(), visitor);
            collect_rhs_variables(&arguments[1], context, position, visitor);
            collect_rhs_variables(&arguments[2], context, position.right(), visitor);
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun2) && arguments.len() >= 2 =>
        {
            collect_rhs_variables(&arguments[0], context, position.right(), visitor);
            collect_rhs_variables(&arguments[1], context, position, visitor);
        }
        Term::Apply { label, arguments }
            if [InternalLabel::KEqualsK, InternalLabel::KNotEqualsK]
                .iter()
                .any(|internal| label.is(*internal))
                && arguments.len() == 2 =>
        {
            collect_rhs_variables(&arguments[0], context, position.matching_pattern(), visitor);
            collect_rhs_variables(&arguments[1], context, position, visitor);
        }
        Term::As { pattern, alias } => {
            collect_rhs_variables(pattern, context, position, visitor);
            collect_rhs_variables(alias, context, position, visitor);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                collect_rhs_variables(item, context, position, visitor);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn lambda_production(
    lambda: &Label,
    closure: &[ClosureVariable],
    argument: Sort,
    result: Sort,
) -> Sentence {
    let mut items = vec![
        ProductionItem::Terminal(lambda.name.clone()),
        ProductionItem::Terminal("(".into()),
        ProductionItem::NonTerminal {
            sort: argument,
            name: None,
        },
    ];
    for variable in closure {
        items.push(ProductionItem::Terminal(",".into()));
        items.push(ProductionItem::NonTerminal {
            sort: variable
                .sort
                .clone()
                .unwrap_or_else(|| Sort::builtin(BuiltinSort::K)),
            name: None,
        });
    }
    items.push(ProductionItem::Terminal(")".into()));
    let mut attributes = Attributes::default();
    attributes.mark(AttributeKey::Function);
    Sentence::Production {
        label: Some(lambda.clone()),
        parameters: Vec::new(),
        sort: result,
        items,
        attributes,
    }
}

fn underlying_variable(term: &Term) -> Option<(String, Option<Sort>)> {
    match term.unannotated() {
        Term::Variable { name, sort } => Some((name.clone(), sort.clone())),
        Term::Apply { label, arguments }
            if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                && arguments.len() == 1 =>
        {
            underlying_variable(&arguments[0])
        }
        _ => None,
    }
}

fn rewrite_left(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { left, .. } => (**left).clone(),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_left).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_left).collect()),
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_left(pattern)),
            alias: alias.clone(),
        },
        term => term.clone(),
    }
}

fn rewrite_right(term: &Term) -> Term {
    match term.unannotated() {
        Term::Rewrite { right, .. } => rewrite_right(right),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments.iter().map(rewrite_right).collect(),
        },
        Term::Sequence(items) => Term::Sequence(items.iter().map(rewrite_right).collect()),
        Term::As { alias, .. } => (**alias).clone(),
        term => term.clone(),
    }
}

fn resolve_anonymous(term: Term) -> Term {
    fn transform(term: Term, fresh: &mut FreshNames) -> Term {
        match term {
            Term::Annotated { term, metadata } => transform(*term, fresh).with_metadata(metadata),
            Term::Variable { name, sort } if is_anonymous(&name) => {
                let prefix = name.strip_suffix('_').unwrap_or_default();
                Term::Variable {
                    name: fresh.mint(&format!("{prefix}_Gen")),
                    sort,
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(transform(*left, fresh)),
                right: Box::new(transform(*right, fresh)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(transform(*pattern, fresh)),
                alias: Box::new(transform(*alias, fresh)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform(item, fresh))
                    .collect(),
            ),
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform(argument, fresh))
                    .collect(),
            },
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
        }
    }
    let mut fresh = FreshNames::for_terms([&term]);
    transform(term, &mut fresh)
}

fn rename_fresh_constants(term: Term) -> Term {
    match term {
        Term::Annotated { term, metadata } => rename_fresh_constants(*term).with_metadata(metadata),
        Term::Variable { name, sort } if name.starts_with('!') => Term::Variable {
            name: format!("#_{}", &name[1..]),
            sort,
        },
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rename_fresh_constants(*left)),
            right: Box::new(rename_fresh_constants(*right)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rename_fresh_constants(*pattern)),
            alias: Box::new(rename_fresh_constants(*alias)),
        },
        Term::Sequence(items) => {
            Term::Sequence(items.into_iter().map(rename_fresh_constants).collect())
        }
        Term::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(rename_fresh_constants).collect(),
        },
        leaf @ (Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }) => leaf,
    }
}

fn common_k_sort(left: &Sort, right: &Sort) -> Sort {
    if left == right {
        left.clone()
    } else if left.name == BuiltinSort::K.k_name() || right.name == BuiltinSort::K.k_name() {
        Sort::builtin(BuiltinSort::K)
    } else {
        Sort::builtin(BuiltinSort::KItem)
    }
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

/// A rule's configuration context, left-hand side and right-hand side when it is not a lemma and
/// its body is a rewrite at the top, possibly under `[[ .. ]]`.
fn defining_rule(sentence: &Sentence) -> Option<(Option<&Term>, &Term, &Term)> {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return None;
    };
    if attributes.has(AttributeKey::Simplification) {
        return None;
    }
    let (context, equation) = match body.unannotated() {
        Term::Apply { label, arguments } if label.is(InternalLabel::WithConfig) => {
            match arguments.as_slice() {
                [equation, cell] => (Some(cell), equation),
                _ => return None,
            }
        }
        _ => (None, body),
    };
    match equation.unannotated() {
        Term::Rewrite { left, right } => Some((context, &**left, &**right)),
        _ => None,
    }
}

/// The number of rules, lemmas aside, whose left-hand side is headed by each label, over every
/// module of `definition`.
fn rule_heads(definition: &Definition) -> BTreeMap<String, usize> {
    let mut heads = BTreeMap::new();
    // Invariant: `heads` counts the non-lemma rules headed by each label among the modules and sentences before the current one; each iteration consumes one sentence.
    for sentence in definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        if let Some((_, left, _)) = defining_rule(sentence)
            && let Term::Apply { label, .. } = left.unannotated()
        {
            *heads.entry(label.name.clone()).or_default() += 1;
        }
    }
    heads
}

/// The name of the variable `argument` binds when it matches every value of `sort`: a variable
/// of that sort or of no sort, possibly under a semantic cast to exactly `sort`, whose sort check
/// holds for every value of `sort`.
fn covering_variable<'a>(argument: &'a Term, sort: &Sort) -> Option<&'a str> {
    match argument.unannotated() {
        Term::Variable {
            name,
            sort: variable_sort,
        } if variable_sort
            .as_ref()
            .is_none_or(|variable| variable == sort) =>
        {
            Some(name)
        }
        Term::Apply { label, arguments } if label.semantic_cast_sort().as_ref() == Some(sort) => {
            match arguments.as_slice() {
                [inner] => covering_variable(inner, sort),
                _ => None,
            }
        }
        _ => None,
    }
}

fn is_true(term: &Term) -> bool {
    matches!(term.unannotated(), Term::Token { token, sort }
        if token == "true" && *sort == Sort::builtin(BuiltinSort::Bool))
}

fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn sort_error(error: SortInjectionError) -> Diagnostic {
    plain_error(error.to_string())
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidLocalFunction,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}
