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
//! bound = "O(N + (L + G) x G) plus one SortInjector::with_views per module, and, in a module where a lambda body applies a partial function, one O(S) pass over its visible rules with O(P) per configuration-context cell level, and one O(R) count of the rule heads of the whole definition per pass, and one main-module equation judgement in O(P + R + sum of right-hand-side sizes + overload elements squared)"
//! ```
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Lower local `#fun`, `#let`, and K-matching expressions into generated functions.
//!
//! `#let P = E #in B` is lowered exactly as `#fun(P => B)(E)`: the generated function's equation
//! is `P => B`, and `E` is the argument of its application, evaluated in the enclosing term and
//! outside the scope of `P`, so a variable of `E` is never bound by `P`. The definition check
//! places the arguments of every local function by this lowering
//! (`definition::checks::term_position`), and the closure variables of a generated function come
//! from that same walk (`closure_variables`).
#![deny(clippy::wildcard_enum_match_arm)]

use crate::provenance::extend_unique_sentences as extend_unique;
use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use crate::definition::checks::{FreeVariable, local_function_free_variables};
use crate::definition::head_totality::{self, EquationTotality};
use crate::definition::production_kind::{ProductionKind, Totality};
use crate::definition::totality::TotalityWitness;
use crate::definition::{
    AttributeKey, DefinitionViews, LabelHead, ModuleId, ProductionCatalog, ResolvedDefinition,
};
use crate::names::BuiltinSort;
use crate::{
    definition::{Attributes, Definition, ProductionItem, Sentence},
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{GeneratedCell, GeneratedLabel, InternalLabel, Label, Sort, Term, TermParts},
    kompile::{SortInjectionError, SortInjector, fresh_names::FreshNames},
    provenance::GeneratingPass,
};

/// Evidence that a generated covering lambda's equation results are defined wherever they
/// apply, so every application of the lambda denotes exactly one value.
///
/// Its field is private; the early body judgement and the deferred covering-lambda judgement
/// mint it only after inspecting the equation results.
pub(crate) struct DefinedBody(());

/// A generated lambda's variable pattern covers its parameter sort: every semantic cast on the
/// path to the variable, and any inferred sort recorded on it, equal the computed parameter sort.
/// A narrower sort anywhere on that path restricts the equation and cannot receive this receipt.
/// Only local-function lowering can construct it; later stages still check equation conditions and results.
pub(crate) struct CoveringLambda {
    label: String,
}

impl CoveringLambda {
    pub(crate) fn label(&self) -> &str {
        &self.label
    }

    /// Look up this receipt's own label in the complete main-module equation collection.
    pub(super) fn defined_body(
        &self,
        equations: &super::initializer_totality::DeferredEquations,
        defined: &mut dyn FnMut(&Label) -> bool,
    ) -> Option<DefinedBody> {
        equations
            .lambda_is_defined(self, defined)
            .then_some(DefinedBody(()))
    }
}

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

/// Lower local `#fun`, `#let` and K-matching expressions into generated functions.
///
/// Each occurrence gets a definition-wide-unused `#lambda...` label, a generated function
/// production, and one or more defining rules. Variables used only on the pattern RHS become
/// explicit closure arguments. A generated production is declared `total` only when its pattern
/// is a variable and its body is defined for every value of its variables. Generated sentences remain local to the module containing the
/// expression: the label is unused elsewhere in the definition, so the expression's sentence is
/// the generated function's only user.
pub fn resolve_fun(definition: &Definition) -> Result<Definition, ResolveFunError> {
    super::super::pipeline::run_standalone(
        definition,
        resolve_fun_pass,
        Some(GeneratingPass::ResolveFun),
    )
}

pub(crate) fn resolve_fun_pass(
    input: &super::super::pipeline::PassInput<'_>,
    state: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ResolveFunError> {
    let resolved = input.resolved_raw().map_err(|error| ResolveFunError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let views = resolved.views();
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    let rule_heads = OnceCell::new();
    let totality = OnceCell::new();
    let mut labels = input
        .definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.clone()),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
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
            views: &views,
            module_id,
            defined_by_equation: OnceCell::new(),
            definition: input.definition,
            rule_heads: &rule_heads,
            totality: &totality,
            total_lambdas: BTreeSet::new(),
            covering_lambdas: &mut state.covering_lambdas,
            labels: &mut labels,
            productions: Vec::new(),
            rules: Vec::new(),
            negates_match: false,
            diagnostics: &mut diagnostics,
        };
        // The first sentence of the module whose lowering negates a match, which the module's
        // `BOOL` import is for; it locates the error when the definition has no `BOOL`.
        let mut first_negation = None;
        let mut sentences = Vec::with_capacity(module.local_sentences.len());
        // Invariant: `sentences` holds the transformed form of every sentence of `module.local_sentences` before `sentence`, and `resolver.productions` and `resolver.rules` the lambdas generated from them, and `first_negation` locates the first of them whose lowering negates a match; each iteration consumes one sentence.
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
            if resolver.negates_match && first_negation.is_none() {
                first_negation = Some(Diagnostic::error(
                    DiagnosticCode::InvalidLocalFunction,
                    super::missing_bool_message("A `:/=K` match"),
                    &transformed,
                ));
            }
            sentences.push(transformed);
        }
        extend_unique(&mut sentences, resolver.productions);
        extend_unique(&mut sentences, resolver.rules);
        module.local_sentences = sentences.into_iter().map(Arc::new).collect();
        if let Some(missing_bool) = first_negation
            && !super::import_bool(module, resolved)
        {
            diagnostics.push(missing_bool);
        }
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
    views: &'view DefinitionViews<'definition>,
    module_id: ModuleId,
    /// The partial functions visible in the module that an equation defines on every argument
    /// (`Resolver::functions_defined_by_equation`), computed when a lambda body first needs it.
    defined_by_equation: OnceCell<BTreeSet<String>>,
    /// The whole definition being transformed, every module of it.
    definition: &'view Definition,
    /// The number of rules, lemmas aside, headed by each label anywhere in `definition`
    /// (`rule_heads`), computed once per pass when a lambda body first needs it.
    rule_heads: &'view OnceCell<BTreeMap<String, usize>>,
    /// The main module's equation judgement, built lazily once for this pass.
    totality: &'view OnceCell<Option<EquationTotality>>,
    /// The lambdas generated in this module so far whose production is declared `total`.
    total_lambdas: BTreeSet<String>,
    covering_lambdas: &'a mut Vec<CoveringLambda>,
    labels: &'a mut BTreeSet<String>,
    productions: Vec<Sentence>,
    rules: Vec<Sentence>,
    /// Whether a `:/=K` match of the module has been lowered to a `notBool_` application.
    negates_match: bool,
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
            sentence @ Sentence::SyntaxSort { .. }
            | sentence @ Sentence::SortSynonym { .. }
            | sentence @ Sentence::SyntaxLexical { .. }
            | sentence @ Sentence::Production { .. }
            | sentence @ Sentence::SyntaxAssociativity { .. }
            | sentence @ Sentence::SyntaxPriority { .. }
            | sentence @ Sentence::Claim { .. }
            | sentence @ Sentence::Configuration { .. }
            | sentence @ Sentence::Bubble { .. } => sentence,
        }
    }

    fn transform(&mut self, term: Term) -> Term {
        if let Some((label, arguments)) = special_application(&term) {
            return self.resolve_application(label, arguments, Attributes::default());
        }
        match term.into_parts() {
            TermParts::Annotated { term, metadata } => {
                self.transform(*term).with_metadata(metadata)
            }
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.transform(*left)),
                right: Box::new(self.transform(*right)),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(self.transform(*pattern)),
                alias: Box::new(self.transform(*alias)),
            },
            TermParts::Sequence(items) => {
                Term::Sequence(items.into_iter().map(|item| self.transform(item)).collect())
            }
            TermParts::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.transform(argument))
                    .collect(),
            },
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => Term::from(leaf),
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
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only the listed variants are special here"
        )]
        let hint2 = match body.unannotated() {
            Term::Apply { label, .. } => label.name.clone(),
            _ => String::new(),
        };
        let lambda = self.unique_lambda(&hint1, &hint2);
        let left = rewrite_left(&body);
        let right = rewrite_right(&body);
        let lhs_sort = self.term_sort(&left, &attributes);
        let argument_sort = self.term_sort(&argument, &attributes);
        // An uncast variable pattern matches any term, so the parameter takes `K`, the sort of
        // every term, regardless of the concrete argument sort.
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

        // A lambda has no value on an argument its pattern does not match.
        // A variable pattern covers every argument only when every semantic cast on the path
        // to the variable, and any inferred sort recorded on it, equal the parameter sort.
        // A narrower sort anywhere on that path restricts the generated equation.
        // The generated equation's right-hand side must also denote a defined value.
        let covering = [InternalLabel::Fun2, InternalLabel::Fun3, InternalLabel::Let]
            .iter()
            .any(|internal| source_label.is(*internal))
            && pattern_covers(&left, &parameter_sort);
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
            result_sort.clone(),
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
                attributes.clone(),
                LambdaResult::PatternRight,
            );
            if covering {
                self.covering_lambdas.push(CoveringLambda {
                    label: lambda.name.clone(),
                });
            }
            if covering && let Some(defined) = self.equation_right_is_defined(&rule) {
                self.productions[production]
                    .attributes_mut()
                    .declare_total(TotalityWitness::defined_body(defined));
                self.total_lambdas.insert(lambda.name.clone());
            }
            self.rules.push(rule);
            if !covering {
                // `#let P = E #in B` and `#fun(P => B)(E)` denote `\exists vars(P). (E = P) /\ B`:
                // B under the match of E against P, and nothing when E is no instance of P. The
                // equation above gives the value on P's instances; without an axiom for the
                // other arguments of the parameter sort the definition would leave the lambda's
                // value there unconstrained, an unknown that rewriting can narrow, rather than
                // undefined. This `owise` equation states that it is `\bottom` there. As an
                // `owise` axiom it holds only where the equation above does not apply, so a
                // symbolic or unevaluated argument keeps the application; a covering pattern
                // leaves no argument outside P. (A `#Top` body gives the equation above no term,
                // and the backend refuses such a definition when it loads it.)
                let owise_pattern = Term::Apply {
                    label: Label::semantic_cast(&parameter_sort),
                    arguments: vec![Term::variable("#Owise")],
                };
                let mut refutation = attributes;
                refutation.mark(AttributeKey::Owise);
                refutation.mark(AttributeKey::LambdaRefutation);
                // `#Bottom` is parametric in its sort: the label states the instance, so sort
                // injection places it without a visible `#Bottom` production.
                let bottom = Term::Apply {
                    label: Label::with_parameters(
                        InternalLabel::Bottom.as_str(),
                        vec![result_sort],
                    ),
                    arguments: Vec::new(),
                };
                let refuted = self.lambda_rule(
                    &lambda,
                    &owise_pattern,
                    &body,
                    refutation,
                    LambdaResult::Constant(bottom),
                );
                self.rules.push(refuted);
            }
        }

        let mut call_arguments = vec![self.transform(argument)];
        call_arguments.extend(closure.into_iter().map(|variable| variable.term()));
        let call = Term::Apply {
            label: lambda,
            arguments: call_arguments,
        };
        if source_label.is(InternalLabel::KNotEqualsK) {
            self.negates_match = true;
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
    /// one value on defined arguments, as shown by the module's equation judgement.
    ///
    /// This early judgement mints [`DefinedBody`], the evidence
    /// [`TotalityWitness::defined_body`] requires.
    fn equation_right_is_defined(&self, rule: &Sentence) -> Option<DefinedBody> {
        let Sentence::Rule { body, .. } = rule else {
            return None;
        };
        let Term::Rewrite { right, .. } = body.unannotated() else {
            return None;
        };
        self.is_defined(right, Knowledge::Equations)
            .then_some(DefinedBody(()))
    }

    fn is_defined(&self, term: &Term, knowledge: Knowledge) -> bool {
        head_totality::term_is_defined(term, &mut |label| self.label_is_defined(label, knowledge))
    }

    fn totality(&self) -> Option<&EquationTotality> {
        self.totality
            .get_or_init(|| {
                let main = self.resolved.module_id(&self.definition.main_module)?;
                let overloads = self.views.overloads(main).ok()?;
                Some(EquationTotality::judge(
                    self.views.production_catalog(main),
                    &self.resolved.rule_catalog(main),
                    overloads,
                ))
            })
            .as_ref()
    }

    /// Whether every application of `label` to defined arguments denotes one value in the
    /// compiled definition.
    ///
    /// - A semantic cast is not a symbol: it is erased to its argument, and the sort check it
    ///   implies becomes a condition of the equation, which only restricts where it applies.
    /// - A lambda generated earlier in this module is defined when it was declared `total`.
    /// - Any other compiler-internal label (the matching-logic connectives, `#Bottom` among
    ///   them) is not known to be defined.
    /// - A written label is defined when the main module's equation judgement shows every
    ///   production declaring it total. Macro productions count when their expansions are
    ///   defined, or they have no expansion; labels without productions do not count.
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
        let declared = self.totality().is_some_and(|t| t.label_is_defined(label));
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
    /// right-hand side total by the main module's equation judgement, the compiled definition
    /// has the axiom `f(X1, .., Xn) = R` for all values of the `Xi`; since `R` denotes one value,
    /// so does every application of `f`. A second rule headed by `f` anywhere in the definition,
    /// lemmas aside, could take priority over it or restrict it, so `f` then does not count.
    /// The right-hand side is judged without this set, so no function's definedness rests on
    /// its own or another derived function's equations, and recursion needs no termination
    /// argument. An equation the backend applies only in some cases, or that is not a defining
    /// axiom, does not count: `owise`, `priority`,
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
            let production = self.catalog.production(*production);
            if !matches!(
                ProductionKind::of(production),
                ProductionKind::Function {
                    totality: Totality::Partial,
                    macro_like: false
                }
            ) {
                continue;
            }
            let Sentence::Production { items, .. } = production else {
                continue;
            };
            #[expect(
                clippy::wildcard_enum_match_arm,
                reason = "ProductionItem is syntax; only the listed variants are special here"
            )]
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
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is syntax; only the listed variants are special here"
        )]
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
    /// Symbols total by the main module's equation judgement.
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

/// The closure variables of the local function whose equation is `body`: the variables its body
/// reads from the term enclosing it, once each in the order of their first occurrence, with the
/// sort of the innermost semantic cast around that occurrence or else its own sort.
///
/// They come from the walk the definition check applies to the same construct
/// (`definition::checks::local_function_free_variables`), so the variables a generated equation
/// leaves to the enclosing term are exactly those the check requires that term to bind: a
/// pattern binds in its own body only, a nested local function is a scope of its own, the
/// matching pattern of `:=K` and `:/=K` binds its own variables, and an anonymous variable is
/// read from outside only where it is not also matched.
fn closure_variables(body: &Term) -> Vec<ClosureVariable> {
    let mut seen = BTreeSet::new();
    local_function_free_variables(body)
        .into_iter()
        .filter(|variable| seen.insert(variable.name))
        .map(|FreeVariable { name, sort, cast }| ClosureVariable {
            name: name.to_owned(),
            sort: cast.map(Sort::new).or_else(|| sort.cloned()),
        })
        .collect()
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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

/// Whether the variable pattern `pattern` matches every value of `parameter`: every semantic
/// cast on the path to the variable, and the sort inference recorded on the variable itself,
/// must be exactly `parameter`. A narrower sort anywhere on that path restricts the generated
/// equation to that sort's values, so the lambda has no value elsewhere.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn pattern_covers(pattern: &Term, parameter: &Sort) -> bool {
    match pattern.unannotated() {
        Term::Variable { sort, .. } => sort.as_ref().is_none_or(|sort| sort == parameter),
        Term::Apply { label, arguments } if arguments.len() == 1 => {
            label
                .semantic_cast_sort()
                .is_some_and(|sort| &sort == parameter)
                && pattern_covers(&arguments[0], parameter)
        }
        _ => false,
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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
        match term.into_parts() {
            TermParts::Annotated { term, metadata } => {
                transform(*term, fresh).with_metadata(metadata)
            }
            TermParts::Variable { name, sort } if is_anonymous(&name) => {
                let prefix = name.strip_suffix('_').unwrap_or_default();
                Term::Variable {
                    name: fresh.mint(&format!("{prefix}_Gen")),
                    sort,
                }
            }
            TermParts::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(transform(*left, fresh)),
                right: Box::new(transform(*right, fresh)),
            },
            TermParts::As { pattern, alias } => Term::As {
                pattern: Box::new(transform(*pattern, fresh)),
                alias: Box::new(transform(*alias, fresh)),
            },
            TermParts::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| transform(item, fresh))
                    .collect(),
            ),
            TermParts::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| transform(argument, fresh))
                    .collect(),
            },
            leaf @ (TermParts::InjectedLabel(_)
            | TermParts::Variable { .. }
            | TermParts::Token { .. }) => Term::from(leaf),
        }
    }
    let mut fresh = FreshNames::for_terms([&term]);
    transform(term, &mut fresh)
}

fn rename_fresh_constants(term: Term) -> Term {
    match term.into_parts() {
        TermParts::Annotated { term, metadata } => {
            rename_fresh_constants(*term).with_metadata(metadata)
        }
        TermParts::Variable { name, sort } if name.starts_with('!') => Term::Variable {
            name: format!("#_{}", &name[1..]),
            sort,
        },
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(rename_fresh_constants(*left)),
            right: Box::new(rename_fresh_constants(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(rename_fresh_constants(*pattern)),
            alias: Box::new(rename_fresh_constants(*alias)),
        },
        TermParts::Sequence(items) => {
            Term::Sequence(items.into_iter().map(rename_fresh_constants).collect())
        }
        TermParts::Apply { label, arguments } => Term::Apply {
            label,
            arguments: arguments.into_iter().map(rename_fresh_constants).collect(),
        },
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
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
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
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
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
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

/// The stage on the definition the pipeline gives it ([`crate::kompile::stage_harness`]).
#[cfg(test)]
mod stage_tests {
    use crate::kompile::stage_harness::{labelled, render, rendered_changes, run_to_stage};

    /// A local function is lifted to a generated function whose equation is applied without
    /// the configuration, so it cannot draw a fresh value itself. A `!X` of the enclosing
    /// rewrite rule used in the function body is a closure variable: the rule passes it as an
    /// argument, where the rewrite step that applies the rule allocates it, and the equation
    /// receives it as an ordinary variable.
    #[test]
    fn a_fresh_variable_in_a_local_function_is_passed_in_by_the_enclosing_rule() {
        let run = run_to_stage(
            r#"
module INT
  syntax Int ::= Int "+Int" Int [function, total, symbol(_+Int_), hook(INT.add)]
endmodule
module MAIN
  syntax K
  syntax Int ::= r"[0-9]+" [token]
              | plus(Int, Int) [function, symbol(plus)]
              | freshInt(Int) [function, freshGenerator, symbol(freshInt)]
  syntax KItem ::= "go" [symbol(go)]
  configuration <k> go </k>
  rule <k> go => #fun(Y => plus(Y, !X:Int))(1) ...</k> [label(go)]
endmodule
"#,
            "resolve local functions",
        );
        let rule = r#"rule `<k>`(#noDots(.KList),go(.KList)=>`#lambda__`(#token("1","Int"),!X),#dots(.KList)) requires #token("true","Bool") ensures #token("true","Bool")"#;
        assert_eq!(render(labelled(run.output(), "MAIN", "go")[0]), rule);
        let (mut added, removed) = rendered_changes(&run);
        added.sort();
        let mut expected = [
            rule,
            r#"rule `#lambda__`(#SemanticCastToInt(Y),#_X)=>plus(#SemanticCastToInt(Y),#SemanticCastToInt(#_X)) requires #token("true","Bool") ensures #token("true","Bool")"#,
            "syntax Int ::= #lambda__(Int, Int)",
        ];
        expected.sort_unstable();
        assert_eq!(added, expected);
        assert_eq!(removed.len(), 1, "only the rule is rewritten: {removed:#?}");
    }
}
