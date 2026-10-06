//! ```toml algorithm
//! id = "kompile.macros.expand"
//! name = "macro expansion by indexed structural matching"
//! sites = ["expand_macros", "expand_macros_pass", "Expander::expand_sentence", "Expander::expand_term", "Expander::expand_known", "Expander::expand_chain", "Expander::expand_arguments", "Expander::instantiate", "Expander::substitute", "Expander::record_rewrite", "Expander::expand_site", "Expander::expand_at", "Expander::try_rules", "Expander::try_rules_once", "Expander::new", "Chain::repeats"]
//! variable = "N = sentence term nodes, on the largest intermediate sentence for the typed mode; R = macro rules under the head label; A = macro applications; V = sentences visible in the macro module; Q = macro rules in the module; h = sentence term height; W = macro rewrites made in the sentence, at most MAX_RECURSIVE_REWRITES of them by macro-rec and alias-rec rules; S = nodes of the largest rewrite result; P = nodes of the largest macro rule right side; U = nodes of the largest rewrite result that are copies of bindings not settled (holding an application or token some macro rule has as its head); T = one SentenceTyper::typing of a sentence (kompile.sort_injections.insert)"
//! counters = ["KompileMacroApplications", "KompileMacroExpansionVisits"]
//!
//! [[cost]]
//! mode = "one sentence, no macro rule with a parametric head"
//! bound = "O((N + W x (P + U)) x R + W x S)"
//!
//! [[cost]]
//! mode = "one sentence, some macro rule with a parametric head (typed in place)"
//! bound = "O((W + 1) x (N x (h + R) + T))"
//!
//! [[cost]]
//! mode = "Expander construction per module"
//! bound = "O(V + Q log Q) plus the forced module views; with a parametric macro head, plus two SentenceTyper constructions and one typing per macro rule"
//! ```
//!
//! With a macro rule whose head production has sort parameters, a sentence is expanded in place (`Expander::expand_site`): an application's instance is read from the typing of the sentence as it stands, which is recomputed at most once per rewrite, and every failed application whose rule set has a head fixing a sort parameter is retried after a rewriting round until a round rewrites nothing.
//! A round without a rewrite ends the retries, so there are at most W + 1 rounds and W + 1 typings; each round and each re-expansion of a substituted result clones and compares subterms along paths of length at most h.
//!
//! An application is rewritten at its root in a loop (`Expander::expand_chain`, `Expander::try_rules`) until no rule applies, so a long chain of root rewrites takes no native stack.
//! Without a parametric head, the result of a rewrite is expanded except where it copies a binding that the expansion of the subject's arguments found settled (`Known`): such a copy is kept as it is, so a rewrite visits (`KompileMacroExpansionVisits`) the nodes of the right side and the copies of unsettled bindings, O(P + U).
//! The bindings are moved out of the rewritten subject into the result (`Expander::instantiate`), and copied only for the other occurrences of a variable used more than once; what stays O(S) per rewrite is measuring the depths of the bindings of a `macro-rec` or `alias-rec` rewrite, from which the subject's and the result's depths follow (`instance_depth`), and a repeat check, which compares subjects only of equal depth.
//! Only `macro-rec` and `alias-rec` rules may apply again on a path, so only their rewrites can make expansion diverge; `Expander::record_rewrite` accounts for those alone and reports, at the macro rule, a chain that returns to a subject it already rewrote (`Chain::repeats`, Brent's cycle finding), more than `MAX_RECURSIVE_REWRITES` recursive rewrites in one sentence, and a path whose recursive rewrites have added more depth than `growth_allowance` (the larger of `MIN_RECURSIVE_GROWTH` and the input's depth).
//! The expansion of a sentence or standalone term, and each level of its recursion, runs with a stack red zone in proportion to the deepest term it may hold (`stack_zone`), on a heap-grown segment when the thread's stack runs low (`with_stack`).
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Expand compile-time macro and alias rules by structural matching.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::DEFAULT_RULE_PRIORITY;

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, DefinitionViews, LabelHead, ModuleId, ProductionCatalog,
        ResolvedDefinition, Sentence, SortCatalog,
        checks::{self, check_functions_with_internal_labels},
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    inner::ParsedProgram,
    kast::{Label, Sort, Term, TermParts},
    kompile::{
        SentenceTyper, SentenceTyping, SortInjector,
        fresh_names::{FreshNames, GeneratedVariableIdentity},
    },
    provenance::GeneratingPass,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpandMacrosError {
    pub diagnostics: Vec<Diagnostic>,
}

impl fmt::Display for ExpandMacrosError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "macro expansion produced {} errors",
            self.diagnostics.len()
        )
    }
}

impl std::error::Error for ExpandMacrosError {}

#[derive(Clone)]
struct MacroRule {
    id: usize,
    sentence: Sentence,
    left: Term,
    right: Term,
    recursive: bool,
    /// The instance of a parametric head, one entry per sort parameter of its production, as
    /// the typing of the macro rule gives it; `None` in an entry the rule leaves open, and `None`
    /// altogether for a head whose production has no sort parameter.
    head_instance: Option<Vec<Option<Sort>>>,
}

/// Apply Java's forward `ExpandMacros` sentence transformation.
///
/// ```compile_fail,E0432
/// use k_rust::definition::checks::check_smt_lemmas; // 6e56f086: validated before expansion
/// ```
///
/// ```
/// use k_rust::definition::checks::check_sorts;
/// ```
pub fn expand_macros(definition: &Definition) -> Result<Definition, ExpandMacrosError> {
    // Recording the origins of the expanded sentences compares them with the input
    // recursively, so the whole pass runs with stack for the deepest sentence.
    with_stack(stack_zone(definition_depth(definition)), || {
        super::super::pipeline::run_standalone(
            definition,
            expand_macros_pass,
            Some(GeneratingPass::MacroExpansion),
        )
    })
}

pub(crate) fn expand_macros_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, ExpandMacrosError> {
    let resolved = input.resolved_raw().map_err(|error| ExpandMacrosError {
        diagnostics: vec![plain_error(error.to_string())],
    })?;
    let mut output = input.definition.clone();
    let mut diagnostics = Vec::new();
    let views = resolved.views();
    for module in &mut output.modules {
        let module_id = resolved
            .module_id(&module.name)
            .expect("resolved definition contains every source module");
        let mut expander = match Expander::new(&views, module_id, module_id) {
            Ok(expander) => expander,
            Err(diagnostic) => {
                diagnostics.push(diagnostic);
                continue;
            }
        };
        // The internal labels depend only on the module's catalogs; they are computed once, when
        // the first sentence of the module is expanded.
        let mut internal_labels = None;
        for sentence in &mut module.local_sentences {
            // Rules that are not macro-like, claims and contexts are expanded; a macro-like rule
            // defines an abbreviation and is not expanded itself. The decision also says whether
            // a macro symbol left after expansion is reported: for rules and claims, not for
            // contexts.
            let reports_unexpanded_macros = match &**sentence {
                Sentence::Rule { attributes, .. }
                    if !attributes.has_any(&AttributeKey::MACRO_LIKE) =>
                {
                    true
                }
                Sentence::Claim { .. } => true,
                Sentence::Context { .. } => false,
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Rule { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {
                    crate::definition::sentence_mut(sentence);
                    continue;
                }
            };
            // Copying, expanding and checking the sentence walk its terms recursively, so they
            // run with stack in proportion to the deepest term the expansion may hold.
            let zone = stack_zone(sentence_depth(sentence));
            with_stack(zone, || {
                let sentence = crate::definition::sentence_mut(sentence);
                let original = sentence.clone();
                match expander.expand_sentence(original) {
                    Ok(expanded) => {
                        *sentence = expanded;
                        let internal_labels = internal_labels.get_or_insert_with(|| {
                            checks::internal_labels(expander.productions, expander.sorts)
                        });
                        diagnostics.extend(check_functions_with_internal_labels(
                            &[sentence],
                            expander.productions,
                            internal_labels,
                        ));
                        diagnostics.extend(check_smt_lemmas(&[sentence], expander.productions));
                        if reports_unexpanded_macros
                            && contains_macro_symbol(sentence, expander.productions)
                        {
                            diagnostics.push(Diagnostic::error(
                                DiagnosticCode::InvalidMacroExpansion,
                                "Rule contains macro symbol that was not expanded",
                                sentence,
                            ));
                        }
                    }
                    Err(diagnostic) => diagnostics.push(located_at(diagnostic, sentence)),
                }
            });
        }
    }
    if diagnostics.is_empty() {
        Ok(output)
    } else {
        diagnostics.sort();
        diagnostics.dedup();
        Err(ExpandMacrosError { diagnostics })
    }
}

/// Every label applied in the body of an smt-lemma rule has an SMT interpretation (an smt-hook or
/// smtlib attribute); defined only on alias- and macro-free bodies, so it runs on expanded
/// sentences.
fn check_smt_lemmas(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    // Invariant: `diagnostics` holds an error for every label application in the `smt-lemma` rules
    // before `sentence` none of whose productions carries `smt-hook` or `smtlib`; each iteration
    // consumes one entry of `sentences`.
    for sentence in sentences {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        if !attributes.has(AttributeKey::SmtLemma) {
            continue;
        }
        body.visit_preorder(&mut |term| {
            let Term::Apply { label, .. } = term else {
                return;
            };
            let ids = productions.productions_for(&LabelHead::from(label));
            if ids.is_empty() {
                return;
            }
            if ids.iter().all(|id| {
                let attributes = productions.production(*id).attributes();
                !attributes.has(AttributeKey::SmtHook) && !attributes.has(AttributeKey::Smtlib)
            }) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidSmtLemma,
                    "Invalid term in smt-lemma detected. All terms in smt-lemma rules require smt-hook or smtlib labels",
                    sentence,
                ));
            }
        });
    }
    diagnostics
}

/// A program or configuration value after macro expansion in the executable module: every
/// application the module's macro and alias rules match is rewritten. An application that no
/// rule matches remains; the backend's executable-pattern check rejects it at execution.
/// The value carries the position at which expansion types it and injection instantiates it.
///
/// Macro and alias rules are definitional abbreviations that compilation removes from the
/// executable semantics, so a macro application has no meaning there: execution consumes the
/// expansion of a parse, never the parse itself. Only macro expansion produces this value
/// ([`MacroExpansionDefinition::expand_program`], [`expand_macros_in_term`],
/// [`expand_macros_in_term_with_scope`]), so sort injection and KORE conversion of a program
/// cannot receive an unexpanded one:
///
/// ```compile_fail,E0308
/// # use k_rust::{inner::ParsedProgram, kompile::SortInjector};
/// # fn inject(injector: &SortInjector<'_, '_>, program: ParsedProgram) {
/// let _ = injector.inject_at_top(&program); // 99e02f3e: an unexpanded program reaches conversion
/// # }
/// ```
///
/// The expanded term is what injection and conversion read:
///
/// ```
/// # use k_rust::{kompile::{ExpandedProgram, SortInjector}};
/// # fn inject(injector: &SortInjector<'_, '_>, program: ExpandedProgram) {
/// let _ = injector.inject_at_top(program.term());
/// # }
/// ```
///
/// An expansion is not a presentation of the user's text, which shows macro applications as
/// parsed, so a KAST printer does not take this value:
///
/// ```compile_fail,E0308
/// # use k_rust::{kompile::ExpandedProgram, kast::printer::Printer};
/// # fn show(expanded: &ExpandedProgram) -> String {
/// Printer::new().print_term(expanded) // c156f029: an expanded program presented as KAST
/// # }
/// ```
///
/// [`Self::term`] is the accessor every consumer of the expansion uses, so it is not restricted:
/// printing the expanded term compiles, and the site names the stage it prints.
///
/// ```
/// # use k_rust::{kompile::ExpandedProgram, kast::printer::Printer};
/// # fn show(expanded: &ExpandedProgram) -> String {
/// Printer::new().print_term(expanded.term())
/// # }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub struct ExpandedProgram {
    term: Term,
    position: Sort,
}

impl ExpandedProgram {
    /// The expanded term, for sort injection and KORE conversion.
    #[must_use]
    pub fn term(&self) -> &Term {
        &self.term
    }

    /// The position at which expansion types the value and injection instantiates it.
    #[must_use]
    pub fn position(&self) -> &Sort {
        &self.position
    }

    /// The expanded term, by value.
    #[must_use]
    pub fn into_term(self) -> Term {
        self.term
    }
}

/// Expand macros in a program or configuration value, a term parsed outside the definition.
///
/// Definition compilation expands sentence bodies, but concrete programs are parsed only after
/// that pipeline has finished. They must use the same propagated macro rules before sort
/// injection and KORE conversion.
pub fn expand_macros_in_term(
    definition: &Definition,
    module: &str,
    program: ParsedProgram,
    position: &Sort,
) -> Result<ExpandedProgram, String> {
    expand_macros_in_term_with_scope(definition, module, module, program, position)
}

/// Expand a standalone program parsed in one module with another module's executable syntax.
///
/// Source-driven execution parses concrete input in a syntax or configuration parser module,
/// while K selects executable macro rules from the main module. Parsed applications are rebased
/// into the executable module before expansion so a macro right-hand side may use a production
/// visible only there. A parser-only lexical token instead keeps its self-describing sort and
/// discards the production index.
pub fn expand_macros_in_term_with_scope(
    definition: &Definition,
    _term_module: &str,
    macro_module: &str,
    program: ParsedProgram,
    position: &Sort,
) -> Result<ExpandedProgram, String> {
    MacroExpansionDefinition::prepare(definition)?.expand_program(macro_module, program, position)
}

/// The definition from which standalone terms, such as a program or a configuration-variable
/// value, are macro-expanded.
///
/// Rule parsing retains semantic-cast wrappers around variables. The compilation pipeline
/// removes those wrappers and marks each rule of a macro-like production with the production's
/// macro kind before macro matching, so concrete terms build their expander from the same rule
/// shape. The prepared value depends on the definition alone and not on the term, so one value
/// serves every term expanded against the same definition.
pub struct MacroExpansionDefinition {
    resolved: ResolvedDefinition,
}

impl MacroExpansionDefinition {
    /// Resolve semantic casts in, and propagate macro kinds onto, every rule that can become a
    /// macro rule, and resolve the result.
    ///
    /// An expander reads from its definition the productions, sort declarations, and syntax
    /// relations of its module (catalogs, subsorts, overloads, sort injection) and the rules that
    /// `macro_rule` accepts. Cast resolution and propagation change only the terms and attributes
    /// of rules, so they leave the first part unchanged; this function applies them to a superset
    /// of the accepted rules and leaves every other rule as written:
    ///
    /// - `macro_rule` accepts a rule when it carries a macro kind, or when the head of its
    ///   rewrite's left projection has a macro-kind production visible in the expander's module.
    ///   Cast resolution replaces a cast application by its argument and rebuilds every other
    ///   node with its own label, and the projection keeps the labels of what it keeps, so that
    ///   head is a label of the unresolved body. A production visible in any module is a
    ///   production of the definition, so `may_become_macro_rule` over the macro-kind labels of
    ///   all productions keeps every rule accepted in any module.
    /// - Propagation adds a macro kind only for a label with a macro-kind production, which the
    ///   same test covers.
    ///
    /// A rule outside that superset is rejected by `macro_rule` with or without the passes. It
    /// can differ from its transformed form only in terms and attributes, so where visible-sentence
    /// deduplication would have merged it with a transformed rule, both are rejected alike; kept
    /// rules therefore appear in the same order, and rule identities are compared only with each
    /// other. The expander thus holds the same macro rules, in the same priority order, as with
    /// the passes applied to the whole definition.
    ///
    /// The transformed rules carry no semantic-cast origin receipts: the passes run here on single
    /// sentences, outside the pipeline that records provenance. Receipts are provenance only;
    /// sentence and term equality ignore them, and matching reads none.
    pub fn prepare(definition: &Definition) -> Result<Self, String> {
        // Resolving casts in a rule copies and rebuilds its terms recursively.
        with_stack(stack_zone(definition_depth(definition)), || {
            Self::prepare_on_stack(definition)
        })
    }

    fn prepare_on_stack(definition: &Definition) -> Result<Self, String> {
        let original =
            ResolvedDefinition::resolve(definition).map_err(|error| error.to_string())?;
        let views = original.views();
        let macro_labels = macro_production_labels(definition);
        let mut prepared = definition.clone();
        for module in &mut prepared.modules {
            let module_id = original
                .module_id(&module.name)
                .expect("resolved definition contains every source module");
            let mut subsorts = None;
            for sentence in &mut module.local_sentences {
                if !may_become_macro_rule(sentence, &macro_labels) {
                    continue;
                }
                let order = match subsorts {
                    Some(order) => order,
                    None => {
                        let order = views
                            .subsorts(module_id)
                            .map_err(|error| error.to_string())?;
                        subsorts = Some(order);
                        order
                    }
                };
                // Same order as the pipeline: propagation reads the cast-free left side.
                let mut rule =
                    super::resolve_semantic_casts_in_sentence(order, Sentence::clone(sentence))
                        .map_err(|error| error.to_string())?;
                super::propagate_macro_attribute(&mut rule, views.production_catalog(module_id));
                *sentence = std::sync::Arc::new(rule);
            }
        }
        let resolved = ResolvedDefinition::resolve(&prepared).map_err(|error| error.to_string())?;
        Ok(Self { resolved })
    }

    /// Expand the macros of `macro_module` in one parsed program or configuration value.
    ///
    /// Each call builds its own expander and fresh-name allocator, so the result of one call
    /// does not depend on the programs expanded by earlier calls.
    pub fn expand_program(
        &self,
        macro_module: &str,
        program: ParsedProgram,
        position: &Sort,
    ) -> Result<ExpandedProgram, String> {
        let views = self.resolved.views();
        let mut expanded = expand_macros_in_terms_from_views_with_scope(
            &views,
            macro_module,
            macro_module,
            vec![(program.into_typed_term(), position.clone())],
        )
        .map_err(|diagnostic| diagnostic.message)?;
        Ok(ExpandedProgram {
            term: expanded
                .terms
                .pop()
                .expect("one input term produces one expanded term"),
            position: position.clone(),
        })
    }
}

/// The label names of every production with a macro kind, in any module of `definition`.
///
/// An unlabeled production contributes the empty name, as in `ProductionCatalog::macro_labels`.
fn macro_production_labels(definition: &Definition) -> BTreeSet<&str> {
    definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label, attributes, ..
            } if attributes.has_any(&AttributeKey::MACRO_LIKE) => {
                Some(label.as_ref().map_or("", |label| label.name.as_str()))
            }
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
        .collect()
}

/// Whether a rule carries a macro kind or applies a label with a macro-kind production anywhere
/// in its body; `MacroExpansionDefinition::prepare` shows every rule `macro_rule` can accept
/// after cast resolution and propagation passes this test.
fn may_become_macro_rule(sentence: &Sentence, macro_labels: &BTreeSet<&str>) -> bool {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return false;
    };
    if attributes.has_any(&AttributeKey::MACRO_LIKE) {
        return true;
    }
    let mut applies_macro_label = false;
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term {
            applies_macro_label |= macro_labels.contains(label.name.as_str());
        }
    });
    applies_macro_label
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpandedMacroTerms {
    pub terms: Vec<Term>,
    pub generated_variables: BTreeSet<GeneratedVariableIdentity>,
}

/// Expand several standalone roots through one macro expander and fresh-name allocator.
pub(crate) fn expand_macros_in_terms_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
    terms: Vec<(Term, Sort)>,
) -> Result<ExpandedMacroTerms, String> {
    let views = definition.views();
    expand_macros_in_terms_from_views_with_scope(&views, module, module, terms)
        .map_err(|diagnostic| diagnostic.message)
}

fn expand_macros_in_terms_from_views_with_scope(
    views: &DefinitionViews<'_>,
    term_module: &str,
    macro_module: &str,
    terms: Vec<(Term, Sort)>,
) -> Result<ExpandedMacroTerms, Diagnostic> {
    let definition = views.definition();
    let term_module = definition
        .module_id(term_module)
        .ok_or_else(|| plain_error(format!("unknown module {term_module}")))?;
    let macro_module = definition
        .module_id(macro_module)
        .ok_or_else(|| plain_error(format!("unknown module {macro_module}")))?;
    let mut expander = Expander::new(views, term_module, macro_module)?;
    // Every term is walked recursively before and during its expansion, so the work runs with
    // stack in proportion to the deepest term the expansion may hold.
    let zone = stack_zone(
        terms
            .iter()
            .map(|(term, _)| term_depth(term))
            .max()
            .unwrap_or(0),
    );
    let terms = with_stack(zone, || {
        expander.fresh = FreshNames::for_terms(terms.iter().map(|(term, _)| term));
        terms
            .into_iter()
            .map(|(mut term, position)| {
                erase_parser_instances(&mut term, expander.productions);
                expander.expand_standalone(term, &position)
            })
            .collect::<Result<Vec<_>, _>>()
    })?;
    Ok(ExpandedMacroTerms {
        terms,
        generated_variables: expander.generated,
    })
}

struct Expander<'view, 'definition> {
    productions: &'view ProductionCatalog<'definition>,
    sorts: &'view SortCatalog<'definition>,
    injector: SortInjector<'view, 'definition>,
    subsorts: &'view crate::definition::PartialOrder<Sort>,
    overloads: &'view crate::definition::OverloadOrder<'definition>,
    /// Macro rules by the head of their left side. A loaded rule's head carries no sort
    /// parameter, so it stands for every instance of its production; the variable sorts of its
    /// arguments decide whether it applies to a given subject.
    macros: BTreeMap<LabelHead, Vec<MacroRule>>,
    token_macros: BTreeMap<Sort, Vec<MacroRule>>,
    /// The typing view of the term module, present when some macro rule has a parametric head:
    /// then an application's instance is read from the typing of the sentence it stands in.
    typer: Option<SentenceTyper<'definition>>,
    fresh: FreshNames,
    generated: BTreeSet<GeneratedVariableIdentity>,
    /// Rewrites by `macro-rec` and `alias-rec` rules made since the sentence or standalone
    /// term began expanding.
    recursive_rewrites: usize,
    /// The depth recursive rewrites may add along one path of the term being expanded: the
    /// larger of [`MIN_RECURSIVE_GROWTH`] and the depth of the term before expansion.
    growth_allowance: usize,
    /// The stack red zone of the expansion recursion, sized for the deepest term the expansion
    /// may hold ([`stack_zone`]).
    red_zone: usize,
}

impl<'view, 'definition> Expander<'view, 'definition> {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn new(
        views: &'view DefinitionViews<'definition>,
        term_module: ModuleId,
        macro_module: ModuleId,
    ) -> Result<Self, Diagnostic> {
        let definition = views.definition();
        let productions = views.production_catalog(term_module);
        let sorts = views.sort_catalog(term_module);
        let injector = SortInjector::with_views(views, term_module)
            .map_err(|error| plain_error(error.to_string()))?;
        let subsorts = views
            .subsorts(term_module)
            .map_err(|error| plain_error(error.to_string()))?;
        let overloads = views
            .overloads(term_module)
            .map_err(|error| plain_error(error.to_string()))?;
        let all = definition
            .sentences(macro_module)
            .into_iter()
            .enumerate()
            .filter_map(|(id, sentence)| {
                macro_rule(id, sentence, productions).map(|rule| (sentence, rule))
            })
            .map(|(_, rule)| Ok(rule))
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let priorities = all
            .iter()
            .map(|rule| macro_priority(rule.sentence.attributes()))
            .collect::<Result<Vec<_>, _>>()?;
        let mut all = all.into_iter().zip(priorities).collect::<Vec<_>>();
        let parametric = all.iter().any(|(rule, _)| {
            matches!(rule.left.unannotated(), Term::Apply { label, .. }
                if production_parameters(productions, label).is_some())
        });
        let mut typer = None;
        if parametric {
            // A typing view that cannot be built leaves every instance open.
            let macro_typer =
                SentenceTyper::new(definition, &definition.module(macro_module).name).ok();
            for (rule, _) in &mut all {
                rule.head_instance = macro_typer
                    .as_ref()
                    .and_then(|typer| head_instance(typer, productions, rule));
            }
            typer = SentenceTyper::new(definition, &definition.module(term_module).name).ok();
        }
        all.sort_by_key(|(_, priority)| *priority);
        let mut macros = BTreeMap::<LabelHead, Vec<MacroRule>>::new();
        let mut token_macros = BTreeMap::<Sort, Vec<MacroRule>>::new();
        // Invariant: `macros` and `token_macros` hold, in ascending priority order, every rule of `all` before `rule` whose left side is an application, a token, or a sorted variable; each iteration consumes one entry of `all`.
        for (rule, _) in all {
            match rule.left.unannotated() {
                Term::Apply { label, .. } => {
                    macros.entry(LabelHead::from(label)).or_default().push(rule)
                }
                Term::Token { sort, .. } => {
                    token_macros.entry(sort.clone()).or_default().push(rule)
                }
                Term::Variable { sort, .. } => {
                    let sort = sort.clone().or_else(|| {
                        rule.left
                            .metadata()
                            .and_then(|metadata| metadata.sort.clone())
                    });
                    if let Some(sort) = sort {
                        token_macros.entry(sort).or_default().push(rule);
                    }
                }
                _ => {}
            }
        }
        Ok(Self {
            productions,
            sorts,
            injector,
            subsorts,
            overloads,
            macros,
            token_macros,
            typer,
            fresh: FreshNames::default(),
            generated: BTreeSet::new(),
            recursive_rewrites: 0,
            growth_allowance: MIN_RECURSIVE_GROWTH,
            red_zone: stack_zone(0),
        })
    }

    fn expand_sentence(&mut self, sentence: Sentence) -> Result<Sentence, Diagnostic> {
        self.fresh = FreshNames::for_sentence(&sentence);
        self.generated.clear();
        self.begin(sentence_depth(&sentence));
        if self.typer.is_some() {
            let fields: &[u32] = match &sentence {
                Sentence::Rule { .. } | Sentence::Claim { .. } => &[0, 1, 2],
                Sentence::Context { .. } => &[0, 1],
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => return Ok(sentence),
            };
            let mut site = Site::new(sentence);
            self.expand_site(&mut site, fields)?;
            return Ok(site.sentence);
        }
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Rule {
                body: self.expand_term(body, &BTreeSet::new(), 0)?,
                requires: self.expand_term(requires, &BTreeSet::new(), 0)?,
                ensures: self.expand_term(ensures, &BTreeSet::new(), 0)?,
                attributes,
            }),
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Claim {
                body: self.expand_term(body, &BTreeSet::new(), 0)?,
                requires: self.expand_term(requires, &BTreeSet::new(), 0)?,
                ensures: self.expand_term(ensures, &BTreeSet::new(), 0)?,
                attributes,
            }),
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Ok(Sentence::Context {
                body: self.expand_term(body, &BTreeSet::new(), 0)?,
                requires: self.expand_term(requires, &BTreeSet::new(), 0)?,
                attributes,
            }),
            sentence @ Sentence::SyntaxSort { .. }
            | sentence @ Sentence::SortSynonym { .. }
            | sentence @ Sentence::SyntaxLexical { .. }
            | sentence @ Sentence::Production { .. }
            | sentence @ Sentence::SyntaxAssociativity { .. }
            | sentence @ Sentence::SyntaxPriority { .. }
            | sentence @ Sentence::ContextAlias { .. }
            | sentence @ Sentence::Configuration { .. }
            | sentence @ Sentence::Bubble { .. } => Ok(sentence),
        }
    }

    /// Expand the macros of `term`, innermost first, under the rules `applied` above it;
    /// recursive rewrites enclosing it have added `grown` levels of depth on its path.
    fn expand_term(
        &mut self,
        term: Term,
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<Term, Diagnostic> {
        self.expand_known(term, Known::Unknown, applied, grown)
            .map(|(term, _)| term)
    }

    /// [`Self::expand_term`] for a term of which `known` tells which parts are settled
    /// expansion results, which are kept as they are; with whether the result is settled.
    fn expand_known(
        &mut self,
        term: Term,
        known: Known,
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<(Term, bool), Diagnostic> {
        if matches!(known, Known::Settled) {
            return Ok((term, true));
        }
        with_stack(self.red_zone, || {
            self.expand_chain(term, known, applied, grown)
        })
    }

    /// Expand the arguments of `term`, then rewrite it at its root until no rule applies,
    /// expanding the arguments of each result before trying the rules again; with whether
    /// the result is settled.
    ///
    /// The root rewrites form a [`Chain`] and are made in a loop, so a long chain takes no
    /// native stack; only a rewrite inside an argument of a result nests. The parts of a
    /// result that a rule's variables bound to settled subterms of its subject are kept as
    /// they are ([`Known`]), so a recursive rule that carries a large settled argument along
    /// expands only what its right side builds around it.
    fn expand_chain(
        &mut self,
        term: Term,
        known: Known,
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<(Term, bool), Diagnostic> {
        let mut chain = Chain::default();
        let mut grown = grown;
        let mut term = term;
        let mut known = known;
        let mut chain_applied = None::<BTreeSet<usize>>;
        // Invariant: `term` is the result of the chain's last rewrite (the original term before any), `known` tells which of its parts are settled, and `chain_applied` holds the rules applied above it (`applied` before any rewrite); each iteration returns or makes one rewrite, and `record_rewrite` bounds the rewrites of the sentence.
        loop {
            if matches!(known, Known::Settled) {
                return Ok((term, true));
            }
            let applied = chain_applied.as_ref().unwrap_or(applied);
            let Expanded {
                term: subject,
                rules,
                settled,
            } = self.expand_arguments(term, known, applied, grown)?;
            let Some(rules) = rules else {
                let settled = settled.iter().all(|settled| *settled);
                return Ok((subject, settled));
            };
            let Some((index, bindings)) = self.select_rule(&subject, &rules, applied, None)? else {
                return Ok((subject, false));
            };
            let rule = &rules[index];
            self.record_rewrite(
                &mut chain,
                rule,
                &subject,
                &bindings,
                applied.len(),
                &mut grown,
            )?;
            let (result, result_known) = self.instantiate(rule, subject, &settled);
            let mut next_applied = applied.clone();
            next_applied.insert(rule.id);
            chain_applied = Some(next_applied);
            term = result;
            known = result_known;
        }
    }

    /// `term` with its children expanded under `applied` and `grown`, the parts `known` marks
    /// settled kept as they are; with the macro rules of its head when it is an application
    /// or a token that some rule may rewrite, and whether each child is settled.
    fn expand_arguments(
        &mut self,
        term: Term,
        known: Known,
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<Expanded, Diagnostic> {
        measure::bump(Counter::KompileMacroExpansionVisits);
        let below = grown;
        let metadata = term.metadata().cloned();
        let mut children = match known {
            Known::Children(children) => children.into_iter(),
            Known::Unknown | Known::Settled => Vec::new().into_iter(),
        };
        let mut next = move || children.next().unwrap_or(Known::Unknown);
        let mut settled = Vec::new();
        let mut expand = |expander: &mut Self, child: Term| {
            let (child, child_settled) = expander.expand_known(child, next(), applied, below)?;
            settled.push(child_settled);
            Ok::<_, Diagnostic>(child)
        };
        let (term, rules) = match term.into_unannotated().into_parts() {
            TermParts::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| expand(self, argument))
                    .collect::<Result<Vec<_>, _>>()?;
                let rules = self.macros.get(&LabelHead::from(&label)).cloned();
                (Term::Apply { label, arguments }, rules)
            }
            TermParts::Token { token, sort } => {
                let rules = self.token_macros.get(&sort).cloned();
                (Term::Token { token, sort }, rules)
            }
            TermParts::Rewrite { left, right } => (
                Term::Rewrite {
                    left: Box::new(expand(self, *left)?),
                    right: Box::new(expand(self, *right)?),
                },
                None,
            ),
            TermParts::As { pattern, alias } => (
                Term::As {
                    pattern: Box::new(expand(self, *pattern)?),
                    alias: Box::new(expand(self, *alias)?),
                },
                None,
            ),
            TermParts::Sequence(items) => (
                Term::Sequence(
                    items
                        .into_iter()
                        .map(|item| expand(self, item))
                        .collect::<Result<_, _>>()?,
                ),
                None,
            ),
            leaf @ (TermParts::InjectedLabel(_) | TermParts::Variable { .. }) => {
                (Term::from(leaf), None)
            }
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        Ok(Expanded {
            term: with_metadata(term, metadata),
            rules,
            settled,
        })
    }

    /// Account for the rewrite of `subject`, selected under `applied` earlier rules, by `rule`
    /// with `bindings` as the next step of `chain`, on a path where recursive rewrites have
    /// added `grown` levels of depth so far.
    ///
    /// A rule that is not `macro-rec` or `alias-rec` applies at most once on a path, so only
    /// rewrites by the recursive ones can make expansion diverge, and only they are accounted
    /// for: a chain that repeats a subject, the recursive rewrite that exceeds the sentence's
    /// budget of [`MAX_RECURSIVE_REWRITES`], and a path whose recursive rewrites have added more
    /// depth than the growth allowance are reported at the rule.
    ///
    /// Expansion is deterministic: the subject with its arguments expanded and the rules already
    /// applied above it decide the rule selected and its result, up to the names of variables
    /// the result introduces. A chain whose subject recurs under as many applied rules (which
    /// only grow along a chain, so under the same ones) therefore repeats forever. Any other
    /// infinite expansion makes infinitely many recursive rewrites, so the budget ends it.
    /// A divergence that deepens the term, by nesting rewrites inside results (`t => s(t)`) or
    /// by growing the subject at the root (`f(X) => f(s(X))`), adds depth at every step along
    /// one path; replacing a subterm of depth d by one of depth d' deepens the term by at most
    /// d' - d, so the sum of those increases along a path bounds the depth the recursive rules
    /// have added there, and the allowance ends such a divergence within as many steps, long
    /// before the budget and before the term outgrows the stack its walks are given.
    fn record_rewrite(
        &mut self,
        chain: &mut Chain,
        rule: &MacroRule,
        subject: &Term,
        bindings: &Bindings<'_, '_>,
        applied: usize,
        grown: &mut usize,
    ) -> Result<(), Diagnostic> {
        if !rule.recursive {
            return Ok(());
        }
        // The subject is the left side and the result the right side with each variable
        // replaced by its binding, so both depths follow from the depths of the bindings.
        let depths = bindings
            .iter()
            .map(|(name, binding)| (*name, term_depth(binding)))
            .collect::<BTreeMap<_, _>>();
        let subject_depth = instance_depth(&rule.left, &depths);
        let result_depth = instance_depth(&rule.right, &depths);
        let diverges = |message: String| {
            Err(Diagnostic::error(
                DiagnosticCode::InvalidMacroExpansion,
                message,
                &rule.sentence,
            ))
        };
        if chain.repeats(subject, applied, subject_depth) {
            return diverges(format!(
                "Macro expansion does not terminate: expanding {} with this macro rule leads back to {}, so the expansion repeats forever.",
                shown(subject),
                shown(subject)
            ));
        }
        self.recursive_rewrites += 1;
        if self.recursive_rewrites > MAX_RECURSIVE_REWRITES {
            return diverges(format!(
                "Macro expansion does not terminate within {MAX_RECURSIVE_REWRITES} rewrites by macro-rec rules in one sentence; this macro rule made the last one, of {}. The macro-rec rules applied keep producing applications they rewrite again.",
                shown(subject)
            ));
        }
        *grown += result_depth.saturating_sub(subject_depth);
        if *grown > self.growth_allowance {
            return diverges(format!(
                "Macro expansion does not terminate: the macro-rec rules applied have made one path of the term more than {} levels deeper (the larger of {MIN_RECURSIVE_GROWTH} and the depth of the term before expansion); this macro rule made the last such rewrite, of {}. The macro-rec rules applied keep producing applications they rewrite again.",
                self.growth_allowance,
                shown(subject)
            ));
        }
        Ok(())
    }

    /// Start the expansion of one sentence or standalone term, whose terms are at most
    /// `input_depth` deep, with its full budget.
    fn begin(&mut self, input_depth: usize) {
        self.recursive_rewrites = 0;
        self.growth_allowance = growth_allowance(input_depth);
        self.red_zone = stack_zone(input_depth);
    }

    /// The index in `rules` of the first rule that applies to `subject` (its head instance
    /// agreeing with `instance`, its left side matching, and it recursive or absent from
    /// `applied`), with the subterm of `subject` each variable of its left side stands for.
    fn select_rule<'rules, 'subject>(
        &self,
        subject: &'subject Term,
        rules: &'rules [MacroRule],
        applied: &BTreeSet<usize>,
        instance: Option<&Instance>,
    ) -> Result<Option<(usize, Bindings<'rules, 'subject>)>, Diagnostic> {
        // Invariant: no rule of `rules` before `rule` both matched `subject` and was recursive or absent from `applied`; each iteration consumes one element of the finite slice `rules`, and the first applicable rule is returned with its bindings.
        for (index, rule) in rules.iter().enumerate() {
            let Sentence::Rule { requires, .. } = &rule.sentence else {
                unreachable!()
            };
            if requires != &truth() {
                return Err(Diagnostic::error(
                    DiagnosticCode::InvalidMacroExpansion,
                    "Cannot compute macros with side conditions.",
                    &rule.sentence,
                ));
            }
            if !instances_agree(rule.head_instance.as_deref(), instance) {
                continue;
            }
            let mut bindings = BTreeMap::new();
            let matched = self.matches(&mut bindings, &rule.left, subject)?;
            if matched && (rule.recursive || !applied.contains(&rule.id)) {
                measure::bump(Counter::KompileMacroApplications);
                return Ok(Some((index, bindings)));
            }
        }
        Ok(None)
    }

    /// The right side of `rule`, which matched `subject`, with its variables replaced
    /// ([`Self::substitute`]); with what is known of it, given whether each argument of
    /// `subject` is settled (`settled`, empty when nothing is known).
    ///
    /// The bindings are moved out of `subject`, which the rewrite replaces, rather than
    /// copied: each is moved into its last occurrence in the result and copied into the
    /// others, so the result is the one copies alone would give.
    fn instantiate(&mut self, rule: &MacroRule, subject: Term, settled: &[bool]) -> (Term, Known) {
        let mut bindings = BTreeMap::new();
        take_bindings(&rule.left, subject, &mut bindings);
        let mut bindings = bindings
            .into_iter()
            .map(|(name, binding)| (name, (binding, 0)))
            .collect::<BTreeMap<_, _>>();
        rule.right.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term
                && let Some((_, uses)) = bindings.get_mut(name.as_str())
            {
                *uses += 1;
            }
        });
        let settled = settled_variables(&rule.left, settled);
        self.substitute(
            rule.right.clone(),
            &mut bindings,
            &settled,
            &mut BTreeMap::new(),
        )
    }

    /// Expand a term parsed outside the definition. With a parametric macro head it is expanded
    /// at its position, so selection reads the instance injection emits there.
    fn expand_standalone(&mut self, term: Term, position: &Sort) -> Result<Term, Diagnostic> {
        self.begin(term_depth(&term));
        if self.typer.is_none() {
            return self.expand_term(term, &BTreeSet::new(), 0);
        }
        let mut site = Site::ground(term, position);
        self.expand_site(&mut site, &[0])?;
        let Sentence::Rule { body, .. } = site.sentence else {
            unreachable!("the site holds the rule it was built from")
        };
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        measure::without_counting(|| {
            crate::kompile::invariants::ground::assert_ground_instances(
                self.productions,
                self.typer
                    .as_ref()
                    .expect("ground sites have a typing view"),
                &self.injector,
                &body,
                position,
            );
        });
        Ok(body)
    }

    /// Expand the macros of the term at `path` of `site`, innermost first, in place.
    ///
    /// This is [`Self::expand_term`] for a definition with a parametric macro head. A macro
    /// rule is an axiom about one instance of its head's symbol, and a loaded application
    /// carries no instance, so the instance of an application is read from the typing of the
    /// sentence as it stands when the application's rules are tried: after its arguments have
    /// been expanded, and after every earlier rewrite of the sentence.
    fn expand_at(
        &mut self,
        site: &mut Site,
        path: &[u32],
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<(), Diagnostic> {
        measure::bump(Counter::KompileMacroExpansionVisits);
        with_stack(self.red_zone, || {
            self.expand_children(site, path, applied, grown)?;
            self.try_rules(site, path, applied, grown)
        })
    }

    /// Expand the macros of every child of the term at `path` of `site`.
    fn expand_children(
        &mut self,
        site: &mut Site,
        path: &[u32],
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<(), Diagnostic> {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only the listed variants are special here"
        )]
        let children = match site.term(path).unannotated() {
            Term::Apply { arguments, .. } => arguments.len(),
            Term::Sequence(items) => items.len(),
            Term::Rewrite { .. } | Term::As { .. } => 2,
            _ => 0,
        };
        for index in 0..children {
            let mut child = path.to_vec();
            child.push(u32::try_from(index).expect("a term has fewer than 2^32 children"));
            self.expand_at(site, &child, applied, grown)?;
        }
        Ok(())
    }

    /// Expand the given fields of `site`, then retry every failed application whose rule set has a head fixing a sort parameter after a rewriting round until no retry rewrites anything: a rewrite elsewhere can change even a known instance.
    /// An application still unknown at the fixpoint is left as it is, and compilation reports the ill-sorted sentence at injection.
    fn expand_site(&mut self, site: &mut Site, fields: &[u32]) -> Result<(), Diagnostic> {
        for field in fields {
            self.expand_at(site, &[*field], &BTreeSet::new(), 0)?;
        }
        if site.rewrites == 0 {
            return Ok(());
        }
        // Invariant: `site.tried` holds every failed application whose rule set has a parametric head fixing a parameter, with its path, own applied rule set, and term, plus the macro-headed ancestors of an application rewritten in the previous round with their own applied rule sets; every such application still present is retried after a rewriting round, and a round without a rewrite ends the loop.
        while !site.tried.is_empty() {
            let rewrites = site.rewrites;
            for (path, (applied, grown), subject) in std::mem::take(&mut site.tried) {
                // A tried application inside a subtree a later rewrite replaced is gone.
                if site.get(&path) != Some(&subject) {
                    continue;
                }
                let before = site.rewrites;
                self.try_rules(site, &path, &applied, grown)?;
                if site.rewrites != before {
                    // Its enclosing applications were tried before it was expanded.
                    for length in (1..path.len()).rev() {
                        let ancestor = path[..length].to_vec();
                        if let Some(term) = site.get(&ancestor)
                            && let Term::Apply { label, .. } = term.unannotated()
                            && self.macros.contains_key(&LabelHead::from(label))
                        {
                            let term = term.clone();
                            // Every macro-headed application is recorded when its rules are tried, and a
                            // replacement below an ancestor keeps the ancestor's record.
                            let ancestor_context = site
                                .applied
                                .get(&ancestor)
                                .cloned()
                                .expect("a surviving macro-headed application was tried after its last replacement");
                            site.tried.push((ancestor, ancestor_context, term));
                        }
                    }
                }
            }
            if site.rewrites == rewrites {
                break;
            }
        }
        Ok(())
    }

    /// Try the macro rules of the application or token at `path`, whose arguments are already
    /// expanded at the current typing of the site, and rewrite it until no rule applies,
    /// expanding the children of each result first; the chain of root rewrites is the one
    /// [`Self::expand_chain`] makes, in a loop.
    fn try_rules(
        &mut self,
        site: &mut Site,
        path: &[u32],
        applied: &BTreeSet<usize>,
        grown: usize,
    ) -> Result<(), Diagnostic> {
        let mut chain = Chain::default();
        let mut grown = grown;
        let mut chain_applied = None::<BTreeSet<usize>>;
        // Invariant: the term at `path` is the result of the chain's last rewrite (the original application before any) with its children expanded, and `chain_applied` holds the rules applied above it (`applied` before any rewrite); each iteration returns or makes one rewrite, and `record_rewrite` bounds the rewrites of the sentence.
        loop {
            let applied = chain_applied.as_ref().unwrap_or(applied);
            let Some(next_applied) =
                self.try_rules_once(site, path, applied, &mut grown, &mut chain)?
            else {
                return Ok(());
            };
            self.expand_children(site, path, &next_applied, grown)?;
            chain_applied = Some(next_applied);
        }
    }

    /// Rewrite the application or token at `path` once, returning the rules applied above its
    /// result, or record it for a retry when no rule applies.
    fn try_rules_once(
        &mut self,
        site: &mut Site,
        path: &[u32],
        applied: &BTreeSet<usize>,
        grown: &mut usize,
        chain: &mut Chain,
    ) -> Result<Option<BTreeSet<usize>>, Diagnostic> {
        let subject = site.term(path).clone();
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only the listed variants are special here"
        )]
        let (rules, instance) = match subject.unannotated() {
            Term::Apply { label, .. } => {
                let Some(rules) = self.macros.get(&LabelHead::from(label)).cloned() else {
                    return Ok(None);
                };
                let instance = if rules.iter().any(|rule| rule.head_instance.is_some()) {
                    Some(self.subject_instance(site, path))
                } else {
                    None
                };
                site.applied
                    .insert(path.to_vec(), (applied.clone(), *grown));
                (rules, instance)
            }
            Term::Token { sort, .. } => match self.token_macros.get(sort).cloned() {
                Some(rules) => (rules, None),
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        if let Some((index, bindings)) =
            self.select_rule(&subject, &rules, applied, instance.as_ref())?
        {
            let rule = &rules[index];
            self.record_rewrite(chain, rule, &subject, &bindings, applied.len(), grown)?;
            let (result, _) = self.instantiate(rule, subject, &[]);
            site.replace(path, result);
            let mut next_applied = applied.clone();
            next_applied.insert(rule.id);
            return Ok(Some(next_applied));
        }
        if instance.is_some()
            && rules.iter().any(|rule| {
                rule.head_instance
                    .as_ref()
                    .is_some_and(|head| head.iter().any(Option::is_some))
            })
        {
            site.tried
                .push((path.to_vec(), (applied.clone(), *grown), subject));
        }
        Ok(None)
    }

    /// The instance of the application at `path` in the current typing of its site.
    fn subject_instance(&self, site: &mut Site, path: &[u32]) -> Instance {
        let Some(typer) = self.typer.as_ref() else {
            return Instance::Unknown;
        };
        match site
            .typing(typer)
            .and_then(|typing| typing.instances.get(path))
        {
            Some(instance) => Instance::Known(instance.clone()),
            None => Instance::Unknown,
        }
    }

    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    /// Whether `pattern` matches `subject`, extending `bindings` with the subterm of `subject`
    /// each of its variables stands for.
    fn matches<'pattern, 'subject>(
        &self,
        bindings: &mut Bindings<'pattern, 'subject>,
        pattern: &'pattern Term,
        subject: &'subject Term,
    ) -> Result<bool, Diagnostic> {
        let metadata_sort = pattern
            .metadata()
            .and_then(|metadata| metadata.sort.as_ref());
        match pattern.unannotated() {
            Term::Variable { name, sort } => {
                if let Some(existing) = bindings.get(name.as_str()) {
                    return Ok(*existing == subject);
                }
                if let Some(pattern_sort) = sort.as_ref().or(metadata_sort) {
                    let subject_sort = self
                        .injector
                        .term_sort(subject, None)
                        .map_err(|error| plain_error(error.to_string()))?;
                    if !self.subsorts.less_than_eq(&subject_sort, pattern_sort) {
                        return Ok(false);
                    }
                }
                bindings.insert(name, subject);
                Ok(true)
            }
            Term::Apply {
                label: pattern_label,
                arguments: pattern_arguments,
            } => {
                let Term::Apply {
                    label: subject_label,
                    arguments: subject_arguments,
                } = subject.unannotated()
                else {
                    return Ok(false);
                };
                if pattern_label.name != subject_label.name
                    && !self.pattern_overloads_subject(pattern_label, subject_label)
                {
                    return Ok(false);
                }
                if pattern_arguments.len() != subject_arguments.len() {
                    return Ok(false);
                }
                for (pattern, subject) in pattern_arguments.iter().zip(subject_arguments) {
                    if !self.matches(bindings, pattern, subject)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Term::Token { .. } => Ok(pattern == subject),
            _ if matches!(
                subject.unannotated(),
                Term::Variable { .. } | Term::Token { .. }
            ) =>
            {
                Ok(false)
            }
            _ => Err(plain_error(
                "Cannot compute macros with terms that are not KApply, KToken, or KVariable.",
            )),
        }
    }

    fn pattern_overloads_subject(&self, pattern: &Label, subject: &Label) -> bool {
        let Some(pattern) = self
            .productions
            .productions_for(&LabelHead::from(pattern))
            .first()
        else {
            return false;
        };
        let Some(subject) = self
            .productions
            .productions_for(&LabelHead::from(subject))
            .first()
        else {
            return false;
        };
        self.overloads.order().greater_than(pattern, subject)
    }

    /// `term`, a rule's right side, with each variable bound by the match replaced by its
    /// binding and each other variable but `#Configuration` by a fresh one, the same fresh
    /// variable for every occurrence of a name; with what is known of the result: a binding
    /// in `settled` is settled.
    ///
    /// Each binding comes with the number of its occurrences not yet replaced; the last one
    /// takes the binding itself, and the others a copy.
    fn substitute(
        &mut self,
        term: Term,
        bindings: &mut BTreeMap<&str, (Term, usize)>,
        settled: &BTreeSet<&str>,
        fresh: &mut BTreeMap<String, Term>,
    ) -> (Term, Known) {
        let metadata = term.metadata().cloned();
        let (rebuilt, known) = match term.into_unannotated().into_parts() {
            TermParts::Variable { name, sort } => {
                let last = bindings.get_mut(name.as_str()).map(|(_, uses)| {
                    *uses -= 1;
                    *uses == 0
                });
                if let Some(last) = last {
                    let known = if settled.contains(name.as_str()) {
                        Known::Settled
                    } else {
                        Known::Unknown
                    };
                    let binding = if last {
                        bindings
                            .remove(name.as_str())
                            .expect("a bound variable has a binding")
                            .0
                    } else {
                        bindings[name.as_str()].0.clone()
                    };
                    return (binding, known);
                }
                if let Some(variable) = fresh.get(&name) {
                    return (variable.clone(), Known::Unknown);
                }
                if name == "#Configuration" {
                    (Term::Variable { name, sort }, Known::Unknown)
                } else {
                    let generated_name = self.fresh.mint("_Gen");
                    self.generated
                        .insert(GeneratedVariableIdentity::element(generated_name.clone()));
                    let variable = Term::Variable {
                        name: generated_name,
                        sort,
                    };
                    fresh.insert(name, variable.clone());
                    (variable, Known::Unknown)
                }
            }
            TermParts::Apply { label, arguments } => {
                let (arguments, known) = arguments
                    .into_iter()
                    .map(|argument| self.substitute(argument, bindings, settled, fresh))
                    .unzip();
                (Term::Apply { label, arguments }, Known::Children(known))
            }
            TermParts::Rewrite { left, right } => {
                let (left, left_known) = self.substitute(*left, bindings, settled, fresh);
                let (right, right_known) = self.substitute(*right, bindings, settled, fresh);
                (
                    Term::Rewrite {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    Known::Children(vec![left_known, right_known]),
                )
            }
            TermParts::As { pattern, alias } => {
                let (pattern, pattern_known) = self.substitute(*pattern, bindings, settled, fresh);
                let (alias, alias_known) = self.substitute(*alias, bindings, settled, fresh);
                (
                    Term::As {
                        pattern: Box::new(pattern),
                        alias: Box::new(alias),
                    },
                    Known::Children(vec![pattern_known, alias_known]),
                )
            }
            TermParts::Sequence(items) => {
                let (items, known) = items
                    .into_iter()
                    .map(|item| self.substitute(item, bindings, settled, fresh))
                    .unzip();
                (Term::Sequence(items), Known::Children(known))
            }
            leaf @ (TermParts::InjectedLabel(_) | TermParts::Token { .. }) => {
                (Term::from(leaf), Known::Unknown)
            }
            TermParts::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        let rebuilt = match metadata {
            Some(metadata) => rebuilt.with_metadata(metadata),
            None => rebuilt,
        };
        (rebuilt, known)
    }
}

/// The subterm of a matched subject each variable of a rule's left side stands for.
type Bindings<'pattern, 'subject> = BTreeMap<&'pattern str, &'subject Term>;

/// What expansion knows of a term before expanding it.
///
/// A term is settled when no subterm of it is an application or a token that some macro
/// rule of the expander has as its head: expanding it tries no rule anywhere, so it makes
/// no rewrite, mints no variable and reports nothing, whatever the rules applied above it.
/// Expansion still rebuilds every node, keeping the outermost metadata of each node on one
/// annotation layer; a result of expansion is already in that form, so expanding it again
/// gives it back unchanged. A settled result of expansion is therefore kept as it is.
///
/// The arguments of a subject are expanded before its rules are tried, so a variable of the
/// rule that matched an argument the expansion found settled is bound to a subterm of a
/// settled result, which is itself one; its copies in the rule's result are settled too
/// ([`Expander::substitute`]). Nothing else is known of the result: the right side's own
/// nodes and the other bindings are expanded as before.
enum Known {
    /// Nothing is known: the term is expanded in full.
    Unknown,
    /// The term is a settled result of expansion and is kept as it is.
    Settled,
    /// The children of the term, in the order expansion visits them, are known as listed.
    Children(Vec<Known>),
}

/// A term whose children have been expanded: the macro rules of its head when it has some,
/// and whether each child is settled ([`Known`]), in the order expansion visits them.
struct Expanded {
    term: Term,
    rules: Option<Vec<MacroRule>>,
    settled: Vec<bool>,
}

/// Move into `bindings` the subterm of `subject` that each variable of `pattern` stands for,
/// `pattern` being a left side that matched `subject`: the subterm at the variable's first
/// occurrence, the one matching bound it to.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "a left side that matched is made of applications, tokens and variables"
)]
fn take_bindings<'pattern>(
    pattern: &'pattern Term,
    subject: Term,
    bindings: &mut BTreeMap<&'pattern str, Term>,
) {
    match pattern.unannotated() {
        Term::Variable { name, .. } => {
            bindings.entry(name.as_str()).or_insert(subject);
        }
        Term::Apply {
            arguments: patterns,
            ..
        } => {
            let TermParts::Apply { arguments, .. } = subject.into_unannotated().into_parts() else {
                unreachable!("an application pattern matches only applications")
            };
            for (pattern, argument) in patterns.iter().zip(arguments) {
                take_bindings(pattern, argument, bindings);
            }
        }
        _ => {}
    }
}

/// The depth [`term_depth`] gives `pattern` with each variable named in `depths` replaced by
/// a term of that depth; the depth of a left side or right side instantiated by a match,
/// measured without recursion.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants have children"
)]
fn instance_depth(pattern: &Term, depths: &BTreeMap<&str, usize>) -> usize {
    let mut deepest = 0;
    let mut pending = vec![(pattern, 1)];
    // Invariant: `deepest` is the greatest depth of a node of the instance visited so far, a bound variable counting for its binding's deepest node, and `pending` holds every unvisited child of a visited term with its depth; each iteration visits one term of `pattern`.
    while let Some((term, depth)) = pending.pop() {
        match term.unannotated() {
            Term::Variable { name, .. } => match depths.get(name.as_str()) {
                Some(binding) => deepest = deepest.max(depth - 1 + binding),
                None => deepest = deepest.max(depth),
            },
            Term::Apply { arguments, .. } => {
                deepest = deepest.max(depth);
                pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
            }
            Term::Sequence(items) => {
                deepest = deepest.max(depth);
                pending.extend(items.iter().map(|item| (item, depth + 1)));
            }
            Term::Rewrite { left, right } => {
                deepest = deepest.max(depth);
                pending.extend([(&**left, depth + 1), (&**right, depth + 1)]);
            }
            Term::As { pattern, alias } => {
                deepest = deepest.max(depth);
                pending.extend([(&**pattern, depth + 1), (&**alias, depth + 1)]);
            }
            _ => deepest = deepest.max(depth),
        }
    }
    deepest
}

/// The variables of `pattern`, the left side of a rule, that occur in an argument `settled`
/// marks settled: after a match, each is bound to a subterm of a settled argument.
fn settled_variables<'pattern>(
    pattern: &'pattern Term,
    settled: &[bool],
) -> BTreeSet<&'pattern str> {
    fn collect<'pattern>(term: &'pattern Term, names: &mut BTreeSet<&'pattern str>) {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; only variables and their containers are visited"
        )]
        match term.unannotated() {
            Term::Variable { name, .. } => {
                names.insert(name.as_str());
            }
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
                for argument in arguments {
                    collect(argument, names);
                }
            }
            Term::Rewrite { left, right } => {
                collect(left, names);
                collect(right, names);
            }
            Term::As { pattern, alias } => {
                collect(pattern, names);
                collect(alias, names);
            }
            _ => {}
        }
    }
    let mut names = BTreeSet::new();
    if let Term::Apply { arguments, .. } = pattern.unannotated() {
        for (argument, settled) in arguments.iter().zip(settled) {
            if *settled {
                collect(argument, &mut names);
            }
        }
    }
    names
}

/// The context an application is expanded in: the rules applied above it, and the depth
/// recursive rewrites have added on its path.
type Context = (BTreeSet<usize>, usize);

/// A sentence being expanded in place, with its typing cached until a rewrite changes it.
struct Site {
    sentence: Sentence,
    position: Option<Sort>,
    typing: Option<Option<SentenceTyping>>,
    /// The number of rewrites made in the sentence so far.
    rewrites: usize,
    /// Applications whose rule set has a head fixing a sort parameter and to which no rule applied,
    /// plus macro-headed ancestors of an application rewritten by a retry, each with the rules
    /// already applied above it and the term it was.
    tried: Vec<(Vec<u32>, Context, Term)>,
    /// The context in which each surviving macro-headed application was last tried.
    applied: BTreeMap<Vec<u32>, Context>,
}

impl Site {
    fn new(sentence: Sentence) -> Self {
        Self {
            sentence,
            position: None,
            typing: None,
            rewrites: 0,
            tried: Vec::new(),
            applied: BTreeMap::new(),
        }
    }

    fn ground(term: Term, position: &Sort) -> Self {
        let mut site = Self::new(Sentence::Rule {
            body: term,
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
        site.position = Some(position.clone());
        site
    }

    /// The term at `path`, if the sentence has one there.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    fn get(&self, path: &[u32]) -> Option<&Term> {
        let mut term = *self.fields().get(*path.first()? as usize)?;
        for step in &path[1..] {
            let index = *step as usize;
            term = match term.unannotated() {
                Term::Apply { arguments, .. } => arguments.get(index)?,
                Term::Sequence(items) => items.get(index)?,
                Term::Rewrite { left, right } => [left, right].get(index)?,
                Term::As { pattern, alias } => [pattern, alias].get(index)?,
                _ => return None,
            };
        }
        Some(term)
    }

    fn fields(&self) -> [&Term; 3] {
        match &self.sentence {
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
            } => [body, requires, ensures],
            Sentence::Context { body, requires, .. } => [body, requires, requires],
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => unreachable!("a site holds a rule, claim or context"),
        }
    }

    /// The term at `path` (the field, then children as the typing view numbers them).
    fn term(&self, path: &[u32]) -> &Term {
        let mut term = self.fields()[path[0] as usize];
        for step in &path[1..] {
            term = child(term, *step as usize);
        }
        term
    }

    fn replace(&mut self, path: &[u32], replacement: Term) {
        // Ancestors survive with their own contexts; replaced applications are tried anew.
        self.applied
            .retain(|tried_path, _| !tried_path.starts_with(path));
        let field = match &mut self.sentence {
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
            } => [body, requires, ensures].into_iter().nth(path[0] as usize),
            Sentence::Context { body, requires, .. } => {
                [body, requires].into_iter().nth(path[0] as usize)
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        };
        let mut term = field.expect("a site path starts at one of its sentence's fields");
        for step in &path[1..] {
            term = child_mut(term, *step as usize);
        }
        *term = replacement;
        self.typing = None;
        self.rewrites += 1;
    }

    /// The current typing, cached until a rewrite changes it; a ground value is typed at
    /// its stored position, and a sentence uses its own typing. A typing failure leaves
    /// instances unknown until a rewrite makes the site typable.
    fn typing(&mut self, typer: &SentenceTyper<'_>) -> Option<&SentenceTyping> {
        if self.typing.is_none() {
            let typed = if let Some(position) = &self.position {
                typer.ground_typing(self.fields()[0], position)
            } else {
                match &self.sentence {
                    Sentence::Context {
                        body,
                        requires,
                        attributes,
                    } => typer.typing(&Sentence::Rule {
                        body: body.clone(),
                        requires: requires.clone(),
                        ensures: truth(),
                        attributes: attributes.clone(),
                    }),
                    sentence @ Sentence::SyntaxSort { .. }
                    | sentence @ Sentence::SortSynonym { .. }
                    | sentence @ Sentence::SyntaxLexical { .. }
                    | sentence @ Sentence::Production { .. }
                    | sentence @ Sentence::SyntaxAssociativity { .. }
                    | sentence @ Sentence::SyntaxPriority { .. }
                    | sentence @ Sentence::ContextAlias { .. }
                    | sentence @ Sentence::Rule { .. }
                    | sentence @ Sentence::Claim { .. }
                    | sentence @ Sentence::Configuration { .. }
                    | sentence @ Sentence::Bubble { .. } => typer.typing(sentence),
                }
            };
            self.typing = Some(typed.ok());
        }
        self.typing.as_ref().and_then(Option::as_ref)
    }
}

/// Parser instances belong to parsing; production instances are inferred anew at the value's
/// position. Internal labels retain the parameters that give their syntax its meaning.
fn erase_parser_instances(term: &mut Term, productions: &ProductionCatalog<'_>) {
    match term {
        Term::Annotated { term, .. } => erase_parser_instances(term, productions),
        Term::Apply { label, arguments } => {
            if production_parameters(productions, label).is_some() {
                label.parameters.clear();
            }
            for argument in arguments {
                erase_parser_instances(argument, productions);
            }
        }
        Term::InjectedLabel(label) => {
            if production_parameters(productions, label).is_some() {
                label.parameters.clear();
            }
        }
        Term::Rewrite { left, right } => {
            erase_parser_instances(left, productions);
            erase_parser_instances(right, productions);
        }
        Term::As { pattern, alias } => {
            erase_parser_instances(pattern, productions);
            erase_parser_instances(alias, productions);
        }
        Term::Sequence(items) => {
            for item in items {
                erase_parser_instances(item, productions);
            }
        }
        Term::Variable { .. } | Term::Token { .. } => {}
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn child(term: &Term, index: usize) -> &Term {
    match term.unannotated() {
        Term::Apply { arguments, .. } => &arguments[index],
        Term::Sequence(items) => &items[index],
        Term::Rewrite { left, right } => [left, right][index],
        Term::As { pattern, alias } => [pattern, alias][index],
        _ => unreachable!("a site path steps only into children"),
    }
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants are special here"
)]
fn child_mut(term: &mut Term, index: usize) -> &mut Term {
    let mut term = term;
    while let Term::Annotated { term: inner, .. } = term {
        term = inner;
    }
    match term {
        Term::Apply { arguments, .. } => &mut arguments[index],
        Term::Sequence(items) => &mut items[index],
        Term::Rewrite { left, right } => [left, right].into_iter().nth(index).unwrap(),
        Term::As { pattern, alias } => [pattern, alias].into_iter().nth(index).unwrap(),
        _ => unreachable!("a site path steps only into children"),
    }
}

/// The formal sort parameters, result sort and argument sorts of `label`'s production, when it
/// has sort parameters.
fn production_parameters<'a>(
    productions: &'a ProductionCatalog<'_>,
    label: &Label,
) -> Option<(&'a [Sort], &'a Sort, Vec<&'a Sort>)> {
    let id = productions
        .productions_for(&LabelHead::from(label))
        .first()?;
    let Sentence::Production {
        parameters,
        sort,
        items,
        ..
    } = productions.production(*id)
    else {
        return None;
    };
    (!parameters.is_empty()).then(|| {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is syntax; only the listed variants are special here"
        )]
        let arguments = items
            .iter()
            .filter_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            })
            .collect();
        (parameters.as_slice(), sort, arguments)
    })
}

/// The instance of an application a macro rule is tried on.
enum Instance {
    /// One entry per sort parameter, `None` where the typing leaves it open.
    Known(Vec<Option<Sort>>),
    /// The sentence does not type, so the instance is not known yet.
    Unknown,
}

/// A macro rule is an axiom about one instance of its head's symbol, so it applies to an
/// application only where their instances agree on every parameter both fix; an open
/// parameter agrees with every value. An unknown instance agrees only with a head that fixes
/// no parameter.
fn instances_agree(head: Option<&[Option<Sort>]>, subject: Option<&Instance>) -> bool {
    let (Some(head), Some(subject)) = (head, subject) else {
        return true;
    };
    match subject {
        Instance::Known(subject) => {
            head.len() != subject.len()
                || head.iter().zip(subject).all(|pair| match pair {
                    (Some(head), Some(subject)) => head == subject,
                    _ => true,
                })
        }
        Instance::Unknown => head.iter().all(Option::is_none),
    }
}

/// The instance of `rule`'s head, from the typing of the macro rule itself: the head is the
/// left side of the rule's top rewrite, or its body when the rewrite is nested.
fn head_instance(
    typer: &SentenceTyper<'_>,
    productions: &ProductionCatalog<'_>,
    rule: &MacroRule,
) -> Option<Vec<Option<Sort>>> {
    let Term::Apply { label, .. } = rule.left.unannotated() else {
        return None;
    };
    production_parameters(productions, label)?;
    let Sentence::Rule { body, .. } = &rule.sentence else {
        return None;
    };
    let path: &[u32] = if matches!(body.unannotated(), Term::Rewrite { .. }) {
        &[0, 0]
    } else {
        &[0]
    };
    let (parameters, ..) = production_parameters(productions, label)?;
    // A head the typing view cannot type is fixed by nothing it can see.
    Some(
        typer
            .typing(&rule.sentence)
            .ok()
            .and_then(|typing| typing.instances.get(path).cloned())
            .unwrap_or_else(|| vec![None; parameters.len()]),
    )
}

fn macro_rule(
    id: usize,
    sentence: &Sentence,
    productions: &ProductionCatalog<'_>,
) -> Option<MacroRule> {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return None;
    };
    let left = rewrite_projection(body, false);
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only the listed variants are special here"
    )]
    let production_attributes = if attributes.has(AttributeKey::Simplification) {
        None
    } else {
        match left.unannotated() {
            Term::Apply { label, .. } => productions.attributes_for(&LabelHead::from(label)),
            _ => None,
        }
    };
    if !attributes.has_any(&AttributeKey::MACRO_LIKE)
        && !production_attributes
            .is_some_and(|attributes| attributes.has_any(&AttributeKey::MACRO_LIKE))
    {
        return None;
    }
    let recursive = attributes.has(AttributeKey::MacroRec)
        || attributes.has(AttributeKey::AliasRec)
        || production_attributes.is_some_and(|attributes| {
            attributes.has(AttributeKey::MacroRec) || attributes.has(AttributeKey::AliasRec)
        });
    Some(MacroRule {
        id,
        sentence: sentence.clone(),
        left,
        right: rewrite_projection(body, true),
        recursive,
        head_instance: None,
    })
}

fn rewrite_projection(term: &Term, right: bool) -> Term {
    match term {
        Term::Annotated { term, metadata } => {
            rewrite_projection(term, right).with_metadata(metadata.clone())
        }
        Term::Rewrite {
            left,
            right: rewrite_right,
        } => rewrite_projection(if right { rewrite_right } else { left }, right),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| rewrite_projection(argument, right))
                .collect(),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(rewrite_projection(pattern, right)),
            alias: Box::new(rewrite_projection(alias, right)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| rewrite_projection(item, right))
                .collect(),
        ),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => term.clone(),
    }
}

fn sentence_roots(sentence: &Sentence) -> Vec<&Term> {
    match sentence {
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
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => Vec::new(),
    }
}

fn contains_macro_symbol(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> bool {
    let mut found = false;
    for root in sentence_roots(sentence) {
        root.visit_preorder(&mut |term| {
            if let Term::Apply { label, .. } = term.unannotated()
                && productions
                    .attributes_for(&LabelHead::from(label))
                    .is_some_and(|attributes| attributes.has_any(&AttributeKey::MACRO_LIKE))
            {
                found = true;
            }
        });
    }
    found
}

/// A macro or alias rule's place in expansion order: rules are tried by ascending rank.
///
/// A `priority` attribute names any integer, and a rule without one ranks at the default rule
/// priority. An `owise` rule applies only where no other rule of its head applies, whatever that
/// rule's priority, so it ranks after every rank a priority can name; the derived order, which
/// compares variants first, places [`MacroRank::Owise`] after every [`MacroRank::Ranked`].
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum MacroRank {
    Ranked(i64),
    Owise,
}

fn macro_priority(attributes: &Attributes) -> Result<MacroRank, Diagnostic> {
    if let Some(value) = attributes.string(AttributeKey::Priority) {
        value.parse().map(MacroRank::Ranked).map_err(|_| {
            Diagnostic::error_at(
                DiagnosticCode::InvalidMacroExpansion,
                format!("Invalid value for priority attribute: {value}. Must be an integer."),
                attributes,
            )
        })
    } else if attributes.has(AttributeKey::Owise) {
        Ok(MacroRank::Owise)
    } else {
        Ok(MacroRank::Ranked(i64::from(DEFAULT_RULE_PRIORITY)))
    }
}

/// The rewrites by `macro-rec` and `alias-rec` rules one sentence's or standalone term's
/// expansion may make before it is reported as not terminating.
///
/// Rules that are not recursive apply at most once on a path and are not counted. A terminating
/// recursive rule makes about one rewrite per node of the input it recurses over.
const MAX_RECURSIVE_REWRITES: usize = 100_000;

/// The least depth recursive rewrites may add along one path of a term before the expansion is
/// reported as not terminating; [`growth_allowance`] raises it to the depth of the input.
const MIN_RECURSIVE_GROWTH: usize = 1_000;

/// The depth recursive rewrites may add along one path of a term `input_depth` deep.
///
/// A recursion over its input adds about as much depth as it consumes: rebuilding a list in
/// reverse adds half the list's depth, doubling a numeral its depth. Allowing the larger of the
/// input's depth and [`MIN_RECURSIVE_GROWTH`] admits such recursion over any input, and still
/// ends a divergence that deepens the term after a number of steps in proportion to the input.
fn growth_allowance(input_depth: usize) -> usize {
    MIN_RECURSIVE_GROWTH.max(input_depth)
}

/// Bytes of native stack the recursive walks over one level of a term may take: cloning,
/// comparing, matching, and the sort-injection typing of a sentence with a parametric macro
/// head, the deepest of them at about 2 KiB per level in an unoptimized build.
#[cfg(not(target_family = "wasm"))]
const STACK_PER_LEVEL: usize = 2 * 1024;

/// The stack that must remain on entering one level of the expansion of a term `input_depth`
/// deep: enough for a walk over the deepest term the expansion may hold, the input plus what
/// recursive rewrites may add ([`growth_allowance`]), with a factor of two to spare.
#[cfg(not(target_family = "wasm"))]
fn stack_zone(input_depth: usize) -> usize {
    2 * STACK_PER_LEVEL * (input_depth + growth_allowance(input_depth))
}

#[cfg(target_family = "wasm")]
fn stack_zone(_: usize) -> usize {
    0
}

/// The depth of the deepest term of any sentence of `definition`, measured without recursion.
fn definition_depth(definition: &Definition) -> usize {
    definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .map(|sentence| sentence_depth(sentence))
        .max()
        .unwrap_or(0)
}

/// The depth of the deepest of the body, requires and ensures of a rule, claim or context, and
/// 0 for any other sentence, measured without recursion.
fn sentence_depth(sentence: &Sentence) -> usize {
    sentence_roots(sentence)
        .into_iter()
        .map(term_depth)
        .max()
        .unwrap_or(0)
}

/// The root rewrites of one application, each made to the expanded result of the one before.
///
/// `repeats` stores one subject at a time as Brent's cycle-finding algorithm does: the stored
/// subject is replaced after 1, 2, 4, ... further steps, so a chain that enters a cycle of
/// length λ after μ steps meets its stored subject again within 2(μ + λ) steps.
struct Chain {
    /// The stored subject, the number of rules applied above it, and its depth.
    checkpoint: Option<(Term, usize, usize)>,
    /// Steps after which the stored subject is replaced.
    power: usize,
    /// Steps since the stored subject was stored.
    steps: usize,
}

impl Default for Chain {
    fn default() -> Self {
        Self {
            checkpoint: None,
            power: 1,
            steps: 0,
        }
    }
}

impl Chain {
    /// Whether `subject`, `depth` deep and about to be rewritten under `applied` applied rules,
    /// is the stored subject under as many; otherwise count the step and store `subject` when
    /// its turn comes. Equal terms are equally deep, so the terms are compared only when their
    /// depths are equal.
    fn repeats(&mut self, subject: &Term, applied: usize, depth: usize) -> bool {
        if self
            .checkpoint
            .as_ref()
            .is_some_and(|(stored, count, stored_depth)| {
                *count == applied && *stored_depth == depth && stored == subject
            })
        {
            return true;
        }
        self.steps += 1;
        if self.steps >= self.power {
            self.checkpoint = Some((subject.clone(), applied, depth));
            self.power = self.power.saturating_mul(2);
            self.steps = 0;
        }
        false
    }
}

/// Bytes of each stack segment allocated when less than the red zone remains, beyond the red
/// zone itself; pages are committed only as they are used.
#[cfg(not(target_family = "wasm"))]
const STACK_SEGMENT: usize = 32 * 1024 * 1024;

/// Run `work` with at least `red_zone` bytes of native stack, on a fresh heap-allocated
/// segment when the current one has less, so that expansion and the walks over the terms it
/// holds cannot overflow the native stack. On wasm32 the engine's stack limit is invisible to
/// the module and `work` runs directly.
#[inline]
fn with_stack<T>(red_zone: usize, work: impl FnOnce() -> T) -> T {
    #[cfg(not(target_family = "wasm"))]
    {
        stacker::maybe_grow(red_zone, red_zone + STACK_SEGMENT, work)
    }
    #[cfg(target_family = "wasm")]
    {
        let _ = red_zone;
        work()
    }
}

/// The number of terms on the longest path from `term` to a leaf, counted without recursion so
/// that a term of any depth can be measured.
///
/// A `macro-rec` or `alias-rec` rewrite measures its bindings with this walk, so it is written
/// with plain loops: iterator adapters made it several times slower in unoptimized builds,
/// where the test suite runs.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is syntax; only the listed variants have children"
)]
fn term_depth(term: &Term) -> usize {
    let mut deepest = 0;
    let mut pending = vec![(term, 1)];
    // Invariant: `deepest` is the greatest depth of a term visited so far, and `pending` holds every unvisited child of a visited term with its depth; each iteration visits one term.
    while let Some((term, depth)) = pending.pop() {
        if depth > deepest {
            deepest = depth;
        }
        let children: &[Term] = match term.unannotated() {
            Term::Apply { arguments, .. } => arguments,
            Term::Sequence(items) => items,
            Term::Rewrite { left, right } => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
                continue;
            }
            Term::As { pattern, alias } => {
                pending.push((pattern, depth + 1));
                pending.push((alias, depth + 1));
                continue;
            }
            _ => continue,
        };
        for child in children {
            pending.push((child, depth + 1));
        }
    }
    deepest
}

/// `term` as K text for a diagnostic, shortened to its first 120 characters.
fn shown(term: &Term) -> String {
    let text = term.to_string();
    match text.char_indices().nth(120) {
        Some((end, _)) => format!("{}...", &text[..end]),
        None => text,
    }
}

fn with_metadata(term: Term, metadata: Option<crate::kast::TermMetadata>) -> Term {
    match metadata {
        Some(metadata) => term.with_metadata(metadata),
        None => term,
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn plain_error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        severity: Severity::Error,
        code: DiagnosticCode::InvalidMacroExpansion,
        message: message.into(),
        source: None,
        location: None,
        input_addresses: Vec::new(),
    }
}

fn located_at(mut diagnostic: Diagnostic, sentence: &Sentence) -> Diagnostic {
    if diagnostic.source.is_none() && diagnostic.location.is_none() {
        diagnostic.source = sentence.attributes().source().map(str::to_owned);
        diagnostic.location = sentence.attributes().location();
        if diagnostic.input_addresses.is_empty() {
            diagnostic.input_addresses = sentence.attributes().input_addresses().to_vec();
        }
    }
    diagnostic
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;
    use crate::definition::ProductionItem;
    use serde_json::{Value, json};

    fn attrs(entries: &[(&str, Value)]) -> Attributes {
        Attributes::new(
            entries
                .iter()
                .map(|(key, value)| ((*key).into(), value.clone()))
                .collect::<BTreeMap<_, _>>(),
        )
    }

    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        }
    }

    fn production(
        label: Option<&str>,
        sort: &str,
        arguments: &[&str],
        attributes: Attributes,
    ) -> Sentence {
        Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items: arguments
                .iter()
                .map(|argument| ProductionItem::NonTerminal {
                    sort: Sort::new(*argument),
                    name: None,
                })
                .collect(),
            attributes,
        }
    }

    #[test]
    fn smt_lemma_terms_require_smt_backed_visible_productions() {
        let good = production(
            Some("good"),
            "Bool",
            &["Bool"],
            attrs(&[("smt-hook", json!("good"))]),
        );
        let bad = production(Some("bad"), "Bool", &[], Attributes::default());
        let rule = Sentence::Rule {
            body: Term::apply(
                "good",
                vec![
                    Term::apply("bad", Vec::new()),
                    Term::apply("unknown", Vec::new()),
                ],
            ),
            requires: truth(),
            ensures: truth(),
            attributes: attrs(&[("smt-lemma", json!(""))]),
        };
        let productions = ProductionCatalog::from_visible([&good, &bad]);
        let diagnostics = check_smt_lemmas(&[&rule], &productions);

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, DiagnosticCode::InvalidSmtLemma);
    }
}
