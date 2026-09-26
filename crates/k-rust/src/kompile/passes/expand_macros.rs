//! ```toml algorithm
//! id = "kompile.macros.expand"
//! name = "macro expansion by indexed structural matching"
//! sites = ["expand_macros", "expand_macros_pass", "Expander::expand_sentence", "Expander::expand_term", "Expander::expand_site", "Expander::expand_at", "Expander::try_rules", "Expander::new"]
//! variable = "N = sentence term nodes, on the largest intermediate sentence for the typed mode; R = macro rules under the head label; A = macro applications; V = sentences visible in the macro module; Q = macro rules in the module; h = sentence term height; W = macro rewrites made in the sentence; T = one SentenceTyper::typing of a sentence (kompile.sort_injections.insert)"
//! counters = ["KompileMacroApplications"]
//!
//! [[cost]]
//! mode = "one sentence, no macro rule with a parametric head"
//! bound = "O(N x R) plus recursive expansion of substituted results"
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
//! With a macro rule whose head production has sort parameters, a sentence is expanded in place (`Expander::expand_site`): an application's instance is read from the typing of the sentence as it stands, which is recomputed at most once per rewrite, and applications left untyped are retried in rounds until a round rewrites nothing.
//! A round without a rewrite ends the retries, so there are at most W + 1 rounds and W + 1 typings; each round and each re-expansion of a substituted result clones and compares subterms along paths of length at most h.
//!
//! This transformation pass resolves required views, transforms sentences and terms, records origins, and retargets metadata when needed.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Expand compile-time macro and alias rules by structural matching.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust_kore::measure::{self, Counter};

use crate::definition::AttributeKey;
use crate::names::BuiltinSort;
use crate::{
    definition::{
        Attributes, Definition, DefinitionViews, LabelHead, ModuleId, ProductionCatalog,
        ResolvedDefinition, Sentence, SortCatalog,
        checks::{self, check_functions_with_internal_labels, check_smt_lemmas},
    },
    diagnostic::{Diagnostic, DiagnosticCode, Severity},
    kast::{Label, Sort, Term},
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
pub fn expand_macros(definition: &Definition) -> Result<Definition, ExpandMacrosError> {
    super::super::pipeline::run_standalone(
        definition,
        expand_macros_pass,
        Some(GeneratingPass::MacroExpansion),
    )
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
            let sentence = crate::definition::sentence_mut(sentence);
            if matches!(sentence, Sentence::Rule { attributes, .. } if attributes.has_any(&AttributeKey::MACRO_LIKE))
            {
                continue;
            }
            if matches!(
                sentence,
                Sentence::Rule { .. } | Sentence::Claim { .. } | Sentence::Context { .. }
            ) {
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
                        if matches!(sentence, Sentence::Rule { .. } | Sentence::Claim { .. })
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
            }
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

/// Expand macros in a term parsed outside the definition, such as a program or
/// configuration-variable value.
///
/// Definition compilation expands sentence bodies, but concrete programs are parsed only after
/// that pipeline has finished. They must use the same propagated macro rules before sort
/// injection and KORE conversion.
pub fn expand_macros_in_term(
    definition: &Definition,
    module: &str,
    term: Term,
) -> Result<Term, String> {
    expand_macros_in_term_with_scope(definition, module, module, term)
}

/// Expand a standalone term parsed in one module with another module's executable syntax.
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
    term: Term,
) -> Result<Term, String> {
    MacroExpansionDefinition::prepare(definition)?.expand_term(macro_module, term)
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

    /// Expand the macros of `macro_module` in one standalone term.
    ///
    /// Each call builds its own expander and fresh-name allocator, so the result of one call
    /// does not depend on the terms expanded by earlier calls.
    pub fn expand_term(&self, macro_module: &str, term: Term) -> Result<Term, String> {
        let views = self.resolved.views();
        let mut expanded = expand_macros_in_terms_from_views_with_scope(
            &views,
            macro_module,
            macro_module,
            vec![term],
        )
        .map_err(|diagnostic| diagnostic.message)?;
        Ok(expanded
            .terms
            .pop()
            .expect("one input term produces one expanded term"))
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
            _ => None,
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
    terms: Vec<Term>,
) -> Result<ExpandedMacroTerms, String> {
    let views = definition.views();
    expand_macros_in_terms_from_views_with_scope(&views, module, module, terms)
        .map_err(|diagnostic| diagnostic.message)
}

fn expand_macros_in_terms_from_views_with_scope(
    views: &DefinitionViews<'_>,
    term_module: &str,
    macro_module: &str,
    terms: Vec<Term>,
) -> Result<ExpandedMacroTerms, Diagnostic> {
    let definition = views.definition();
    let term_module = definition
        .module_id(term_module)
        .ok_or_else(|| plain_error(format!("unknown module {term_module}")))?;
    let macro_module = definition
        .module_id(macro_module)
        .ok_or_else(|| plain_error(format!("unknown module {macro_module}")))?;
    let mut expander = Expander::new(views, term_module, macro_module)?;
    expander.fresh = FreshNames::for_terms(terms.iter());
    let terms = terms
        .into_iter()
        .map(|term| expander.expand_standalone(term))
        .collect::<Result<Vec<_>, _>>()?;
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
}

impl<'view, 'definition> Expander<'view, 'definition> {
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
        })
    }

    fn expand_sentence(&mut self, sentence: Sentence) -> Result<Sentence, Diagnostic> {
        self.fresh = FreshNames::for_sentence(&sentence);
        self.generated.clear();
        if self.typer.is_some() {
            let fields: &[u32] = match &sentence {
                Sentence::Rule { .. } | Sentence::Claim { .. } => &[0, 1, 2],
                Sentence::Context { .. } => &[0, 1],
                _ => return Ok(sentence),
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
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                ensures: self.expand_term(ensures, &BTreeSet::new())?,
                attributes,
            }),
            Sentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            } => Ok(Sentence::Claim {
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                ensures: self.expand_term(ensures, &BTreeSet::new())?,
                attributes,
            }),
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Ok(Sentence::Context {
                body: self.expand_term(body, &BTreeSet::new())?,
                requires: self.expand_term(requires, &BTreeSet::new())?,
                attributes,
            }),
            sentence => Ok(sentence),
        }
    }

    fn expand_term(&mut self, term: Term, applied: &BTreeSet<usize>) -> Result<Term, Diagnostic> {
        let metadata = term.metadata().cloned();
        match term.into_unannotated() {
            Term::Apply { label, arguments } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.expand_term(argument, applied))
                    .collect::<Result<Vec<_>, _>>()?;
                let application = with_metadata(
                    Term::Apply {
                        label: label.clone(),
                        arguments,
                    },
                    metadata,
                );
                let rules = self.macros.get(&LabelHead::from(&label)).cloned();
                self.apply_rules(application, rules.as_deref(), applied)
            }
            Term::Token { token, sort } => {
                let token = with_metadata(
                    Term::Token {
                        token,
                        sort: sort.clone(),
                    },
                    metadata,
                );
                let rules = self.token_macros.get(&sort).cloned();
                self.apply_rules(token, rules.as_deref(), applied)
            }
            Term::Rewrite { left, right } => Ok(with_metadata(
                Term::Rewrite {
                    left: Box::new(self.expand_term(*left, applied)?),
                    right: Box::new(self.expand_term(*right, applied)?),
                },
                metadata,
            )),
            Term::As { pattern, alias } => Ok(with_metadata(
                Term::As {
                    pattern: Box::new(self.expand_term(*pattern, applied)?),
                    alias: Box::new(self.expand_term(*alias, applied)?),
                },
                metadata,
            )),
            Term::Sequence(items) => Ok(with_metadata(
                Term::Sequence(
                    items
                        .into_iter()
                        .map(|item| self.expand_term(item, applied))
                        .collect::<Result<_, _>>()?,
                ),
                metadata,
            )),
            leaf @ (Term::InjectedLabel(_) | Term::Variable { .. }) => {
                Ok(with_metadata(leaf, metadata))
            }
            Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        }
    }

    fn apply_rules(
        &mut self,
        subject: Term,
        rules: Option<&[MacroRule]>,
        applied: &BTreeSet<usize>,
    ) -> Result<Term, Diagnostic> {
        let Some(rules) = rules else {
            return Ok(subject);
        };
        match self.select_rule(&subject, rules, applied, None)? {
            Some((id, substituted)) => {
                let mut next_applied = applied.clone();
                next_applied.insert(id);
                self.expand_term(substituted, &next_applied)
            }
            None => Ok(subject),
        }
    }

    /// The first rule of `rules` that applies to `subject` (its head instance agreeing with
    /// `instance`, its left side matching, and it recursive or absent from `applied`), with its
    /// substituted right side.
    fn select_rule(
        &mut self,
        subject: &Term,
        rules: &[MacroRule],
        applied: &BTreeSet<usize>,
        instance: Option<&Instance>,
    ) -> Result<Option<(usize, Term)>, Diagnostic> {
        // Invariant: no rule of `rules` before `rule` both matched `subject` and was recursive or absent from `applied`; each iteration consumes one element of the finite slice `rules`, and the first applicable rule is returned with its substituted right side.
        for rule in rules {
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
            let mut substitution = BTreeMap::new();
            let matched = self.matches(&mut substitution, &rule.left, subject)?;
            if matched && (rule.recursive || !applied.contains(&rule.id)) {
                measure::bump(Counter::KompileMacroApplications);
                let substituted = self.substitute(rule.right.clone(), &mut substitution);
                return Ok(Some((rule.id, substituted)));
            }
        }
        Ok(None)
    }

    /// Expand a term parsed outside the definition. With a parametric macro head it is expanded
    /// as the body of a rule, so that its positions are typed as compilation types a rule body.
    fn expand_standalone(&mut self, term: Term) -> Result<Term, Diagnostic> {
        if self.typer.is_none() {
            return self.expand_term(term, &BTreeSet::new());
        }
        let mut site = Site::new(Sentence::Rule {
            body: term,
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
        self.expand_site(&mut site, &[0])?;
        let Sentence::Rule { body, .. } = site.sentence else {
            unreachable!("the site holds the rule it was built from")
        };
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
    ) -> Result<(), Diagnostic> {
        let children = match site.term(path).unannotated() {
            Term::Apply { arguments, .. } => arguments.len(),
            Term::Sequence(items) => items.len(),
            Term::Rewrite { .. } | Term::As { .. } => 2,
            _ => 0,
        };
        let rewrites = site.rewrites;
        for index in 0..children {
            let mut child = path.to_vec();
            child.push(u32::try_from(index).expect("a term has fewer than 2^32 children"));
            self.expand_at(site, &child, applied)?;
        }
        self.try_rules(site, path, applied, site.rewrites == rewrites)
    }

    /// Expand the given fields of `site`, then retry, until no retry rewrites anything, the
    /// applications whose instance was unknown because the sentence did not type: a later
    /// rewrite can make it typable. An application still unknown at the fixpoint is left as it
    /// is, and compilation reports the ill-sorted sentence at injection.
    fn expand_site(&mut self, site: &mut Site, fields: &[u32]) -> Result<(), Diagnostic> {
        for field in fields {
            self.expand_at(site, &[*field], &BTreeSet::new())?;
        }
        // Invariant: `site.pending` holds the applications, with their paths, applied rule sets, and terms, whose instance was unknown when their rules were tried because the sentence did not type, plus the macro-headed ancestors of an application rewritten in the previous round; every earlier round rewrote the sentence at least once, and a round without a rewrite ends the loop.
        while !site.pending.is_empty() {
            let rewrites = site.rewrites;
            for (path, applied, subject) in std::mem::take(&mut site.pending) {
                // A pending application inside a subtree a later rewrite replaced is gone.
                if site.get(&path) != Some(&subject) {
                    continue;
                }
                let before = site.rewrites;
                self.try_rules(site, &path, &applied, false)?;
                if site.rewrites != before {
                    // Its enclosing applications were tried before it was expanded.
                    for length in (1..path.len()).rev() {
                        let ancestor = path[..length].to_vec();
                        if let Some(term @ Term::Apply { label, .. }) =
                            site.get(&ancestor).map(Term::unannotated)
                            && self.macros.contains_key(&LabelHead::from(label))
                        {
                            let term = term.clone();
                            site.pending.push((ancestor, applied.clone(), term));
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
    /// expanded; `unchanged` when no rewrite happened below it since it was parsed or built.
    fn try_rules(
        &mut self,
        site: &mut Site,
        path: &[u32],
        applied: &BTreeSet<usize>,
        unchanged: bool,
    ) -> Result<(), Diagnostic> {
        let subject = site.term(path).clone();
        let (rules, instance) = match subject.unannotated() {
            Term::Apply { label, .. } => {
                let Some(rules) = self.macros.get(&LabelHead::from(label)).cloned() else {
                    return Ok(());
                };
                let instance = if rules.iter().any(|rule| rule.head_instance.is_some()) {
                    Some(self.subject_instance(site, path, &subject, unchanged))
                } else {
                    None
                };
                (rules, instance)
            }
            Term::Token { sort, .. } => match self.token_macros.get(sort).cloned() {
                Some(rules) => (rules, None),
                None => return Ok(()),
            },
            _ => return Ok(()),
        };
        if let Some((id, substituted)) =
            self.select_rule(&subject, &rules, applied, instance.as_ref())?
        {
            site.replace(path, substituted);
            let mut next_applied = applied.clone();
            next_applied.insert(id);
            self.expand_at(site, path, &next_applied)?;
        } else if matches!(instance, Some(Instance::Unknown))
            && rules.iter().any(|rule| {
                rule.head_instance
                    .as_ref()
                    .is_some_and(|head| head.iter().any(Option::is_some))
            })
        {
            site.pending.push((path.to_vec(), applied.clone(), subject));
        }
        Ok(())
    }

    /// The instance of the application `subject` at `path`: the one it was parsed with while
    /// nothing below it has been rewritten, else the one the typing of the sentence gives it.
    fn subject_instance(
        &self,
        site: &mut Site,
        path: &[u32],
        subject: &Term,
        unchanged: bool,
    ) -> Instance {
        let Term::Apply { label, .. } = subject.unannotated() else {
            return Instance::Unknown;
        };
        if unchanged && !label.parameters.is_empty() {
            return Instance::Known(label.parameters.iter().cloned().map(Some).collect());
        }
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

    fn matches(
        &self,
        substitution: &mut BTreeMap<String, Term>,
        pattern: &Term,
        subject: &Term,
    ) -> Result<bool, Diagnostic> {
        let metadata_sort = pattern
            .metadata()
            .and_then(|metadata| metadata.sort.as_ref());
        match pattern.unannotated() {
            Term::Variable { name, sort } => {
                if let Some(existing) = substitution.get(name) {
                    return Ok(existing == subject);
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
                substitution.insert(name.clone(), subject.clone());
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
                    if !self.matches(substitution, pattern, subject)? {
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

    fn substitute(&mut self, term: Term, substitution: &mut BTreeMap<String, Term>) -> Term {
        let metadata = term.metadata().cloned();
        let rebuilt = match term.into_unannotated() {
            Term::Variable { name, sort } => {
                if let Some(term) = substitution.get(&name) {
                    return term.clone();
                }
                if name == "#Configuration" {
                    Term::Variable { name, sort }
                } else {
                    let generated_name = self.fresh.mint("_Gen");
                    self.generated
                        .insert(GeneratedVariableIdentity::element(generated_name.clone()));
                    let variable = Term::Variable {
                        name: generated_name,
                        sort,
                    };
                    substitution.insert(name, variable.clone());
                    variable
                }
            }
            Term::Apply { label, arguments } => Term::Apply {
                label,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.substitute(argument, substitution))
                    .collect(),
            },
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.substitute(*left, substitution)),
                right: Box::new(self.substitute(*right, substitution)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.substitute(*pattern, substitution)),
                alias: Box::new(self.substitute(*alias, substitution)),
            },
            Term::Sequence(items) => Term::Sequence(
                items
                    .into_iter()
                    .map(|item| self.substitute(item, substitution))
                    .collect(),
            ),
            leaf @ (Term::InjectedLabel(_) | Term::Token { .. }) => leaf,
            Term::Annotated { .. } => unreachable!("into_unannotated strips metadata"),
        };
        match metadata {
            Some(metadata) => rebuilt.with_metadata(metadata),
            None => rebuilt,
        }
    }
}

/// A sentence being expanded in place, with its typing cached until a rewrite changes it.
struct Site {
    sentence: Sentence,
    typing: Option<Option<SentenceTyping>>,
    /// The number of rewrites made in the sentence so far.
    rewrites: usize,
    /// Applications no rule applied to because the sentence did not type, with the rules
    /// already applied above them and the term they were.
    pending: Vec<(Vec<u32>, BTreeSet<usize>, Term)>,
}

impl Site {
    fn new(sentence: Sentence) -> Self {
        Self {
            sentence,
            typing: None,
            rewrites: 0,
            pending: Vec::new(),
        }
    }

    /// The term at `path`, if the sentence has one there.
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
            _ => unreachable!("a site holds a rule, claim or context"),
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
            _ => None,
        };
        let mut term = field.expect("a site path starts at one of its sentence's fields");
        for step in &path[1..] {
            term = child_mut(term, *step as usize);
        }
        *term = replacement;
        self.typing = None;
        self.rewrites += 1;
    }

    /// The typing of the sentence as it stands; `None` when the typing view rejects it, which
    /// leaves every instance open. A parsed program's labels carry the parser's instances, which
    /// the typing view rejects as written parameters; it types a copy without them, and the
    /// instance of an application whose arguments are unchanged is read from its own label.
    fn typing(&mut self, typer: &SentenceTyper<'_>) -> Option<&SentenceTyping> {
        if self.typing.is_none() {
            let mut sentence = self.sentence.clone();
            erase_label_parameters(&mut sentence);
            let typed = match &sentence {
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
                sentence => typer.typing(sentence),
            };
            self.typing = Some(typed.ok());
        }
        self.typing.as_ref().and_then(Option::as_ref)
    }
}

/// Clear the sort parameters of every label in `sentence`'s terms.
fn erase_label_parameters(sentence: &mut Sentence) {
    fn erase(term: &mut Term) {
        match term {
            Term::Annotated { term, .. } => erase(term),
            Term::Apply { label, arguments } => {
                label.parameters.clear();
                arguments.iter_mut().for_each(erase);
            }
            Term::InjectedLabel(label) => label.parameters.clear(),
            Term::Rewrite { left, right } => {
                erase(left);
                erase(right);
            }
            Term::As { pattern, alias } => {
                erase(pattern);
                erase(alias);
            }
            Term::Sequence(items) => items.iter_mut().for_each(erase),
            Term::Variable { .. } | Term::Token { .. } => {}
        }
    }
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
        } => [body, requires, ensures].into_iter().for_each(erase),
        Sentence::Context { body, requires, .. } => [body, requires].into_iter().for_each(erase),
        _ => {}
    }
}

fn child(term: &Term, index: usize) -> &Term {
    match term.unannotated() {
        Term::Apply { arguments, .. } => &arguments[index],
        Term::Sequence(items) => &items[index],
        Term::Rewrite { left, right } => [left, right][index],
        Term::As { pattern, alias } => [pattern, alias][index],
        _ => unreachable!("a site path steps only into children"),
    }
}

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
        _ => Vec::new(),
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

fn macro_priority(attributes: &Attributes) -> Result<i64, Diagnostic> {
    if let Some(value) = attributes.string(AttributeKey::Priority) {
        value.parse().map_err(|_| {
            Diagnostic::error_at(
                DiagnosticCode::InvalidMacroExpansion,
                format!("Invalid value for priority attribute: {value}. Must be an integer."),
                attributes,
            )
        })
    } else if attributes.has(AttributeKey::Owise) {
        Ok(200)
    } else {
        Ok(50)
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
