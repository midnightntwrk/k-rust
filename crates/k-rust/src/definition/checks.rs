//! ```toml algorithm
//! id = "definition.checks.run"
//! name = "structural checking of resolved definitions"
//! sites = ["check_definition_with_options", "check_module_with_options"]
//! variable = "M = modules; S = visited sentences and terms; P = visible parametric token declarations"
//! counters = []
//! no_counter = "structural definition checks have no dedicated counter"
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(M x (S x (P + 1) + catalog work))"
//! ```
//!
//! Structural definition checking composes Java-compatible per-module checks over resolved catalogs.
//! Complexity: O(M(S(P + 1) + catalog work)) over modules and their sentences.
//! Token admission can match each token against visible parametric token declarations; no dedicated counter.
//!
//! Dependency-light structural checks ported from the Java frontend.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use super::ast::{ProductionItem, Sentence};
use super::catalog::LabelHead;
use super::partial_order::{Cycle, PartialOrder};
use super::resolve::{ModuleId, ResolvedDefinition};
use super::sort_catalog::SortCatalog;
use super::views::DefinitionViews;
use crate::definition::AttributeKey;
use crate::definition::production_kind::ResultSorts;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Sort, SortRole, Term};

mod attributes;
mod collections;
mod deprecated;
mod fresh_variables;
mod functions;
mod kompile_checks;
mod label_parameters;
mod labels;
mod production_shapes;
mod regexes;
mod rhs_variables;
mod sorts;
mod term_position;

pub use attributes::{check_attribute_semantics, check_attributes};
pub use deprecated::check_deprecated_productions;
pub use functions::check_functions;
pub(crate) use functions::check_functions_with_internal_labels;
pub use kompile_checks::{
    check_claims_in_definition, check_is_sort_predicates, check_proof_module,
};
use kompile_checks::{check_is_sort_predicates_with_views, check_proof_module_with_views};
pub(crate) use label_parameters::{
    LabelParameterError, SentenceLabelParameterError, reject_label_parameters,
    reject_label_parameters_in_definition,
};
pub(crate) use labels::internal_labels;
pub use labels::{
    check_duplicate_klabels, check_duplicate_overloads, check_function_rule_attributes,
    check_klabels, check_singleton_overloads, check_unused_symbols,
};
use labels::{
    check_duplicate_overloads_with_views, check_function_rule_attributes_with_views,
    check_unused_symbols_with_views,
};
pub use production_shapes::{check_configuration_cells, check_holes, check_streams};
pub use regexes::check_regexes;
pub use rhs_variables::{
    CheckMode, StructuralCheckBackend, StructuralCheckOptions, check_rhs_variables,
};
#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
pub(crate) use rhs_variables::{CheckedRoot, right_hand_side_binding};
pub(crate) use rhs_variables::{FreeVariable, local_function_free_variables};
pub(crate) use sorts::kernel_position_cycle;
pub(crate) use sorts::rule_grammar_subsorts;
pub use sorts::{check_outer_modules, check_sort_synonyms, check_sorts, check_user_lists};

const ALLOWED_TOKEN_ATTRIBUTES: [AttributeKey; 3] = [
    AttributeKey::Function,
    AttributeKey::Token,
    AttributeKey::Bracket,
];
const IGNORED_TOKEN_SORTS: [&str; 2] =
    [FrontendSort::KBott.as_str(), FrontendSort::KLabel.as_str()];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    CircularSubsort(Cycle<Sort>),
    CircularPriority(Cycle<String>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircularSubsort(error) => error.fmt(formatter),
            Self::CircularPriority(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for Error {}

/// Run the implemented dependency-light structural checks over local sentences.
pub fn check_module(
    definition: &ResolvedDefinition,
    module: ModuleId,
) -> Result<Vec<Diagnostic>, Error> {
    check_module_with_options(definition, module, StructuralCheckOptions::default())
}

pub fn check_module_with_options(
    definition: &ResolvedDefinition,
    module: ModuleId,
    options: StructuralCheckOptions,
) -> Result<Vec<Diagnostic>, Error> {
    let views = definition.views();
    let sort_catalog = views.sort_catalog(module);
    check_module_with_options_and_catalog(&views, module, options, sort_catalog)
}

fn check_module_with_options_and_catalog(
    views: &DefinitionViews<'_>,
    module: ModuleId,
    options: StructuralCheckOptions,
    sort_catalog: &SortCatalog<'_>,
) -> Result<Vec<Diagnostic>, Error> {
    let definition = views.definition();
    let sentences = definition
        .module(module)
        .local_sentences
        .iter()
        .map(std::sync::Arc::as_ref)
        .collect::<Vec<_>>();
    let subsorts = views
        .subsorts(module)
        .map_err(|error| Error::CircularSubsort(error.clone()))?;
    let priorities = views
        .priorities(module)
        .map_err(|error| Error::CircularPriority(error.clone()))?;
    let production_catalog = views.production_catalog(module);
    let overloads = views.overloads(module).ok();
    let rule_catalog = definition.rule_catalog(module);
    let macro_labels = rule_catalog.all_macro_labels(production_catalog);
    let associativity = if local_associativity(&sentences) {
        check_associativity_by(&sentences, |below, above| {
            grammar_admits(views, module, below, above)
        })
    } else {
        Vec::new()
    };
    let mut diagnostics = check_attributes(definition.module(module))
        .into_iter()
        .chain(check_duplicate_labels(&sentences))
        .chain(check_syntax_groups(&sentences, priorities))
        .chain(associativity)
        .chain(check_sort_top_uniqueness(&sentences, subsorts))
        .chain(check_holes(&sentences))
        .chain(check_streams(&sentences, subsorts))
        .chain(check_configuration_cells(&sentences, production_catalog))
        .chain(collections::check_collection_productions(
            &sentences,
            production_catalog,
            sort_catalog,
        ))
        .chain(check_tokens(&sentences, sort_catalog, &macro_labels))
        .chain(check_domain_value_tokens(&sentences, sort_catalog))
        .chain(check_k_terms(&sentences))
        .chain(check_rewrites(&sentences))
        .chain(check_anonymous_variables(&sentences))
        .chain(check_rhs_variables(&sentences, options.clone()))
        .chain(fresh_variables::check_fresh_variables(
            &sentences,
            production_catalog,
        ))
        .chain(check_functions(
            &sentences,
            production_catalog,
            sort_catalog,
        ))
        .chain(check_klabels(&sentences, production_catalog, sort_catalog))
        .chain(attributes::check_attribute_semantics_with_overloads(
            &sentences,
            production_catalog,
            sort_catalog,
            overloads,
        ))
        .chain(check_deprecated_productions(&sentences, production_catalog))
        // Java validates SMT lemmas from `ExpandMacros`, after aliases and macros have been
        // removed from rule bodies. Checking here rejects valid lemmas that still contain an
        // alias whose expansion uses only SMT-backed symbols.
        .chain(check_regexes(&sentences, &definition.sentences(module)))
        .collect::<Vec<_>>();
    diagnostics.sort();
    Ok(diagnostics)
}

/// Run all implemented structural checks across a resolved definition.
pub fn check_definition(definition: &ResolvedDefinition) -> Result<Vec<Diagnostic>, Error> {
    check_definition_with_options(definition, StructuralCheckOptions::default())
}

pub fn check_definition_with_options(
    definition: &ResolvedDefinition,
    options: StructuralCheckOptions,
) -> Result<Vec<Diagnostic>, Error> {
    let views = definition.views();
    let mut diagnostics = Vec::new();
    diagnostics.extend(check_claims_in_definition(definition, &options));
    diagnostics.extend(check_proof_module_with_views(&views, &options));
    diagnostics.extend(check_is_sort_predicates_with_views(&views, &options));
    for (module_id, module) in definition.modules() {
        let visible = definition.sentences(module_id);
        let sort_catalog = views.sort_catalog(module_id);
        diagnostics.extend(check_sorts(module, sort_catalog));
        diagnostics.extend(check_user_lists(module, &visible));
        diagnostics.extend(check_module_with_options_and_catalog(
            &views,
            module_id,
            options.clone(),
            sort_catalog,
        )?);
    }
    let compiled = check_compiled_view_productions(&views);
    let reported = diagnostics.iter().cloned().collect::<BTreeSet<_>>();
    diagnostics.extend(
        compiled
            .into_iter()
            .filter(|diagnostic| !reported.contains(diagnostic)),
    );
    diagnostics.extend(check_sort_synonyms(definition));
    diagnostics.extend(check_duplicate_klabels(definition));
    diagnostics.extend(check_unused_symbols_with_views(&views, &options));
    diagnostics.extend(check_duplicate_overloads_with_views(&views));
    diagnostics.extend(check_function_rule_attributes_with_views(&views));
    diagnostics.sort();
    Ok(diagnostics)
}

/// The checks that judge a sentence by a property of the compiled definition, run over every
/// module the main module imports, against the main module's view.
///
/// - Whether a sort is hooked or has domain values is fixed by its declarations anywhere in the
///   compiled definition, and a module that declares a production on the sort need not import
///   the module that hooks it or declares its tokens (token productions, hooked constructors).
/// - The symbol a collection attribute (`element`, `update`, `wrapElement`, `unit`) names, and
///   the collection hook of the sort whose unit it names, are the compiled definition's: a module
///   may name a production or rely on a hook declared in a module it does not import, which the
///   compiled definition resolves (collection productions).
/// - The subsort order is the compiled definition's: a module may place a sort below both `KList`
///   and `Bag` in subsorts declared outside the module that declares the sort (top sorts).
///
/// The per-module checks see only the declaring module's view, where the sentence passes; the
/// compiled definition is emitted from the main module's view, which contains the view of every
/// module it imports, so it is the one view this second judgement needs. A module the main
/// module does not import contributes nothing to the compiled definition and keeps its own-view
/// judgement only. Diagnostics the per-module checks already reported are not repeated.
fn check_compiled_view_productions(views: &DefinitionViews<'_>) -> Vec<Diagnostic> {
    let definition = views.definition();
    let main = definition.main_module_id();
    let sorts = views.sort_catalog(main);
    let productions = views.production_catalog(main);
    // A cyclic order is the definition's circular subsort error, which its own checks report.
    let subsorts = views.subsorts(main).ok();
    let macro_labels = definition.rule_catalog(main).all_macro_labels(productions);
    let mut modules = definition.transitive_imports(main);
    modules.push(main);
    let mut diagnostics = Vec::new();
    for module in modules {
        let sentences = definition
            .module(module)
            .local_sentences
            .iter()
            .map(std::sync::Arc::as_ref)
            .collect::<Vec<_>>();
        diagnostics.extend(check_tokens(&sentences, sorts, &macro_labels));
        diagnostics.extend(attributes::check_hooked_sort_constructors(
            &sentences,
            productions,
            sorts,
        ));
        diagnostics.extend(collections::check_collection_productions(
            &sentences,
            productions,
            sorts,
        ));
        if let Some(subsorts) = subsorts {
            diagnostics.extend(check_sort_top_uniqueness(&sentences, subsorts));
        }
    }
    diagnostics
}

/// Java `CheckK`: the alias of an `#as` pattern must be a variable.
pub fn check_k_terms(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        for (_, term) in sentence.terms() {
            term.visit_preorder(&mut |term| {
                let Term::As { alias, .. } = term else {
                    return;
                };
                if !valid_as_alias(alias) {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidAsPattern,
                        "Found #as pattern where the right side is not a variable.",
                        sentence,
                    ));
                }
            });
        }
    }
    diagnostics
}

/// Java `CheckRewrite`.
pub fn check_rewrites(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let (body, requires, is_claim) = match sentence {
            Sentence::Rule { body, requires, .. } => (body, requires, false),
            Sentence::Claim { body, requires, .. } => (body, requires, true),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let mut state = RewriteState::default();
        visit_rewrite_term(requires, &mut state, &mut diagnostics, sentence);
        visit_rewrite_term(body, &mut state, &mut diagnostics, sentence);
        if !state.has_rewrite && !is_claim {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidRewrite,
                "Rules must have at least one rewrite.",
                sentence,
            ));
        }
    }
    diagnostics
}

/// Java `CheckAnonymous`.
pub fn check_anonymous_variables(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        if sentence.attributes().string(AttributeKey::Label) == Some("STDIN-STREAM.stdinUnblock") {
            continue;
        }
        let mut counts = BTreeMap::<String, usize>::new();
        for (_, term) in sentence.terms() {
            term.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term {
                    *counts.entry(name.clone()).or_default() += 1;
                }
            });
        }
        for (name, count) in counts {
            let named_anonymous = is_named_anonymous(&name);
            if count == 1
                && !named_anonymous
                && !anonymous_variable_exempt(sentence, &name)
                // Java suppresses this warning for generated variables, identified by
                // missing term locations. Until retained relative spans are mapped back to
                // absolute source locations, the sentence location is the closest proxy.
                && sentence.attributes().location().is_some()
            {
                diagnostics.push(Diagnostic::warning(
                    DiagnosticCode::UnusedVariable,
                    format!(
                        "Variable '{name}' defined but not used. Prefix variable name with underscore if this is intentional."
                    ),
                    sentence,
                ));
            } else if count > 1 && named_anonymous && !is_anonymous(&name) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidAnonymousVariable,
                    format!(
                        "Variable '{name}' declared as unused, but it is used. Remove underscore from variable name if this is intentional."
                    ),
                    sentence,
                ));
            }
        }
    }
    diagnostics
}

/// Java `CheckLabels`: context aliases are deliberately exempt.
pub fn check_duplicate_labels(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut labels = HashSet::new();
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        if matches!(sentence, Sentence::ContextAlias { .. }) {
            continue;
        }
        let Some(label) = sentence.attributes().string(AttributeKey::Label) else {
            continue;
        };
        if !labels.insert(label) {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::DuplicateSentenceLabel,
                format!("Found duplicate sentence label {label}"),
                sentence,
            ));
        }
    }
    diagnostics
}

/// Java `CheckSyntaxGroups`.
pub fn check_syntax_groups(
    sentences: &[&Sentence],
    priorities: &PartialOrder<String>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::SyntaxAssociativity { tags, .. } = sentence else {
            continue;
        };
        let tags = tags
            .iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        for left in 0..tags.len() {
            // Invariant: `diagnostics` holds a warning for every pair `(tags[l], tags[r])` related by `priorities` with `l < left`, or with `l == left` and `r < right`; each iteration consumes one index of `left + 1..tags.len()`, so a group costs O(|tags|^2) `in_some_relation` queries.
            for right in left + 1..tags.len() {
                if priorities.in_some_relation(tags[left], tags[right]) {
                    diagnostics.push(Diagnostic::warning(
                        DiagnosticCode::InvalidAssociativity,
                        format!(
                            "Symbols {} and {} are in the same associativity group, but have different priorities.",
                            tags[left], tags[right]
                        ),
                        sentence,
                    ));
                }
            }
        }
    }
    diagnostics
}

/// Whether a local sentence is a production with an associativity attribute.
fn local_associativity(sentences: &[&Sentence]) -> bool {
    sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Production { attributes, .. }
            if attributes.has_any(&[AttributeKey::Left, AttributeKey::Right, AttributeKey::NonAssoc]))
    })
}

/// Whether some grammar containing the productions of `module` admits a term of sort `below` at a
/// nonterminal of sort `above`.
///
/// A production belongs to the rule grammar of its own module and to that of every module that
/// imports it, directly or not, and the rules of each are parsed in that module's grammar, whose
/// order ([`sorts::rule_grammar_subsorts`]) includes the subsorts the module itself declares. The
/// declaring module is asked first, and the importing modules only when it does not admit the
/// term.
/// A cyclic rule-grammar order is the definition's subsort error, which its own checks report;
/// the module's declared order then stands in, and a module whose declared order is cyclic too
/// admits nothing here.
fn grammar_admits(
    views: &DefinitionViews<'_>,
    module: ModuleId,
    below: &Sort,
    above: &Sort,
) -> bool {
    std::iter::once(module)
        .chain(views.importers(module).iter().copied())
        .any(|grammar| {
            views
                .rule_grammar_subsorts(grammar)
                .or_else(|_| views.subsorts(grammar))
                .is_ok_and(|order| order.less_than_eq(below, above))
        })
}

/// Reject an associativity attribute on a binary production that it cannot affect.
///
/// `left` on a production `p` forbids a `p` term as the right argument of a `p` term, `right` as
/// the left argument, and `non-assoc` as either. Such a nesting can be parsed only when a term of
/// the result sort of `p` is admitted at that argument, so the attribute has an effect exactly when
/// the result sort is below the argument sort in `admission`: the order the grammar the production
/// is parsed in admits terms by, which for a module is its rule grammar's order
/// (`sorts::rule_grammar_subsorts`), where every sort of K items is below `KItem` and `K`.
pub fn check_associativity(
    sentences: &[&Sentence],
    admission: &PartialOrder<Sort>,
) -> Vec<Diagnostic> {
    check_associativity_by(sentences, |below, above| {
        admission.less_than_eq(below, above)
    })
}

/// [`check_associativity`] with the admission order given as `admits(below, above)`.
///
/// A production is part of every grammar that contains it, and its attribute has an effect when
/// some such grammar admits the nesting it forbids; the definition checks pass
/// [`grammar_admits`], which asks every module whose view contains the production.
fn check_associativity_by(
    sentences: &[&Sentence],
    mut admits: impl FnMut(&Sort, &Sort) -> bool,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        let arguments = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect::<Vec<_>>();
        let [left, right] = arguments.as_slice() else {
            continue;
        };
        // Only the relations an attribute needs are asked: `admits` may consult other modules.
        if attributes.has(AttributeKey::Left) && !admits(sort, right) {
            diagnostics.push(invalid_assoc(
                AttributeKey::Left.as_str(),
                format!(
                    "The sub-sorting relation {sort} <= {right} does not hold in any module that sees this production, so the left attribute has no effect."
                ),
                sentence,
            ));
        }
        if attributes.has(AttributeKey::Right) && !admits(sort, left) {
            diagnostics.push(invalid_assoc(
                AttributeKey::Right.as_str(),
                format!(
                    "The sub-sorting relation {sort} <= {left} does not hold in any module that sees this production, so the right attribute has no effect."
                ),
                sentence,
            ));
        }
        if attributes.has(AttributeKey::NonAssoc) && !(admits(sort, left) && admits(sort, right)) {
            diagnostics.push(invalid_assoc(
                AttributeKey::NonAssoc.as_str(),
                format!(
                    "One of the sub-sorting relations {sort} <= {left} or {sort} <= {right} does not hold in any module that sees this production, so the non-assoc attribute has no effect."
                ),
                sentence,
            ));
        }
    }
    diagnostics
}

/// Java `CheckSortTopUniqueness`.
pub fn check_sort_top_uniqueness(
    sentences: &[&Sentence],
    subsorts: &PartialOrder<Sort>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let cell = Sort::frontend(FrontendSort::Cell);
    let k_list = Sort::frontend(FrontendSort::KList);
    let bag = Sort::frontend(FrontendSort::Bag);
    for sentence in sentences {
        let sort = match sentence {
            Sentence::Production { sort, .. } | Sentence::SyntaxSort { sort, .. } => sort,
            Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        if sort != &cell && subsorts.less_than(sort, &k_list) && subsorts.less_than(sort, &bag) {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::MultipleTopSorts,
                format!("Multiple top sorts found for {sort}: KList and Bag."),
                sentence,
            ));
        }
    }
    diagnostics
}

/// Java `CheckTokens`.
pub fn check_tokens(
    sentences: &[&Sentence],
    sorts: &SortCatalog<'_>,
    macro_labels: &BTreeSet<LabelHead>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Production {
            label,
            sort,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        let head = match ResultSorts::of(sentence) {
            // Instances are judged where sort injection forms them.
            ResultSorts::Every => continue,
            ResultSorts::Head(head) => head,
        };
        if matches!(sort.role(), SortRole::Scaffolding | SortRole::RigidVariable)
            || attributes.has_any(&ALLOWED_TOKEN_ATTRIBUTES)
            || IGNORED_TOKEN_SORTS.contains(&sort.name.as_str())
            || !sorts.head_admits_domain_values(&head)
            || label
                .as_ref()
                .is_some_and(|label| macro_labels.contains(&LabelHead::from(label)))
        {
            continue;
        }
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            if sorts.token_sorts().contains(sort) {
                format!(
                    "Sort {} was declared as a token. Productions of this sort can only contain [function] or [token] labels.",
                    sort.name
                )
            } else {
                format!("Sort {sort} has domain values (its head has a token declaration, or the compiler writes its literals). Productions of this sort can only contain [function] or [token] labels.")
            },
            sentence,
        ));
    }
    diagnostics
}

fn invalid_assoc(attribute: &str, hint: String, sentence: &Sentence) -> Diagnostic {
    Diagnostic::error(
        DiagnosticCode::InvalidAssociativity,
        format!("{attribute} attribute not permitted on non-associative production.\nHint: {hint}"),
        sentence,
    )
}

fn check_domain_value_tokens(sentences: &[&Sentence], sorts: &SortCatalog<'_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        for (_, root) in sentence.terms() {
            root.visit_preorder(&mut |term| {
                if let Term::Token { token, sort } = term
                    && !sorts.admits_domain_value(sort)
                {
                    diagnostics.push(Diagnostic::error(
                        DiagnosticCode::InvalidDomainValue,
                        format!(
                            "Token {token:?} of sort {sort} has no visible token declaration in {sentence:?}"
                        ),
                        sentence,
                    ));
                }
            });
        }
    }
    diagnostics
}

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Term is not a sentence kind; only the listed variants are special here"
)]
fn valid_as_alias(alias: &Term) -> bool {
    match alias.unannotated() {
        Term::Variable { .. } => true,
        Term::Apply { label, arguments }
            if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
                && matches!(arguments.as_slice(), [argument] if matches!(argument.unannotated(), Term::Variable { .. })) =>
        {
            true
        }
        _ => false,
    }
}

fn is_named_anonymous(name: &str) -> bool {
    name.starts_with('_')
        || name.starts_with("?_")
        || name.starts_with("!_")
        || name.starts_with("@_")
}

fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn anonymous_variable_exempt(sentence: &Sentence, name: &str) -> bool {
    matches!(sentence, Sentence::ContextAlias { .. }) && name == "HERE"
        || matches!(
            sentence,
            Sentence::Context { .. } | Sentence::ContextAlias { .. }
        ) && name == "HOLE"
}

#[derive(Default)]
struct RewriteState {
    has_rewrite: bool,
    in_rewrite: bool,
    in_rewrite_rhs: bool,
    in_as: bool,
    in_function_context: bool,
    in_function_body: bool,
}

// Invariant: the `state` flags describe the rewrite, `#as`, and `#fun` context enclosing `term`, and each recursive call descends into a strict subterm of `term`, so the size of the rule body bounds the calls.
fn visit_rewrite_term(
    term: &Term,
    state: &mut RewriteState,
    diagnostics: &mut Vec<Diagnostic>,
    sentence: &Sentence,
) {
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            let was_in_rewrite = state.in_rewrite;
            let was_in_rewrite_rhs = state.in_rewrite_rhs;
            if state.in_rewrite {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "Rewrites are not allowed to be nested.",
                    sentence,
                ));
            }
            if state.in_function_context {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "Rewrites are not allowed in the context of a function rule.",
                    sentence,
                ));
            }
            if state.in_as {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "Rewrites are not allowed inside an #as pattern.",
                    sentence,
                ));
            }
            state.has_rewrite = true;
            state.in_rewrite = true;
            visit_rewrite_term(left, state, diagnostics, sentence);
            state.in_rewrite_rhs = true;
            visit_rewrite_term(right, state, diagnostics, sentence);
            state.in_rewrite_rhs = was_in_rewrite_rhs;
            state.in_rewrite = was_in_rewrite;
        }
        Term::As { pattern, alias } => {
            let was_in_as = state.in_as;
            if state.in_rewrite_rhs {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "#as is not allowed in the RHS of a rule.",
                    sentence,
                ));
            }
            state.in_as = true;
            visit_rewrite_term(pattern, state, diagnostics, sentence);
            visit_rewrite_term(alias, state, diagnostics, sentence);
            state.in_as = was_in_as;
        }
        Term::Variable { name, .. } => {
            if !state.in_rewrite_rhs && name.starts_with('?') {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidExistentialVariable,
                    format!(
                        "Existential variable {name} found in LHS. Existential variables are only allowed in the RHS."
                    ),
                    sentence,
                ));
            }
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun2) && arguments.len() >= 2 =>
        {
            let saved = save_function_state(state);
            state.in_rewrite = false;
            state.has_rewrite = false;
            state.in_function_context = false;
            state.in_function_body = false;
            visit_rewrite_term(&arguments[0], state, diagnostics, sentence);
            if !state.has_rewrite {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "#fun expressions must have at least one rewrite.",
                    sentence,
                ));
            }
            restore_function_state(state, saved);
            visit_rewrite_term(&arguments[1], state, diagnostics, sentence);
            for argument in &arguments[2..] {
                visit_rewrite_term(argument, state, diagnostics, sentence);
            }
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::Fun3) && arguments.len() >= 3 =>
        {
            let saved = save_function_state(state);
            state.in_rewrite = true;
            state.has_rewrite = true;
            state.in_function_context = false;
            state.in_function_body = false;
            visit_rewrite_term(&arguments[0], state, diagnostics, sentence);
            visit_rewrite_term(&arguments[1], state, diagnostics, sentence);
            restore_function_state(state, saved);
            visit_rewrite_term(&arguments[2], state, diagnostics, sentence);
            for argument in &arguments[3..] {
                visit_rewrite_term(argument, state, diagnostics, sentence);
            }
        }
        Term::Apply { label, arguments }
            if label.is(InternalLabel::WithConfig) && arguments.len() >= 2 =>
        {
            let was_in_function_context = state.in_function_context;
            let was_in_function_body = state.in_function_body;
            if state.in_function_context || state.in_function_body {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "Function context is not allowed to be nested.",
                    sentence,
                ));
            }
            if state.in_rewrite {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::InvalidRewrite,
                    "Function context is not allowed inside a rewrite.",
                    sentence,
                ));
            }
            state.in_function_body = true;
            visit_rewrite_term(&arguments[0], state, diagnostics, sentence);
            state.in_function_body = was_in_function_body;
            state.in_function_context = true;
            visit_rewrite_term(&arguments[1], state, diagnostics, sentence);
            state.in_function_context = was_in_function_context;
            for argument in &arguments[2..] {
                visit_rewrite_term(argument, state, diagnostics, sentence);
            }
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                visit_rewrite_term(item, state, diagnostics, sentence);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
        Term::Annotated { .. } => unreachable!(),
    }
}

fn save_function_state(state: &RewriteState) -> (bool, bool, bool, bool) {
    (
        state.in_rewrite,
        state.has_rewrite,
        state.in_function_context,
        state.in_function_body,
    )
}

fn restore_function_state(state: &mut RewriteState, saved: (bool, bool, bool, bool)) {
    state.in_rewrite = saved.0;
    state.has_rewrite = saved.1;
    state.in_function_context = saved.2;
    state.in_function_body = saved.3;
}
