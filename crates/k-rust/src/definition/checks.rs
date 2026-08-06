//! Dependency-light structural checks ported from the Java frontend.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use super::ast::{ProductionItem, Sentence};
use super::ordering::Error as OrderingError;
use super::partial_order::{Cycle, PartialOrder};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{Label, Sort, Term};

mod functions;
mod rhs_variables;
mod term_position;

pub use functions::check_functions;
pub use rhs_variables::{StructuralCheckBackend, StructuralCheckOptions, check_rhs_variables};

const ALLOWED_TOKEN_ATTRIBUTES: [&str; 3] = ["function", "token", "bracket"];
const IGNORED_TOKEN_SORTS: [&str; 2] = ["KBott", "KLabel"];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Ordering(OrderingError),
    CircularSubsort(Cycle<Sort>),
    CircularPriority(Cycle<String>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ordering(error) => error.fmt(formatter),
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
    let sentences = definition
        .sorted_local_sentences(module)
        .map_err(Error::Ordering)?;
    let subsorts = definition
        .subsorts(module)
        .map_err(Error::CircularSubsort)?;
    let priorities = definition
        .priorities(module)
        .map_err(Error::CircularPriority)?;
    let sort_catalog = definition.sort_catalog(module);
    let production_catalog = definition.production_catalog(module);
    let rule_catalog = definition.rule_catalog(module);
    let macro_labels = rule_catalog.all_macro_labels(&production_catalog);

    let mut diagnostics = check_duplicate_labels(&sentences)
        .into_iter()
        .chain(check_syntax_groups(&sentences, &priorities))
        .chain(check_associativity(&sentences, &subsorts))
        .chain(check_sort_top_uniqueness(&sentences, &subsorts))
        .chain(check_tokens(
            &sentences,
            sort_catalog.token_sorts(),
            &macro_labels,
        ))
        .chain(check_k_terms(&sentences))
        .chain(check_rewrites(&sentences))
        .chain(check_anonymous_variables(&sentences))
        .chain(check_rhs_variables(&sentences, options))
        .chain(check_functions(
            &sentences,
            &production_catalog,
            &sort_catalog,
        ))
        .collect::<Vec<_>>();
    diagnostics.sort();
    Ok(diagnostics)
}

/// Java `CheckK`: the alias of an `#as` pattern must be a variable.
pub fn check_k_terms(sentences: &[&Sentence]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        for term in checked_terms(sentence) {
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
            _ => continue,
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
        if sentence.attributes().get_str("label") == Some("STDIN-STREAM.stdinUnblock") {
            continue;
        }
        let mut counts = BTreeMap::<String, usize>::new();
        for term in checked_terms(sentence) {
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
                // missing term locations. Until terms retain spans, the sentence location
                // is the closest conservative proxy available.
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
        let Some(label) = sentence.attributes().get_str("label") else {
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

/// Java `CheckAssoc`.
pub fn check_associativity(
    sentences: &[&Sentence],
    subsorts: &PartialOrder<Sort>,
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
        let leq_left = subsorts.less_than_eq(sort, left);
        let leq_right = subsorts.less_than_eq(sort, right);
        if attributes.get("left").is_some() && !leq_right {
            diagnostics.push(invalid_assoc(
                "left",
                format!(
                    "The sub-sorting relation {sort} <= {right} does not hold, so the left attribute has no effect."
                ),
                sentence,
            ));
        }
        if attributes.get("right").is_some() && !leq_left {
            diagnostics.push(invalid_assoc(
                "right",
                format!(
                    "The sub-sorting relation {sort} <= {left} does not hold, so the right attribute has no effect."
                ),
                sentence,
            ));
        }
        if attributes.get("non-assoc").is_some() && !(leq_left && leq_right) {
            diagnostics.push(invalid_assoc(
                "non-assoc",
                format!(
                    "One of the sub-sorting relations {sort} <= {left} or {sort} <= {right} does not hold, so the non-assoc attribute has no effect."
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
    let cell = Sort::new("Cell");
    let k_list = Sort::new("KList");
    let bag = Sort::new("Bag");
    for sentence in sentences {
        let sort = match sentence {
            Sentence::Production { sort, .. } | Sentence::SyntaxSort { sort, .. } => sort,
            _ => continue,
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
    token_sorts: &BTreeSet<Sort>,
    macro_labels: &BTreeSet<Label>,
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
        if sort.name.starts_with('#')
            || ALLOWED_TOKEN_ATTRIBUTES
                .iter()
                .any(|attribute| attributes.get(attribute).is_some())
            || IGNORED_TOKEN_SORTS.contains(&sort.name.as_str())
            || !token_sorts.contains(sort)
            || label
                .as_ref()
                .is_some_and(|label| macro_labels.contains(label))
        {
            continue;
        }
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidTokenProduction,
            format!(
                "Sort {} was declared as a token. Productions of this sort can only contain [function] or [token] labels.",
                sort.name
            ),
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

fn checked_terms(sentence: &Sentence) -> Vec<&Term> {
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
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![body, requires],
        _ => Vec::new(),
    }
}

fn valid_as_alias(alias: &Term) -> bool {
    match alias {
        Term::Variable { .. } => true,
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo")
                && matches!(arguments.as_slice(), [Term::Variable { .. }]) =>
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

fn visit_rewrite_term(
    term: &Term,
    state: &mut RewriteState,
    diagnostics: &mut Vec<Diagnostic>,
    sentence: &Sentence,
) {
    match term {
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
        Term::Apply { label, arguments } if label.name == "#fun2" && arguments.len() >= 2 => {
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
        Term::Apply { label, arguments } if label.name == "#fun3" && arguments.len() >= 3 => {
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
        Term::Apply { label, arguments } if label.name == "#withConfig" && arguments.len() >= 2 => {
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
