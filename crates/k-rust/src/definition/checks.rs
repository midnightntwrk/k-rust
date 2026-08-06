//! Dependency-light structural checks ported from the Java frontend.

use std::collections::{BTreeSet, HashSet};

use super::ast::{ProductionItem, Sentence};
use super::ordering::Error as OrderingError;
use super::partial_order::{Cycle, PartialOrder};
use super::resolve::{ModuleId, ResolvedDefinition};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{Label, Sort};

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

/// Run the first dependency-light structural-check batch over local sentences.
pub fn check_module(
    definition: &ResolvedDefinition,
    module: ModuleId,
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

    let diagnostics = check_duplicate_labels(&sentences)
        .into_iter()
        .chain(check_syntax_groups(&sentences, &priorities))
        .chain(check_associativity(&sentences, &subsorts))
        .chain(check_sort_top_uniqueness(&sentences, &subsorts))
        .chain(check_tokens(
            &sentences,
            sort_catalog.token_sorts(),
            &macro_labels,
        ))
        .collect::<BTreeSet<_>>();
    Ok(diagnostics.into_iter().collect())
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
