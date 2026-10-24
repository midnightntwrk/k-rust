//! The findings of a definition's full critical-pair check as a campaign states them
//! (ARCHITECTURE 4.3): their names, which `assume-joined` matches, and their report entries
//! with readable terms ([`crate::report::DefinitionFinding`]).
//!
//! A pair is named `FIRST,SECOND@POSITION`: each equation by its written position
//! `FILE:LINE:COLUMN` with the file's last path component (a compiler-generated overload axiom,
//! which has none, by `overload:GREATER:LESSER`, the KORE names of its overloaded pair), and the
//! position in the first equation's left-hand side, `root` or argument indexes joined by `.`. A
//! name given to `assume-joined` matches a pair when its position is the pair's and each rule
//! part names the equation: its written position, or any trailing part of it that starts after
//! a `/`, its unique id, its label, or its overload part; a root pair is matched in either order.
//! A name may start with `baseline:` or `mutant:` to apply on that definition only; otherwise it
//! applies on each definition where it matches, and must match the same equations (by unique
//! id) on both.

use std::collections::BTreeSet;

use k_rust::{
    k_rust_backend::{
        confluence::UnjoinedPair,
        data_term::{DataHeads, Finding},
        externalize,
        rule::{Predicate, RewriteRule, RuleOrigin},
        substitution::{Substitution, substitute},
        term::Term,
    },
    kast::identifier::{decode_label, decode_sort_name, decode_variable, encode_variable},
    kore::ast::{Pattern as KorePattern, VariableKind},
};

use crate::{
    report::{DefinitionFinding, DefinitionRole, FindingInstance, FindingKind, FindingVerdict},
    values::TextSyntax,
};

/// The written position of `rule`'s first sentence, `FILE:LINE:COLUMN`.
fn written(rule: &RewriteRule) -> Option<String> {
    rule.attributes
        .origins
        .first()
        .and_then(RuleOrigin::written_position)
}

/// How a finding names `rule`: its written position, else its label, its unique id, or the
/// rule's diagnostic name.
fn equation(rule: &RewriteRule) -> String {
    written(rule)
        .or_else(|| rule.attributes.label.clone())
        .or_else(|| rule.attributes.identifier().map(str::to_owned))
        .unwrap_or_else(|| rule.attributes.diagnostic_name(label))
}

/// `position` as a name writes it.
fn position_text(position: &[usize]) -> String {
    if position.is_empty() {
        "root".to_owned()
    } else {
        position
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(".")
    }
}

/// The overload part naming a compiler-generated overload axiom, which has no written position.
fn overload_part(rule: &RewriteRule) -> Option<String> {
    let (greater, lesser) = rule.attributes.overload.as_ref()?;
    Some(format!("overload:{greater}:{lesser}"))
}

/// How a name writes `rule`: its written position with the file's last path component, else its
/// overload part, its label or its unique id.
fn rule_part(rule: &RewriteRule) -> Option<String> {
    written(rule)
        .map(|written| match written.rsplit_once('/') {
            Some((_, file)) => file.to_owned(),
            None => written,
        })
        .or_else(|| overload_part(rule))
        .or_else(|| rule.attributes.label.clone())
        .or_else(|| rule.attributes.identifier().map(str::to_owned))
}

/// The name `assume-joined` takes for `pair` (the module documentation), `None` when an
/// equation has neither a written position, an overloaded pair, a label nor a unique id.
pub(crate) fn name(pair: &UnjoinedPair) -> Option<String> {
    Some(format!(
        "{},{}@{}",
        rule_part(&pair.first)?,
        rule_part(&pair.second)?,
        position_text(&pair.position)
    ))
}

/// Whether `given`, one rule part of a name, names `rule`.
fn names_rule(given: &str, rule: &RewriteRule) -> bool {
    let given = given.trim();
    if given.is_empty() {
        return false;
    }
    written(rule).is_some_and(|written| {
        written == given
            || written
                .strip_suffix(given)
                .is_some_and(|prefix| prefix.ends_with('/'))
    }) || rule.attributes.identifier() == Some(given)
        || rule.attributes.label.as_deref() == Some(given)
        || overload_part(rule).as_deref() == Some(given)
}

/// Whether the name `given`, without a side prefix, names `pair` (the module documentation). A
/// name not of the shape `FIRST,SECOND@POSITION` names nothing.
pub(crate) fn names(given: &str, pair: &UnjoinedPair) -> bool {
    let Some((rules, position)) = given.rsplit_once('@') else {
        return false;
    };
    let Some((first, second)) = rules.split_once(',') else {
        return false;
    };
    position.trim() == position_text(&pair.position)
        && ((names_rule(first, &pair.first) && names_rule(second, &pair.second))
            // A root pair is symmetric.
            || (pair.position.is_empty()
                && names_rule(first, &pair.second)
                && names_rule(second, &pair.first)))
}

/// The names of `assume_joined` that apply on the definition `side`, side prefixes removed.
pub(crate) fn for_side(side: DefinitionRole, assume_joined: &[String]) -> Vec<String> {
    assume_joined
        .iter()
        .filter_map(|given| match side_of(given) {
            (Some(named), _) if named != side => None,
            (_, rest) => Some(rest.to_owned()),
        })
        .collect()
}

/// The side prefix of `given`, if any, and the name without it.
pub(crate) fn side_of(given: &str) -> (Option<DefinitionRole>, &str) {
    if let Some(rest) = given.strip_prefix("baseline:") {
        (Some(DefinitionRole::Baseline), rest)
    } else if let Some(rest) = given.strip_prefix("mutant:") {
        (Some(DefinitionRole::Mutant), rest)
    } else {
        (None, given)
    }
}

/// Whether one of `assumed` (side prefixes already removed) names `finding`'s pair.
pub(crate) fn assumed(assumed: &[String], finding: &Finding) -> bool {
    finding
        .pair()
        .is_some_and(|pair| assumed.iter().any(|given| names(given, pair)))
}

/// How a pair's equations are identified across definitions: each by its unique id, else its
/// overload part, else its written position.
fn identity(rule: &RewriteRule) -> String {
    rule.attributes
        .identifier()
        .map(str::to_owned)
        .or_else(|| overload_part(rule))
        .unwrap_or_else(|| equation(rule))
}

/// The pairs `given` (without a side prefix) names among `heads`' findings, assumed or not:
/// each as its equations' identities ([`identity`]) and its position, and as the report writes
/// it.
pub(crate) fn named_pairs(given: &str, heads: &DataHeads) -> BTreeSet<(Vec<String>, String)> {
    heads
        .findings()
        .iter()
        .chain(heads.assumed())
        .filter_map(Finding::pair)
        .filter(|pair| names(given, pair))
        .map(|pair| {
            let mut identities = vec![identity(&pair.first), identity(&pair.second)];
            if pair.position.is_empty() {
                // A root pair is symmetric: its equations in either order are one pair.
                identities.sort();
            }
            identities.push(position_text(&pair.position));
            (
                identities,
                format!(
                    "{},{}@{}",
                    equation(&pair.first),
                    equation(&pair.second),
                    position_text(&pair.position)
                ),
            )
        })
        .collect()
}

/// The report entries of `heads`' findings for the definition `side`, the assumed ones marked,
/// terms written with `text` where it prints them.
pub(crate) fn report(
    side: DefinitionRole,
    heads: &DataHeads,
    text: Option<&TextSyntax>,
) -> Vec<DefinitionFinding> {
    heads
        .findings()
        .iter()
        .map(|finding| entry(side, finding, false, text))
        .chain(
            heads
                .assumed()
                .iter()
                .map(|finding| entry(side, finding, true, text)),
        )
        .collect()
}

fn entry(
    side: DefinitionRole,
    finding: &Finding,
    assumed: bool,
    text: Option<&TextSyntax>,
) -> DefinitionFinding {
    let verdict = if finding.is_genuine() {
        FindingVerdict::Genuine
    } else {
        FindingVerdict::Undecided
    };
    match finding {
        Finding::Precondition(violation) => DefinitionFinding {
            side,
            verdict,
            kind: FindingKind::Precondition,
            name: None,
            equations: violation.rule.iter().map(|rule| equation(rule)).collect(),
            position: None,
            reason: violation.kind.to_string(),
            overlap: None,
            reducts: Vec::new(),
            conditions: None,
            instance: None,
            assumed,
        },
        Finding::Equation(pair) => DefinitionFinding {
            side,
            verdict,
            kind: FindingKind::Equation,
            name: None,
            equations: vec![equation(&pair.first)],
            position: None,
            reason: format!(
                "the equation is not applied to every subject it describes: {}",
                pair.reason
            ),
            overlap: None,
            reducts: Vec::new(),
            conditions: None,
            instance: None,
            assumed,
        },
        Finding::Pair { pair, instance } => {
            let names = Readable::of(pair);
            let show = |term: &Term| names.show(term, text);
            // The reducts, then the overlap, written so that different terms never read alike.
            let reducts = pair.sides.as_ref().map(|(left, right)| {
                let bottom = || "\\bottom".to_owned();
                match (left, right) {
                    (Some(left), Some(right)) => names.show_apart(left, right, text),
                    (left, right) => (
                        left.as_ref().map_or_else(bottom, show),
                        right.as_ref().map_or_else(bottom, show),
                    ),
                }
            });
            let overlap = pair.overlap.as_ref().map(|overlap| {
                let written = show(overlap);
                match (&reducts, &pair.sides) {
                    (Some((left, right)), Some((left_term, right_term)))
                        if written == *left || written == *right =>
                    {
                        let other = if written == *left {
                            left_term
                        } else {
                            right_term
                        };
                        let other = other.as_ref().unwrap_or(overlap);
                        names.show_apart(overlap, other, text).0
                    }
                    _ => written,
                }
            });
            let instance = instance.as_ref().map(|instance| {
                let (left, right) = names.show_apart(&instance.values.0, &instance.values.1, text);
                FindingInstance {
                    assignment: instance
                        .assignment
                        .iter()
                        .map(|(variable, value)| {
                            format!("{} = {}", readable_variable(&variable.name), show(value))
                        })
                        .collect(),
                    overlap: show(&instance.overlap),
                    values: vec![left, right],
                }
            });
            DefinitionFinding {
                side,
                verdict,
                kind: FindingKind::Pair,
                name: name(pair),
                equations: vec![equation(&pair.first), equation(&pair.second)],
                position: Some(position_text(&pair.position)),
                reason: match &instance {
                    Some(instance) => format!(
                        "at {} the two equations equate {} and {}, distinct data terms, so no \
                         model satisfies the definition",
                        instance.overlap, instance.values[0], instance.values[1]
                    ),
                    None => format!("not shown to join: {}", pair.reason),
                },
                overlap,
                reducts: reducts
                    .map(|(left, right)| vec![left, right])
                    .unwrap_or_default(),
                conditions: pair
                    .conditions
                    .as_ref()
                    .filter(|conditions| **conditions != Predicate::True)
                    .map(|conditions| names.show_predicate(conditions, text)),
                instance,
                assumed,
            }
        }
    }
}

/// A KORE symbol name as the K label it encodes.
fn label(name: &str) -> String {
    decode_label(name).unwrap_or_else(|_| name.to_owned())
}

/// A backend variable name as the author wrote it: the K name its KORE name encodes, and for a
/// variable the check introduced (`NAME!MARKERN`, `confluence::UnjoinedPair`) the base name, a
/// `'` and the number.
fn readable_variable(name: &str) -> String {
    let (base, minted) = match name.split_once('!') {
        Some((base, minted)) => (base, Some(minted)),
        None => (name, None),
    };
    let base = base.rsplit_once('#').map_or(base, |(_, base)| base);
    let decoded = match decode_variable(base) {
        (_, Ok(decoded)) if !decoded.is_empty() => decoded,
        _ => base.to_owned(),
    };
    match minted {
        Some(minted) => {
            let digits = minted
                .trim_start_matches(|character: char| !character.is_ascii_digit())
                .to_owned();
            format!("{decoded}'{digits}")
        }
        None => decoded,
    }
}

/// The renaming of one pair's variables to the KORE names of their readable names
/// ([`readable_variable`]), so that the definition's printer writes them as the author would.
struct Readable(Substitution);

impl Readable {
    fn of(pair: &UnjoinedPair) -> Self {
        let mut variables = BTreeSet::new();
        for term in [pair.overlap.as_ref()]
            .into_iter()
            .chain(
                pair.sides
                    .iter()
                    .flat_map(|(left, right)| [left.as_ref(), right.as_ref()]),
            )
            .flatten()
        {
            variables.extend(term.attributes().variables.iter().cloned());
        }
        if let Some(conditions) = &pair.conditions {
            variables.extend(conditions.free_variables());
        }
        Self(
            variables
                .into_iter()
                .map(|variable| {
                    let renamed = variable.with_name(encode_variable(
                        &readable_variable(&variable.name),
                        VariableKind::Element,
                    ));
                    (variable, Term::variable(renamed))
                })
                .collect(),
        )
    }

    /// `term` as one line: K text through `text` when it prints, otherwise applications of K
    /// labels.
    fn show(&self, term: &Term, text: Option<&TextSyntax>) -> String {
        let pattern = externalize::term(&substitute(term, &self.0));
        text.and_then(|text| text.show(&pattern))
            .unwrap_or_else(|| prefix(&pattern))
    }

    /// `left` and `right` as [`Self::show`] writes them, or, when the two texts are equal although
    /// the terms differ (the printers drop injections, so terms of different source sorts read
    /// alike), as applications of K labels with each injection's source sort (`t : Sort`).
    fn show_apart(&self, left: &Term, right: &Term, text: Option<&TextSyntax>) -> (String, String) {
        let (left_text, right_text) = (self.show(left, text), self.show(right, text));
        if left_text != right_text || left == right {
            return (left_text, right_text);
        }
        let typed = |term: &Term| typed(&externalize::term(&substitute(term, &self.0)));
        (typed(left), typed(right))
    }

    /// `predicate`, its conjuncts joined by `andBool`, each a Boolean term as [`Self::show`]
    /// writes it when it is one, else its matching-logic form.
    fn show_predicate(&self, predicate: &Predicate, text: Option<&TextSyntax>) -> String {
        let conjuncts = match predicate {
            Predicate::And(conjuncts) => conjuncts.to_vec(),
            other => vec![other.clone()],
        };
        conjuncts
            .iter()
            .map(|conjunct| match conjunct {
                Predicate::Term(term) => self.show(term, text),
                Predicate::Equals(left, right) if is_true(right) => self.show(left, text),
                Predicate::Equals(left, right) if is_true(left) => self.show(right, text),
                Predicate::Equals(left, right) => {
                    format!("{} = {}", self.show(left, text), self.show(right, text))
                }
                other => {
                    let mut terms = Vec::new();
                    other.visit_terms(&mut |term| terms.push(self.show(term, text)));
                    format!("{}({})", connective(other), terms.join(", "))
                }
            })
            .collect::<Vec<_>>()
            .join(" andBool ")
    }
}

fn is_true(term: &Term) -> bool {
    *term == Term::bool(true)
}

/// The matching-logic connective of `predicate`, for a conjunct that is no Boolean term.
fn connective(predicate: &Predicate) -> &'static str {
    match predicate {
        Predicate::True => "\\top",
        Predicate::False => "\\bottom",
        Predicate::Term(_) | Predicate::Equals(..) => "\\equals",
        Predicate::Ceil(_) | Predicate::Defined(_) => "\\ceil",
        Predicate::Floor(_) => "\\floor",
        Predicate::In(..) => "\\in",
        Predicate::Not(_) => "\\not",
        Predicate::And(_) => "\\and",
        Predicate::Or(_) => "\\or",
        Predicate::Implies(..) => "\\implies",
        Predicate::Iff(..) => "\\iff",
        Predicate::Exists(..) => "\\exists",
        Predicate::Forall(..) => "\\forall",
        Predicate::Absent(_) => "absent",
    }
}

/// `pattern` as applications of K labels: injections dropped, domain values as their text,
/// variables by their K names.
fn prefix(pattern: &KorePattern) -> String {
    labelled(pattern, false)
}

/// [`prefix`], with each injection written as its argument and its source sort, `(t : Sort)`.
fn typed(pattern: &KorePattern) -> String {
    labelled(pattern, true)
}

fn labelled(pattern: &KorePattern, sorts: bool) -> String {
    let prefix = |pattern: &KorePattern| labelled(pattern, sorts);
    match pattern {
        KorePattern::String(text) => format!("{:?}", String::from_utf8_lossy(text.as_bytes())),
        KorePattern::Variable(variable) => readable_variable(&variable.name),
        KorePattern::DomainValue { value, .. } => {
            String::from_utf8_lossy(value.as_bytes()).into_owned()
        }
        KorePattern::Application { symbol, arguments }
        | KorePattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            if symbol.name == "inj"
                && let [argument] = arguments.as_slice()
            {
                return match (sorts, symbol.sort_parameters.first()) {
                    (true, Some(k_rust::kore::ast::Sort::Application { name, .. })) => {
                        let sort = decode_sort_name(name).unwrap_or_else(|_| name.clone());
                        format!("({} : {sort})", prefix(argument))
                    }
                    _ => prefix(argument),
                };
            }
            if symbol.name == "\\dv"
                && let [KorePattern::String(text)] = arguments.as_slice()
            {
                return String::from_utf8_lossy(text.as_bytes()).into_owned();
            }
            let name = label(&symbol.name);
            if arguments.is_empty() {
                name
            } else {
                format!(
                    "{name}({})",
                    arguments.iter().map(prefix).collect::<Vec<_>>().join(", ")
                )
            }
        }
        other => format!("{other:?}"),
    }
}
