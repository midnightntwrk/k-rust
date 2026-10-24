//! The findings of a definition's full critical-pair check as a campaign states them
//! (ARCHITECTURE 4.3): their names, which `assume-joined` matches, and their report entries
//! with readable terms ([`crate::report::DefinitionFinding`]).
//!
//! A pair is named `FIRST,SECOND@POSITION`: each equation by its written position
//! `FILE:LINE:COLUMN` with the file's last path component (a compiler-generated overload axiom,
//! which has none, by `overload:GREATER:LESSER`, the K labels of its overloaded pair, each
//! quoted with `"` when it holds `,`, `:`, `@`, `"`, `\` or whitespace), and the
//! position in the first equation's left-hand side, `root` or argument indexes joined by `.`. A
//! name given to `assume-joined` matches a pair when its position is the pair's and each rule
//! part names the equation: its written position, or any trailing part of it that starts after
//! a `/`, its unique id, its label, or its overload part; a root pair is matched in either order.
//! A name may start with `baseline:` or `mutant:` to apply on that definition only; otherwise it
//! applies on each definition where it matches, and must match the same equations (by unique
//! id) on both.
//!
//! Every other finding that keeps a definition without data has a name too, so that every one
//! can be assumed: an equation at an evaluated hook that is not shown to agree with the hook
//! (a hook pair, or an equation at a hook with no written meaning) is `hook:EQUATION`, another
//! equation the evaluator does not apply to every subject it describes is `equation:EQUATION`,
//! and a precondition row is `precondition:EQUATION` for the equation it names, else
//! `precondition:KIND` followed by the K labels it names (`precondition:no-least-common-overload:A:B`).
//! `EQUATION` is a rule part as above. One `hook:` name covers every hook pair of its equation
//! (one per equation of the hook's written meaning): assuming it reads the equation as agreeing
//! with the hook; likewise one `precondition:EQUATION` names every row of that equation.
//!
//! A decided finding ([`Finding::is_decided`]) is named too, but its name is refused: a
//! precondition row that an equation is headed by a constructor or an injection, or indexed at a
//! collection or a bare variable (the equation rewrites terms the data judgement reads as free,
//! so they are not normal forms), or an equation whose right-hand side leaves a variable unbound
//! (read as written it equates every value of that sort). Each is a fact about the definition
//! as written that no assumption removes.

use std::collections::BTreeSet;

use k_rust::{
    k_rust_backend::{
        confluence::{UnjoinedPair, UnjoinedReason, Violation, ViolationKind},
        data_term::{DataHeads, Finding},
        externalize,
        rule::{Predicate, RewriteRule, RuleOrigin, TermIndex},
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

/// The overload part naming a compiler-generated overload axiom, which has no written position:
/// `overload:GREATER:LESSER` with the K labels of its overloaded pair, quoted where needed
/// ([`quoted`]).
fn overload_part(rule: &RewriteRule) -> Option<String> {
    let (greater, lesser) = rule.attributes.overload.as_ref()?;
    Some(format!(
        "overload:{}:{}",
        quoted(&label(greater)),
        quoted(&label(lesser))
    ))
}

/// The same part with the KORE names, which a name may also use.
fn overload_kore_part(rule: &RewriteRule) -> Option<String> {
    let (greater, lesser) = rule.attributes.overload.as_ref()?;
    Some(format!("overload:{greater}:{lesser}"))
}

/// `text`, or `text` in `"` with `"` and `\` escaped by `\` when it holds a character a name
/// separates its parts with (`,`, `:`, `@`), a quote, a backslash or whitespace.
fn quoted(text: &str) -> String {
    if text
        .chars()
        .any(|character| ",:@\"\\".contains(character) || character.is_whitespace())
    {
        let mut out = String::from('"');
        for character in text.chars() {
            if character == '"' || character == '\\' {
                out.push('\\');
            }
            out.push(character);
        }
        out.push('"');
        out
    } else {
        text.to_owned()
    }
}

/// `given` split at its first `,` and its last `@` outside quotes: the two rule parts and the
/// position; `None` for any other shape.
fn split_name(given: &str) -> Option<(String, String, String)> {
    let mut parts = vec![String::new()];
    let mut separators = Vec::new();
    let (mut quoted, mut escaped) = (false, false);
    for character in given.chars() {
        let current = parts.last_mut().expect("one part at least");
        if escaped {
            escaped = false;
            current.push(character);
        } else if quoted && character == '\\' {
            escaped = true;
            current.push(character);
        } else if character == '"' {
            quoted = !quoted;
            current.push(character);
        } else if !quoted && (character == ',' || character == '@') {
            separators.push(character);
            parts.push(String::new());
        } else {
            current.push(character);
        }
    }
    match (separators.as_slice(), parts.as_slice()) {
        ([',', '@'], [first, second, position]) => {
            Some((first.clone(), second.clone(), position.clone()))
        }
        _ => None,
    }
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
        || overload_kore_part(rule).as_deref() == Some(given)
}

/// Whether the name `given`, without a side prefix, names `pair` (the module documentation). A
/// name not of the shape `FIRST,SECOND@POSITION` names nothing.
pub(crate) fn names(given: &str, pair: &UnjoinedPair) -> bool {
    let Some((first, second, position)) = split_name(given) else {
        return false;
    };
    position.trim() == position_text(&pair.position)
        && ((names_rule(&first, &pair.first) && names_rule(&second, &pair.second))
            // A root pair is symmetric.
            || (pair.position.is_empty()
                && names_rule(&first, &pair.second)
                && names_rule(&second, &pair.first)))
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

/// The prefix of the name of a finding about one equation ([`Finding::Equation`]): `hook` for an
/// equation at an evaluated hook not shown to agree with it, `equation` otherwise.
fn equation_prefix(pair: &UnjoinedPair) -> &'static str {
    if pair.hook.is_some() || matches!(pair.reason, UnjoinedReason::UnmodelledHook(_)) {
        "hook"
    } else {
        "equation"
    }
}

/// The kind of a precondition row as a name writes it, with the K labels it names.
fn precondition_kind(kind: &ViolationKind) -> String {
    match kind {
        ViolationKind::ConstructorHeaded(symbol) => {
            format!("constructor-headed:{}", quoted(&label(symbol)))
        }
        ViolationKind::InjectionHeaded => "injection-headed".to_owned(),
        ViolationKind::IndexedAt(index) => format!("indexed-at:{}", quoted(&format!("{index:?}"))),
        ViolationKind::OverloadShape(symbol) => {
            format!("overload-shape:{}", quoted(&label(symbol)))
        }
        ViolationKind::NoLeastCommonOverload(first, second) => format!(
            "no-least-common-overload:{}:{}",
            quoted(&label(first)),
            quoted(&label(second))
        ),
        ViolationKind::PinnedByInjectiveTotal(symbol) => {
            format!("pinned-by-injective-total:{}", quoted(&label(symbol)))
        }
    }
}

/// The name `assume-joined` takes for `finding` (the module documentation), `None` when an
/// equation it names has neither a written position, an overloaded pair, a label nor a unique
/// id.
pub(crate) fn finding_name(finding: &Finding) -> Option<String> {
    match finding {
        Finding::Pair { pair, .. } => name(pair),
        Finding::Equation(pair) => Some(format!(
            "{}:{}",
            equation_prefix(pair),
            rule_part(&pair.first)?
        )),
        Finding::Precondition(violation) => Some(match &violation.rule {
            Some(rule) => format!("precondition:{}", rule_part(rule)?),
            None => format!("precondition:{}", precondition_kind(&violation.kind)),
        }),
    }
}

/// Whether the name `given`, without a side prefix, names `finding` (the module documentation).
pub(crate) fn names_finding(given: &str, finding: &Finding) -> bool {
    match finding {
        Finding::Pair { pair, .. } => names(given, pair),
        Finding::Equation(pair) => given
            .strip_prefix(equation_prefix(pair))
            .and_then(|rest| rest.strip_prefix(':'))
            .is_some_and(|rest| names_rule(rest, &pair.first)),
        Finding::Precondition(violation) => {
            given
                .strip_prefix("precondition:")
                .is_some_and(|rest| match &violation.rule {
                    Some(rule) => names_rule(rest, rule),
                    None => rest == precondition_kind(&violation.kind),
                })
        }
    }
}

/// Whether one of `assumed` (side prefixes already removed) names `finding`. A decided finding
/// ([`Finding::is_decided`]) is never assumed: its name is refused at setup
/// ([`decided_named`]).
pub(crate) fn assumed(assumed: &[String], finding: &Finding) -> bool {
    !finding.is_decided() && assumed.iter().any(|given| names_finding(given, finding))
}

/// The printed name of a decided finding of `heads` that `given` (without a side prefix) names,
/// with why it cannot be assumed, if any: such a name is refused, since the finding is a fact
/// about the definition as written.
pub(crate) fn decided_named(given: &str, heads: &DataHeads) -> Option<(String, String)> {
    heads
        .findings()
        .iter()
        .filter(|finding| finding.is_decided() && names_finding(given, finding))
        .find_map(|finding| {
            let why = match finding {
                Finding::Equation(pair) => format!(
                    "an equation whose right-hand side leaves {} unbound by its left-hand side: \
                     read as written it equates its left-hand side with every value of that \
                     sort, and the evaluator never applies it, so `applied as written` is no \
                     premise about the definition",
                    unbound_variables(pair)
                ),
                _ => "a precondition row: its equation rewrites terms the data judgement reads \
                      as free (constructor-, injection- or collection-headed), so no assumption \
                      about the definition as written makes them normal forms"
                    .to_owned(),
            };
            Some((finding_name(finding)?, why))
        })
}

/// The variables an equation's right-hand side or `ensures` leaves unbound by its left-hand
/// side, as the author wrote them, each in backquotes.
fn unbound_variables(pair: &UnjoinedPair) -> String {
    let names = pair
        .first
        .computed_attributes
        .unbound_result_variables
        .iter()
        .map(|name| format!("`{}`", readable_variable(name)))
        .collect::<Vec<_>>();
    if names.is_empty() {
        "a variable".to_owned()
    } else {
        names.join(", ")
    }
}

/// What a decided single-equation finding states: an equation whose right-hand side leaves a
/// variable unbound, which read as written equates every value of the variable's sort.
fn decided_equation_reason(pair: &UnjoinedPair) -> String {
    format!(
        "`{}`'s right-hand side or `ensures` leaves {} unbound by its left-hand side, so read as \
         written the equation equates its left-hand side with every value of that sort and the \
         evaluator never applies it: no end of this definition is data (a fact about the \
         definition as written, which assume-joined cannot remove; change that equation)",
        equation(&pair.first),
        unbound_variables(pair)
    )
}

/// What a decided precondition row states (the row withdraws claims: an equation rewrites terms
/// the data judgement reads as free): the equation, the terms it rewrites, and that those terms
/// are not normal forms, so no end of the definition is data.
fn decided_reason(violation: &Violation) -> String {
    let rule = violation.rule.as_ref().map_or_else(
        || "an equation".to_owned(),
        |rule| format!("`{}`", equation(rule)),
    );
    let rewrites = match &violation.kind {
        ViolationKind::ConstructorHeaded(symbol) => {
            let symbol = label(symbol);
            format!("a term headed by the constructor `{symbol}`, so `{symbol}` terms are")
        }
        ViolationKind::InjectionHeaded => "a sort injection, so injected terms are".to_owned(),
        ViolationKind::IndexedAt(TermIndex::Variable) => {
            "any term (it is indexed at a bare variable), so its subjects are".to_owned()
        }
        ViolationKind::IndexedAt(index) => {
            format!("a {index:?}-headed term, so {index:?} terms are")
        }
        other => return other.to_string(),
    };
    format!(
        "{rule} rewrites {rewrites} not normal forms: no end of this definition is data (a fact \
         about the definition as written, which assume-joined cannot remove; change that \
         equation)"
    )
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

/// The findings `given` (without a side prefix) names among `heads`' findings, assumed or not:
/// each as its kind and its equations' identities ([`identity`]), with a pair's position, and as
/// the report writes it. The hook pairs of one equation are one finding: one name assumes them
/// all.
pub(crate) fn named_findings(given: &str, heads: &DataHeads) -> BTreeSet<(Vec<String>, String)> {
    heads
        .findings()
        .iter()
        .chain(heads.assumed())
        .filter(|finding| names_finding(given, finding))
        .map(|finding| match finding {
            Finding::Pair { pair, .. } => {
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
            }
            Finding::Equation(pair) => {
                let prefix = equation_prefix(pair);
                (
                    vec![prefix.to_owned(), identity(&pair.first)],
                    format!("{prefix}:{}", equation(&pair.first)),
                )
            }
            Finding::Precondition(violation) => {
                let named = match &violation.rule {
                    Some(rule) => identity(rule),
                    None => precondition_kind(&violation.kind),
                };
                (
                    vec!["precondition".to_owned(), named.clone()],
                    format!("precondition:{named}"),
                )
            }
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
    } else if finding.is_decided() {
        FindingVerdict::Decided
    } else {
        FindingVerdict::Undecided
    };
    match finding {
        Finding::Precondition(violation) => DefinitionFinding {
            side,
            verdict,
            kind: FindingKind::Precondition,
            name: finding_name(finding),
            equations: violation.rule.iter().map(|rule| equation(rule)).collect(),
            position: None,
            reason: if finding.is_decided() {
                decided_reason(violation)
            } else {
                violation.kind.to_string()
            },
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
            name: finding_name(finding),
            equations: vec![equation(&pair.first)],
            position: None,
            reason: match &pair.hook {
                None if finding.is_decided() => decided_equation_reason(pair),
                Some(hook) => format!(
                    "the equation is not shown to agree with its hook `{hook}`: {}",
                    pair.reason
                ),
                None => format!(
                    "the equation is not applied to every subject it describes: {}",
                    pair.reason
                ),
            },
            overlap: None,
            reducts: Vec::new(),
            conditions: None,
            instance: None,
            assumed,
        },
        Finding::Pair { pair, instance } => {
            pair_entry(side, verdict, pair, instance.as_ref(), assumed, text)
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

/// The report entry of a pair finding (see [`entry`]).
fn pair_entry(
    side: DefinitionRole,
    verdict: FindingVerdict,
    pair: &UnjoinedPair,
    instance: Option<&k_rust::k_rust_backend::data_term::GroundInstance>,
    assumed: bool,
    text: Option<&TextSyntax>,
) -> DefinitionFinding {
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
                "at {} both equations apply and the input has two normal forms, {} and {}: \
                 k-rust's result for it depends on the order it tries the equations",
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

#[cfg(test)]
mod tests {
    use k_rust::{k_rust_backend::definition::BackendDefinition, kore::parser::parse_definition};

    use super::{decided_named, entry, finding_name};
    use crate::report::{DefinitionRole, FindingKind, FindingVerdict};

    /// INT8 follow-ups (review N4): an equation whose right-hand side leaves `Y` unbound (only
    /// hand-written KORE gives one) is a decided finding: its report entry says so, and the name
    /// `assume-joined` would take for it is refused with why.
    #[test]
    fn an_unbound_result_variable_is_decided_and_its_name_refused() {
        const FIXTURE: &str =
            include_str!("../../k-rust-backend/tests/fixtures/overloaded-list-owise.kore");
        let (head, tail) = FIXTURE.rsplit_once("endmodule").expect("one module");
        let source = format!(
            r#"{head}
    symbol any{{}}(SortExps{{}}) : SortVal{{}} [function{{}}()]
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(),
            \and{{R}}(\in{{SortExps{{}}, R}}(X0:SortExps{{}}, Es:SortExps{{}}), \top{{R}}())),
        \equals{{SortVal{{}}, R}}(any{{}}(X0:SortExps{{}}), \and{{SortVal{{}}}}(Y:SortVal{{}}, \top{{SortVal{{}}}}())))
        [label{{}}("any-unbound")]
endmodule{tail}"#
        );
        let syntax = parse_definition(&source).expect("parses");
        let definition =
            BackendDefinition::internalize(&syntax, "OVERLOADED-LIST-OWISE").expect("loads");
        let heads = definition.data_heads();
        let finding = heads
            .findings()
            .iter()
            .find(|finding| finding.is_decided())
            .expect("a decided finding");
        let report = entry(DefinitionRole::Baseline, finding, false, None);
        assert_eq!(report.verdict, FindingVerdict::Decided);
        assert_eq!(report.kind, FindingKind::Equation);
        assert!(
            report.reason.contains("leaves `Y` unbound") && report.reason.contains("change that"),
            "{}",
            report.reason
        );
        let name = finding_name(finding).expect("named");
        assert!(name.starts_with("equation:"), "{name}");
        let (named, why) = decided_named(&name, &heads).expect("refused");
        assert_eq!(named, name);
        assert!(why.contains("leaves `Y` unbound"), "{why}");
    }
}
