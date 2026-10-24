//! The names of the findings of a definition's full critical-pair check ([`Finding`]), by which a
//! client assumes a finding ([`BackendDefinition::data_heads_assuming`](crate::definition::BackendDefinition::data_heads_assuming)).
//! Every client that prints a finding or reads an assumed name goes through these functions, so
//! a name one client prints is the name another reads (k-rust-fuzz's `assume-joined` and
//! `definition-findings`, kink's `[spec] assume_joined`).
//!
//! A pair is named `FIRST,SECOND@POSITION`: each equation by its written position
//! `FILE:LINE:COLUMN` with the file's last path component (a compiler-generated overload axiom,
//! which has none, by `overload:GREATER:LESSER`, the K labels of its overloaded pair, each
//! quoted with `"` when it holds `,`, `:`, `@`, `"`, `\` or whitespace), and the position in the
//! first equation's left-hand side, `root` or argument indexes joined by `.`. A given name
//! matches a pair when its position is the pair's and each rule part names the equation: its
//! written position, or any trailing part of it that starts after a `/`, its unique id, its
//! label, or its overload part (with K labels or KORE names); a root pair is matched in either
//! order.
//!
//! Every other finding has a name too: an equation at an evaluated hook that is not shown to
//! agree with the hook (a hook pair, or an equation at a hook with no written meaning) is
//! `hook:EQUATION`, another equation the evaluator does not apply to every subject it describes
//! is `equation:EQUATION`, and a precondition row is `precondition:EQUATION` for the equation it
//! names, else `precondition:KIND` followed by the K labels it names
//! (`precondition:no-least-common-overload:A:B`). `EQUATION` is a rule part as above.
//!
//! Symbols are written by the caller's `label`, which maps a KORE symbol name to the K label it
//! encodes (k-rust's `kast::identifier::decode_label`, the name itself when it does not decode);
//! every client passes that decoder, so the names agree byte for byte.

use super::Finding;
use crate::{
    confluence::{UnjoinedPair, UnjoinedReason, ViolationKind},
    rule::{RewriteRule, RuleOrigin},
};

/// The written position of `rule`'s first sentence, `FILE:LINE:COLUMN`.
fn written(rule: &RewriteRule) -> Option<String> {
    rule.attributes
        .origins
        .first()
        .and_then(RuleOrigin::written_position)
}

/// `position` as a name writes it: `root`, or the argument indexes joined by `.`.
#[must_use]
pub fn position_text(position: &[usize]) -> String {
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
pub fn overload_part(rule: &RewriteRule, label: impl Fn(&str) -> String + Copy) -> Option<String> {
    let (greater, lesser) = rule.attributes.overload.as_ref()?;
    Some(format!(
        "overload:{}:{}",
        quoted(&label(greater)),
        quoted(&label(lesser))
    ))
}

/// The same part with the KORE names, which a given name may also use.
fn overload_kore_part(rule: &RewriteRule) -> Option<String> {
    let (greater, lesser) = rule.attributes.overload.as_ref()?;
    Some(format!("overload:{greater}:{lesser}"))
}

/// `text`, or `text` in `"` with `"` and `\` escaped by `\` when it holds a character a name
/// separates its parts with (`,`, `:`, `@`), a quote, a backslash or whitespace.
#[must_use]
pub fn quoted(text: &str) -> String {
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
pub fn rule_part(rule: &RewriteRule, label: impl Fn(&str) -> String + Copy) -> Option<String> {
    written(rule)
        .map(|written| match written.rsplit_once('/') {
            Some((_, file)) => file.to_owned(),
            None => written,
        })
        .or_else(|| overload_part(rule, label))
        .or_else(|| rule.attributes.label.clone())
        .or_else(|| rule.attributes.identifier().map(str::to_owned))
}

/// The name of `pair` (the module documentation), `None` when an equation has neither a written
/// position, an overloaded pair, a label nor a unique id.
pub fn pair_name(pair: &UnjoinedPair, label: impl Fn(&str) -> String + Copy) -> Option<String> {
    Some(format!(
        "{},{}@{}",
        rule_part(&pair.first, label)?,
        rule_part(&pair.second, label)?,
        position_text(&pair.position)
    ))
}

/// Whether `given`, one rule part of a name, names `rule`.
fn names_rule(given: &str, rule: &RewriteRule, label: impl Fn(&str) -> String + Copy) -> bool {
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
        || overload_part(rule, label).as_deref() == Some(given)
        || overload_kore_part(rule).as_deref() == Some(given)
}

/// Whether the name `given` names `pair` (the module documentation). A name not of the shape
/// `FIRST,SECOND@POSITION` names nothing.
pub fn names_pair(given: &str, pair: &UnjoinedPair, label: impl Fn(&str) -> String + Copy) -> bool {
    let Some((first, second, position)) = split_name(given) else {
        return false;
    };
    position.trim() == position_text(&pair.position)
        && ((names_rule(&first, &pair.first, label) && names_rule(&second, &pair.second, label))
            // A root pair is symmetric.
            || (pair.position.is_empty()
                && names_rule(&first, &pair.second, label)
                && names_rule(&second, &pair.first, label)))
}

/// The prefix of the name of a finding about one equation ([`Finding::Equation`]): `hook` for an
/// equation at an evaluated hook not shown to agree with it, `equation` otherwise.
#[must_use]
pub fn equation_prefix(pair: &UnjoinedPair) -> &'static str {
    if pair.hook.is_some() || matches!(pair.reason, UnjoinedReason::UnmodelledHook(_)) {
        "hook"
    } else {
        "equation"
    }
}

/// The kind of a precondition row as a name writes it, with the K labels it names.
pub fn precondition_kind(kind: &ViolationKind, label: impl Fn(&str) -> String + Copy) -> String {
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

/// The name of `finding` (the module documentation), `None` when an equation it names has
/// neither a written position, an overloaded pair, a label nor a unique id.
pub fn finding_name(finding: &Finding, label: impl Fn(&str) -> String + Copy) -> Option<String> {
    match finding {
        Finding::Pair { pair, .. } => pair_name(pair, label),
        Finding::Equation(pair) => Some(format!(
            "{}:{}",
            equation_prefix(pair),
            rule_part(&pair.first, label)?
        )),
        Finding::Precondition(violation) => Some(match &violation.rule {
            Some(rule) => format!("precondition:{}", rule_part(rule, label)?),
            None => format!("precondition:{}", precondition_kind(&violation.kind, label)),
        }),
    }
}

/// Whether the name `given` names `finding` (the module documentation).
pub fn names_finding(
    given: &str,
    finding: &Finding,
    label: impl Fn(&str) -> String + Copy,
) -> bool {
    match finding {
        Finding::Pair { pair, .. } => names_pair(given, pair, label),
        Finding::Equation(pair) => given
            .strip_prefix(equation_prefix(pair))
            .and_then(|rest| rest.strip_prefix(':'))
            .is_some_and(|rest| names_rule(rest, &pair.first, label)),
        Finding::Precondition(violation) => {
            given
                .strip_prefix("precondition:")
                .is_some_and(|rest| match &violation.rule {
                    Some(rule) => names_rule(rest, rule, label),
                    None => rest == precondition_kind(&violation.kind, label),
                })
        }
    }
}
