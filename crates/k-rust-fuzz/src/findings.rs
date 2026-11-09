//! The findings of a definition's full critical-pair check as a campaign states them
//! (ARCHITECTURE 4.3): their names, which `assume-joined` matches, and their report entries
//! with readable terms ([`crate::report::DefinitionFinding`]). The names are k-rust-backend's
//! (`data_term::names`), the one renderer kink's `[spec] assume_joined` reads too, called with
//! the K label decoder; this module adds the side prefixes.
//!
//! A finding is named by its kind, its sentences and a digest of the compiled sentences it is
//! about (k-rust-backend `data_term::names`, "The grammar"): `root:A,B#D` for two equations at
//! the root, `self:A#D` for an equation paired with itself, `inner:A,B@1.0#D` for an inner pair,
//! `hook:A#D`, `equation:A#D`, `precondition:A#D` or `precondition:KIND:SYMBOL..#D` for the
//! others, each sentence by its K label (`id:UNIQUE_ID` when it has none, `overload:G:L` or
//! `witness:...` for a generated one). A name given to `assume-joined` assumes the findings whose
//! name is byte-equal to it, on each definition where it is one, so it names the same compiled
//! sentences on both; it may start with `baseline:` or `mutant:` to apply on that definition
//! only. One `hook:` name covers every hook pair of its equation (one per equation of the hook's
//! written meaning). A name of the former grammar (`FIRST,SECOND@POSITION` by written
//! positions) is refused, with the names of the findings at that position now.
//!
//! Only an undecided finding can be assumed: a decided one ([`Finding::is_decided`]: a
//! precondition row that an equation is headed by a constructor or an injection, or indexed at a
//! collection or a bare variable, or an equation whose right-hand side leaves a variable
//! unbound) is a fact about the definition as written that no assumption removes, and a genuine
//! one would make the premise known to be false. Their names are refused.

use std::collections::BTreeSet;

use k_rust::{
    k_rust_backend::{
        confluence::{UnjoinedPair, Violation, ViolationKind},
        data_term::{
            DataHeads, Finding, Stuck,
            names::{self, FindingName, Refusal, Spelling},
        },
        definition::BackendDefinition,
        externalize,
        rule::{Predicate, RewriteRule, RuleOrigin, TermIndex},
        substitution::{Substitution, substitute},
        term::Term,
    },
    kast::identifier::{decode_sort_name, decode_variable, encode_variable},
    kore::ast::{Pattern as KorePattern, VariableKind},
};

use crate::{
    report::{
        DefinitionFinding, DefinitionRole, FindingInstance, FindingKind, FindingStuck,
        FindingVerdict,
    },
    source_names::SourceNames,
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

/// `name` as `assume-joined` takes it (k-rust-backend `data_term::names`, the renderer kink's
/// `[spec] assume_joined` reads too): the K spelling.
pub(crate) fn name_text(name: &FindingName) -> String {
    Spelling::k(&label).text(name)
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

/// Whether one of `assumed` (side prefixes already removed) is byte-equal to `name`, read back
/// (k-rust-backend `data_term::names::canonical`). Only an undecided finding is ever assumed
/// (`BackendDefinition::data_heads_assuming`).
pub(crate) fn assumed(assumed: &[String], name: Option<&FindingName>) -> bool {
    name.is_some_and(|name| {
        let name = name_text(name);
        assumed
            .iter()
            .any(|given| names::canonical(given).as_deref() == Some(name.as_str()))
    })
}

/// Which findings of `heads` (of `definition`) `given`, a name without a side prefix, assumes,
/// or why it is refused (k-rust-backend `data_term::names::classify`).
pub(crate) fn classify(
    given: &str,
    heads: &DataHeads,
    definition: &BackendDefinition,
) -> Result<Vec<usize>, Refusal> {
    let candidates = heads
        .named()
        .map(|(finding, name, _)| names::Candidate { finding, name })
        .collect::<Vec<_>>();
    names::classify(given, &candidates, definition, &Spelling::k(&label))
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

/// What a decided precondition row states (an equation headed by a constructor or an injection,
/// or indexed at a collection or a bare variable): the equation and the terms that are therefore
/// not distinct normal forms, so no end of the definition is data.
fn decided_fact(violation: &Violation) -> String {
    let rule = violation.rule.as_ref().map_or_else(
        || "an equation".to_owned(),
        |rule| format!("`{}`", equation(rule)),
    );
    match &violation.kind {
        ViolationKind::ConstructorHeaded(symbol) => {
            let symbol = label(symbol);
            format!(
                "{rule} rewrites a term headed by the constructor `{symbol}`, so `{symbol}` terms \
                 are not normal forms"
            )
        }
        ViolationKind::InjectionHeaded => {
            format!("{rule} rewrites a sort injection, so injected terms are not normal forms")
        }
        ViolationKind::IndexedAt(TermIndex::Variable) => format!(
            "{rule} is indexed at a bare variable and is offered at every subject, so the terms \
             it rewrites are not normal forms"
        ),
        ViolationKind::IndexedAt(index) => format!(
            "{rule} states the instances of its left-hand side, {index:?} terms, equal to its \
             right-hand side, an axiom the evaluator never applies, so those {index:?} terms are \
             not distinct normal forms"
        ),
        other => other.to_string(),
    }
}

/// [`decided_fact`] as a report reason: the fact, that no end of the definition is data, and the
/// remedy.
fn decided_reason(violation: &Violation) -> String {
    format!(
        "{}: no end of this definition is data (a fact about the definition as written, which \
         assume-joined cannot remove; change that equation)",
        decided_fact(violation)
    )
}

/// The report entries of `heads`' findings for the definition `side`, the assumed ones marked,
/// terms written with `text` where it prints them, and each equation's written position with
/// its source named by `names` ([`relative_position`]).
pub(crate) fn report(
    side: DefinitionRole,
    heads: &DataHeads,
    text: Option<&TextSyntax>,
    names: &SourceNames,
) -> Vec<DefinitionFinding> {
    heads
        .named()
        .map(|(finding, name, assumed)| entry(side, finding, name, assumed, text))
        .map(|mut entry| {
            for equation in &mut entry.equations {
                let relative = relative_position(equation, names);
                if relative != *equation {
                    entry.reason = entry.reason.replace(equation.as_str(), &relative);
                    *equation = relative;
                }
            }
            entry
        })
        .collect()
}

/// `position`, a written position `FILE:LINE:COLUMN`, with `FILE` named as the report names
/// sources: relative to the directory of the main module's file ([`SourceNames::location`];
/// FZ-REPLAY-WHOLE S1), so that a finding names no directory the definition was compiled in.
/// Any other text (a label or a unique id naming an equation without a position) is kept.
fn relative_position(position: &str, names: &SourceNames) -> String {
    let mut parts = position.rsplitn(3, ':');
    match (parts.next(), parts.next(), parts.next()) {
        (Some(column), Some(line), Some(file))
            if [column, line]
                .iter()
                .all(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit())) =>
        {
            format!("{}:{line}:{column}", names.location(file))
        }
        _ => position.to_owned(),
    }
}

fn entry(
    side: DefinitionRole,
    finding: &Finding,
    name: Option<&FindingName>,
    assumed: bool,
    text: Option<&TextSyntax>,
) -> DefinitionFinding {
    let name = name.map(name_text);
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
            name,
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
            name,
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
            pair_entry(side, verdict, pair, name, instance.as_ref(), assumed, text)
        }
    }
}

/// A KORE symbol name as the K label it encodes.
fn label(name: &str) -> String {
    k_rust::kast::identifier::label_or_name(name)
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

/// The reason of a genuine pair finding: what its instance's two values are.
fn genuine_reason(instance: &FindingInstance) -> String {
    let order = "k-rust's result for it depends on the order it tries the equations";
    let partial = instance
        .stuck
        .iter()
        .position(|stuck| *stuck == Some(FindingStuck::Partial));
    match partial {
        Some(undefined) => format!(
            "at {} both equations apply; one result is the normal form {}, the other, {}, holds \
             an application of a partial function that no equation rewrites, undefined in the \
             normal-form reading: {order}",
            instance.overlap,
            instance.values[1 - undefined],
            instance.values[undefined]
        ),
        None => format!(
            "at {} both equations apply and the input has two normal forms, {} and {}: {order}",
            instance.overlap, instance.values[0], instance.values[1]
        ),
    }
}

/// The report entry of a pair finding (see [`entry`]).
fn pair_entry(
    side: DefinitionRole,
    verdict: FindingVerdict,
    pair: &UnjoinedPair,
    name: Option<String>,
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
        // The input written apart from a value that would print alike (an overload application
        // against its stuck lowering, `Cgascap_Gas(S, inj(-1), ..)` against `Cgascap_Int(S, -1,
        // ..)`).
        let written = show(&instance.overlap);
        let overlap = if written == left {
            names
                .show_apart(&instance.overlap, &instance.values.0, text)
                .0
        } else if written == right {
            names
                .show_apart(&instance.overlap, &instance.values.1, text)
                .0
        } else {
            written
        };
        FindingInstance {
            assignment: instance
                .assignment
                .iter()
                .map(|(variable, value)| {
                    format!("{} = {}", readable_variable(&variable.name), show(value))
                })
                .collect(),
            overlap,
            values: vec![left, right],
            stuck: [instance.stuck.0, instance.stuck.1]
                .into_iter()
                .map(|stuck| {
                    stuck.map(|stuck| match stuck {
                        Stuck::Total => FindingStuck::Total,
                        Stuck::Partial => FindingStuck::Partial,
                    })
                })
                .collect(),
        }
    });
    DefinitionFinding {
        side,
        verdict,
        kind: FindingKind::Pair,
        name,
        equations: vec![equation(&pair.first), equation(&pair.second)],
        position: Some(names::position_text(&pair.position)),
        reason: match &instance {
            Some(instance) => genuine_reason(instance),
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

    use super::{classify, entry, name_text};
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
        let (finding, named, _) = heads
            .named()
            .find(|(finding, _, _)| finding.is_decided())
            .expect("a decided finding");
        let report = entry(DefinitionRole::Baseline, finding, named, false, None);
        assert_eq!(report.verdict, FindingVerdict::Decided);
        assert_eq!(report.kind, FindingKind::Equation);
        assert!(
            report.reason.contains("leaves `Y` unbound") && report.reason.contains("change that"),
            "{}",
            report.reason
        );
        let name = name_text(named.expect("named"));
        // kink-native `tests/data.rs` reads the same name (fz26 KINK-BASELINE-FINDINGS review N4).
        assert!(name.starts_with("equation:any-unbound#"), "{name}");
        assert_eq!(report.name.as_deref(), Some(name.as_str()));
        let refusal = classify(&name, &heads, &definition).expect_err("refused");
        assert_eq!(refusal.reason(), "decided");
        assert!(
            refusal.detail(&name).contains("decided finding"),
            "{}",
            refusal.detail(&name)
        );
    }

    /// S2B-T3: a genuine pair whose second reduct holds a stuck partial application under a
    /// constructor (`s(V) = failed` beside `s(V) = bound(nb(V))`, `nb` partial without an
    /// equation) reports `stuck` per value, `null` and `partial`, and a reason that names the
    /// undefined value as such rather than as a normal form.
    #[test]
    fn an_undefined_side_is_reported_as_partial() {
        use crate::report::FindingStuck;
        const FIXTURE: &str =
            include_str!("../../k-rust-backend/tests/fixtures/overloaded-list-owise.kore");
        let (head, tail) = FIXTURE.rsplit_once("endmodule").expect("one module");
        let equation = |rhs: &str, label: &str| {
            format!(
                r#"
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortVal{{}}, R}}(X0:SortVal{{}}, V:SortVal{{}}), \top{{R}}())),
        \equals{{SortState{{}}, R}}(s{{}}(X0:SortVal{{}}), \and{{SortState{{}}}}({rhs}, \top{{SortState{{}}}}())))
        [label{{}}("{label}")]
"#
            )
        };
        let source = format!(
            "{head}
    symbol nb{{}}(SortVal{{}}) : SortVal{{}} [function{{}}()]
    symbol s{{}}(SortVal{{}}) : SortState{{}} [function{{}}(), total{{}}()]
{}{}
endmodule{tail}",
            equation("failed{}()", "s-failed"),
            equation("bound{}(nb{}(V:SortVal{}))", "s-nb"),
        );
        let syntax = parse_definition(&source).expect("parses");
        let definition =
            BackendDefinition::internalize(&syntax, "OVERLOADED-LIST-OWISE").expect("loads");
        let heads = definition.data_heads();
        let (finding, name, _) = heads
            .named()
            .find(|(finding, _, _)| finding.is_genuine())
            .expect("a genuine finding");
        let report = entry(DefinitionRole::Baseline, finding, name, false, None);
        assert_eq!(report.verdict, FindingVerdict::Genuine);
        let instance = report.instance.as_ref().expect("the instance");
        let undefined = usize::from(instance.stuck[0].is_none());
        assert_eq!(
            instance.stuck[undefined],
            Some(FindingStuck::Partial),
            "{instance:?}"
        );
        assert_eq!(instance.stuck[1 - undefined], None, "{instance:?}");
        assert!(instance.values[undefined].contains("nb"), "{instance:?}");
        assert!(
            report.reason.contains(&format!(
                "one result is the normal form {}, the other, {}, holds an application of a \
                 partial function",
                instance.values[1 - undefined],
                instance.values[undefined]
            )),
            "{}",
            report.reason
        );
    }

    /// INT8 follow-ups review round 2 (R2-B1): a pinned injective row is an overload premise,
    /// not a decided fact: its report entry is `undecided` with the row's own text, and its
    /// name is one `assume-joined` accepts.
    #[test]
    fn a_pinned_injective_row_is_undecided_and_its_name_accepted() {
        use k_rust::k_rust_backend::{
            confluence::{Violation, ViolationKind},
            data_term::Finding,
        };
        const FIXTURE: &str =
            include_str!("../../k-rust-backend/tests/fixtures/overloaded-list-owise.kore");
        let definition = BackendDefinition::internalize(
            &parse_definition(FIXTURE).expect("parses"),
            "OVERLOADED-LIST-OWISE",
        )
        .expect("loads");
        let finding = Finding::Precondition(Violation {
            rule: None,
            kind: ViolationKind::PinnedByInjectiveTotal("Lblenc".into()),
        });
        assert!(!finding.is_decided());
        let named = k_rust::k_rust_backend::data_term::names::finding_name(&definition, &finding)
            .expect("named");
        let report = entry(
            DefinitionRole::Baseline,
            &finding,
            Some(&named),
            false,
            None,
        );
        assert_eq!(report.verdict, FindingVerdict::Undecided);
        assert!(
            report.reason.contains("total and injective"),
            "{}",
            report.reason
        );
        let name = report.name.expect("named");
        assert!(
            name.starts_with("precondition:pinned-by-injective-total:enc#"),
            "{name}"
        );
        assert!(super::assumed(std::slice::from_ref(&name), Some(&named)));
    }
}
