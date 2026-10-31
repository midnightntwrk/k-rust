//! Literals whose element the definition leaves open (`builtin::ChosenClass::Literal`).
//!
//! A literal gets its element when its text is internalized (`Term::domain_value_of`), so no
//! evaluation can leave it open or mark it. The literal rules leave open the element of a Float
//! literal at a tie of "nearest", at or beyond half an ulp past the largest finite value, of a
//! nonzero value that rounds to a zero and of an `Infinity` lexeme
//! ([`crate::builtin::float_literal_open`]), and of a machine-integer literal its width cannot
//! hold (`term::mint_literal_open`); k-rust builds its own element of each.
//!
//! So the text is classified where it is read: every internalization of a sentence or a request
//! runs [`recording`], and [`observe`], called on every domain value read from text, adds the
//! open ones to the innermost recording. The load stores a sentence's in
//! `ComputedRuleAttributes::open_literals`; a claim holding one is refused
//! (`definition::UnstatedDefinedness::OpenLiteral`); a request's are refused or, for an
//! execution, marked on every leaf (`definition::Admitted`). An attempt of a rule or an equation
//! holding one asks [`withheld`]: an execution marks it, with the rule's `UNIQUE_ID`, and goes on;
//! every other evaluation stops the attempt there, undecided.
//!
//! No hook builds a `Float` from text: `STRING.string2float` and `STRING.float2string` have no
//! evaluator (their applications are the unsupported-hook outcome). An evaluator added for them
//! must classify `String2Float`'s argument by [`crate::builtin::float_literal_open`] (class
//! `literal` or a hook class, marked in an execution and withheld elsewhere), and treat
//! `Float2String`'s spelling of every value as open: the round trip `domains.md` states fixes
//! the value a text reads back as, not the text.

use std::{cell::RefCell, sync::Arc};

use crate::{
    builtin::{ChosenClass, ChosenValue},
    definition::BackendDefinition,
    evaluation::EvaluationMode,
    path_facts::PathFact,
    term::{DomainKind, Term, TermKind},
};

/// Whether the domain value text `text` of `kind` names an element the literal rules leave open.
pub fn open(kind: DomainKind, text: &str) -> bool {
    match kind {
        DomainKind::Float => crate::builtin::float_literal_open(text),
        DomainKind::MInt(width) => crate::term::mint_literal_open(text, width),
        DomainKind::Int
        | DomainKind::Bool
        | DomainKind::String
        | DomainKind::Bytes
        | DomainKind::Token => false,
    }
}

std::thread_local! {
    /// The open literals each recording open on this thread has observed, innermost last.
    static RECORDINGS: RefCell<Vec<Vec<Arc<str>>>> = const { RefCell::new(Vec::new()) };
}

/// Run `action`, an internalization, and return with its result the distinct open literals it
/// read, as written, in first-read order. A recording opened inside `action` keeps its own.
pub(crate) fn recording<T>(action: impl FnOnce() -> T) -> (T, Vec<Arc<str>>) {
    struct Frame;
    impl Drop for Frame {
        fn drop(&mut self) {
            RECORDINGS.with_borrow_mut(|frames| {
                frames.pop();
            });
        }
    }
    RECORDINGS.with_borrow_mut(|frames| frames.push(Vec::new()));
    let frame = Frame;
    let result = action();
    let literals = RECORDINGS.with_borrow_mut(|frames| {
        std::mem::take(frames.last_mut().expect("the recording's frame"))
    });
    drop(frame);
    (result, literals)
}

/// Note that the text `text` of a domain value of `kind` was read, for the innermost recording.
pub(crate) fn observe(kind: DomainKind, text: &[u8]) {
    if !matches!(kind, DomainKind::Float | DomainKind::MInt(_))
        || RECORDINGS.with_borrow(Vec::is_empty)
    {
        return;
    }
    let Ok(text) = std::str::from_utf8(text) else {
        return;
    };
    if !open(kind, text) {
        return;
    }
    RECORDINGS.with_borrow_mut(|frames| {
        let frame = frames.last_mut().expect("a recording is open");
        if !frame.iter().any(|seen| &**seen == text) {
            frame.push(Arc::from(text));
        }
    });
}

/// Whether the domain value `term` may be an open literal's element: one of `Float` or
/// machine-integer sort, or of a sort whose kind the definition does not name (a sort-parametric
/// value, say).
fn may_be_open(definition: &BackendDefinition, term: &Term) -> bool {
    matches!(term.kind(), TermKind::DomainValue { sort, .. }
    if !matches!(
        definition.domain_kind(sort),
        Some(
            DomainKind::Int
                | DomainKind::Bool
                | DomainKind::String
                | DomainKind::Bytes
                | DomainKind::Token
        )
    ))
}

/// `term` with every domain value that may be an open literal's element ([`may_be_open`])
/// replaced by a variable of its sort, each its own, named apart from the variables of `term` and
/// of `subject`. In every model of the literals' elements the term's instances are instances of
/// this pattern (a variable of the value's sort matches whatever the value matches), so where it
/// does not match a subject, the term matches it in none: a proof route reads a failed match of
/// it as the rule's refutation (`rewrite::apply`).
pub(crate) fn generalized(definition: &BackendDefinition, term: &Term, subject: &Term) -> Term {
    let taken = term
        .attributes()
        .variables
        .iter()
        .chain(subject.attributes().variables.iter())
        .map(|variable| variable.name.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let mut next = 0usize;
    let mut fresh = |sort: crate::term::Sort| loop {
        let name = crate::term::Name::from(format!("VarLiteral{next}"));
        next += 1;
        if !taken.contains(&name) {
            return Term::variable(crate::term::Variable::new(name, sort));
        }
    };
    fn walk(
        definition: &BackendDefinition,
        term: &Term,
        fresh: &mut impl FnMut(crate::term::Sort) -> Term,
    ) -> Term {
        if may_be_open(definition, term) {
            return fresh(term.sort());
        }
        term.try_map_children::<std::convert::Infallible>(|child| {
            Ok(walk(definition, child, fresh))
        })
        .unwrap_or_else(|never| match never {})
    }
    walk(definition, term, &mut fresh)
}

/// Whether `term` holds a domain value of a sort whose literals can be open (`Float`, a machine
/// integer, or a sort whose kind the definition does not name): the only terms an open literal
/// can have put in a sentence's internalized term. A term holding none matches a subject, and is
/// indexed, the same whatever element a literal of its sentence names. Evaluated once per
/// left-hand side at load (`rule::internalize_axiom`).
pub(crate) fn may_hold_open_literal(definition: &BackendDefinition, term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if may_be_open(definition, term) {
            return true;
        }
        pending.extend(crate::term::immediate_children(term.kind()));
    }
    false
}

/// The mark of an open literal: `hook` is the `UNIQUE_ID` of the rule or equation holding it, or,
/// for a request's own literal, the literal as written.
pub(crate) fn mark(hook: &str) -> ChosenValue {
    ChosenValue::new(Arc::from(hook), ChosenClass::Literal)
}

/// Whether an attempt of the sentence `unique_id`, which holds `open_literals`, stops here. In an
/// execution it goes on with k-rust's element of each literal, and the attempt is marked from its
/// own scope, whatever becomes of it (a failed match also read the literal). Every other
/// evaluation stops the attempt, undecided: a proof, an implication or a load analysis must not
/// rest on an element the definition does not fix, and a skipped attempt would be read as a rule
/// that does not apply.
pub(crate) fn withheld(open_literals: &[Arc<str>], unique_id: &str) -> bool {
    if open_literals.is_empty() {
        return false;
    }
    if crate::evaluation::current() == EvaluationMode::Execution {
        crate::path_facts::note(PathFact::ChosenValue(mark(unique_id)));
        false
    } else {
        true
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, sync::Arc};

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use crate::{
        builtin::ChosenClass,
        confluence::{CheckScope, UnjoinedReason},
        definition::{BackendDefinition, DefinitionError, RequestLiterals},
        evaluation::{EvaluationMode, with_evaluation},
        simplify::SimplificationOptions,
        term::{Term, TermKind},
    };

    /// The nullary function `name` at `sort` and its one equation `name() = value`, with the
    /// `UNIQUE_ID` `name`.
    fn constant(name: &str, sort: &str, value: &str) -> String {
        format!(
            r#"symbol {name}{{}}() : {sort} [function{{}}(), total{{}}()]
            axiom{{R}} \implies{{R}}(
                \and{{R}}(\top{{R}}(), \top{{R}}()),
                \equals{{{sort}, R}}({name}{{}}(), \and{{{sort}}}(\dv{{{sort}}}("{value}"), \top{{{sort}}}()))
            ) [label{{}}("{name}"), UNIQUE'Unds'ID{{}}("{name}")]"#
        )
    }

    /// Equations whose literal's element the literal rules leave open (`big`, `wide`) beside
    /// determined ones (`near`, between the largest finite value and the overflow threshold;
    /// `narrow`, the least 8-bit integer).
    fn definition() -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortFloat{{}} [hook{{}}("FLOAT.Float"), hasDomainValues{{}}()]
                hooked-sort SortMInt{{S}} [hook{{}}("MINT.MInt"), hasDomainValues{{}}()]
                sort Sort8{{}} []
                {}
                {}
                {}
                {}
            endmodule []"#,
            constant("big", "SortFloat{}", "1.0e400"),
            constant("near", "SortFloat{}", "1.7976931348623158e308"),
            constant("wide", "SortMInt{Sort8{}}", "256p8"),
            constant("narrow", "SortMInt{Sort8{}}", "-128p8"),
        );
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .admit_unverified(&parse_pattern(source).unwrap(), &[])
            .internalize_term()
            .unwrap()
    }

    #[test]
    fn the_load_records_the_open_literals_of_each_sentence_as_written() {
        let definition = definition();
        let recorded = definition
            .function_theory()
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(|rule| {
                (
                    rule.attributes.unique_id.clone(),
                    rule.computed_attributes.open_literals.to_vec(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let literal = |text: &str| vec![Arc::<str>::from(text)];
        assert_eq!(
            recorded,
            BTreeMap::from([
                ("big".to_owned(), literal("1.0e400")),
                ("near".to_owned(), Vec::new()),
                ("wide".to_owned(), literal("256p8")),
                ("narrow".to_owned(), Vec::new()),
            ])
        );
    }

    /// An execution evaluates an equation holding an open literal with k-rust's element and
    /// marks the attempt; every other evaluation leaves the application unevaluated, and an
    /// equation of determined literals is evaluated in every mode.
    #[test]
    fn an_equation_holding_an_open_literal_is_marked_in_an_execution_and_withheld_elsewhere() {
        let definition = definition();
        let simplified = |mode, name: &str| {
            let subject = term(&definition, &format!("{name}{{}}()"));
            with_evaluation(mode, || {
                crate::path_facts::run(|| {
                    crate::path_facts::collect(|| {
                        crate::simplify::simplify(
                            &definition,
                            &subject,
                            SimplificationOptions::default(),
                        )
                        .unwrap()
                        .unwrap()
                        .term
                    })
                    .0
                })
            })
        };
        let marks = |facts: &[crate::path_facts::PathFact]| {
            facts
                .iter()
                .filter_map(crate::path_facts::PathFact::chosen_value)
                .map(|chosen| (chosen.hook.to_string(), chosen.class))
                .collect::<Vec<_>>()
        };
        for name in ["big", "wide"] {
            let (proof, facts) = simplified(EvaluationMode::Proof, name);
            assert!(
                matches!(proof.kind(), TermKind::Application { .. }),
                "{name}: {proof:?}"
            );
            assert!(marks(&facts).is_empty(), "{name}: {facts:?}");
            let (execution, facts) = simplified(EvaluationMode::Execution, name);
            assert!(
                matches!(execution.kind(), TermKind::DomainValue { .. }),
                "{name}: {execution:?}"
            );
            assert_eq!(marks(&facts), [(name.to_owned(), ChosenClass::Literal)]);
        }
        for name in ["near", "narrow"] {
            for mode in [EvaluationMode::Proof, EvaluationMode::Execution] {
                let (value, facts) = simplified(mode, name);
                assert!(
                    matches!(value.kind(), TermKind::DomainValue { .. }),
                    "{name}: {value:?}"
                );
                assert!(marks(&facts).is_empty(), "{name}: {facts:?}");
            }
        }
    }

    /// The critical-pair check joins an equation holding an open literal with nothing: it is
    /// reported on its own, naming the literal.
    #[test]
    fn the_critical_pair_check_reports_an_equation_holding_an_open_literal() {
        let definition = definition();
        let claims = definition.value_claims_in_scope(CheckScope::All);
        let reported = claims
            .unjoined()
            .iter()
            .map(|pair| (pair.first.attributes.unique_id.clone(), pair.reason.clone()))
            .collect::<Vec<_>>();
        assert_eq!(
            reported,
            [
                (
                    "big".to_owned(),
                    UnjoinedReason::OpenLiteral("1.0e400".to_owned())
                ),
                (
                    "wide".to_owned(),
                    UnjoinedReason::OpenLiteral("256p8".to_owned())
                ),
            ]
        );
        assert!(
            claims
                .unjoined()
                .iter()
                .all(|pair| pair.reason.describes_one_equation())
        );
    }

    /// `f(c(literal)) = 1` (`a`) beside the `anywhere` equation `c(MAX) = m(MAX)` (`b`), where
    /// `c` is an `anywhere` head, `m` a constructor and `f` a total function.
    fn overlapping(literal: &str) -> BackendDefinition {
        let source = format!(
            r#"[]
            module MAIN
                hooked-sort SortFloat{{}} [hook{{}}("FLOAT.Float"), hasDomainValues{{}}()]
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                sort SortS{{}} []
                symbol c{{}}(SortFloat{{}}) : SortS{{}} [anywhere{{}}()]
                symbol m{{}}(SortFloat{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol f{{}}(SortS{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortS{{}}, R}}(X0:SortS{{}}, c{{}}(\dv{{SortFloat{{}}}}("{literal}"))), \top{{R}}())),
                    \equals{{SortInt{{}}, R}}(f{{}}(X0:SortS{{}}), \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("1"), \top{{SortInt{{}}}}()))
                ) [UNIQUE'Unds'ID{{}}("a")]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortFloat{{}}, R}}(X0:SortFloat{{}}, \dv{{SortFloat{{}}}}("1.7976931348623157e308")), \top{{R}}())),
                    \equals{{SortS{{}}, R}}(c{{}}(X0:SortFloat{{}}), \and{{SortS{{}}}}(m{{}}(X0:SortFloat{{}}), \top{{SortS{{}}}}()))
                ) [anywhere{{}}(), UNIQUE'Unds'ID{{}}("b")]
            endmodule []"#
        );
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap()
    }

    /// The critical-pair check computes no overlap of `a` and `b` where `a`'s literal is
    /// `1.0e400`: k-rust's element, infinity, is apart from MAX, while in the model where the
    /// literal is MAX the two overlap at `f(c(MAX))` (`1` against `f(m(MAX))`). Seeding `a` alone
    /// taints `c`, which `a` mentions, and so `b`, whose left-hand side is rooted at `c`, as
    /// seeding that pair would (`confluence.rs`, the `OpenLiteral` report). With `1.0`, apart
    /// from MAX in every model, `c` keeps its claims.
    #[test]
    fn an_open_literal_taints_the_equations_its_element_may_overlap() {
        let name = |text: &str| crate::term::Name::from(text);
        let open = overlapping("1.0e400").value_claims_in_scope(CheckScope::All);
        assert!(open.tainted_symbols().contains(&name("c")), "{open:?}");
        let report = open
            .unjoined()
            .iter()
            .find(|pair| pair.reason == UnjoinedReason::OpenLiteral("1.0e400".to_owned()))
            .expect("the open equation is reported");
        assert!(report.withdrawn.contains(&name("c")), "{report:?}");
        let determined = overlapping("1.0").value_claims_in_scope(CheckScope::All);
        assert!(
            !determined.tainted_symbols().contains(&name("c")),
            "{determined:?}"
        );
    }

    /// A request's open literal is refused unless the request is an execution's, which collects
    /// it as written.
    #[test]
    fn a_request_holding_an_open_literal_is_refused_outside_an_execution() {
        let definition = definition();
        for (source, literal) in [
            (r#"\dv{SortFloat{}}("Infinity")"#, "Infinity"),
            (
                r#"\dv{SortFloat{}}("9007199254740993")"#,
                "9007199254740993",
            ),
            (r#"\dv{SortMInt{Sort8{}}}("0377p8")"#, "0377p8"),
        ] {
            let syntax = parse_pattern(source).unwrap();
            assert_eq!(
                definition.admit_unverified(&syntax, &[]).internalize_term(),
                Err(DefinitionError::OpenLiteral(literal.to_owned()))
            );
            let literals = RequestLiterals::new();
            definition
                .admit_unverified(&syntax, &[])
                .for_execution(&literals)
                .internalize_term()
                .unwrap();
            assert_eq!(literals.to_vec(), [Arc::<str>::from(literal)]);
        }
        let syntax = parse_pattern(r#"\dv{SortMInt{Sort8{}}}("255p8")"#).unwrap();
        assert!(
            definition
                .admit_unverified(&syntax, &[])
                .internalize_term()
                .is_ok()
        );
    }
}
