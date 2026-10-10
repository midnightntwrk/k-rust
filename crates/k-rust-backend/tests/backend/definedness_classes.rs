//! Class tests of the definedness cluster (`draft/open-issues-2026-10/tickets/definedness-tickets.md`).
//!
//! Each test states one invariant that follows from what the construct means, and checks krust
//! against itself on small definitions; none compares with another implementation. They are
//! ignored until the ticket that fixes their class lands, and each fails on `934d29e7`.
//!
//! - An equation states nothing at an undefined argument: it binds each argument by membership
//!   in its argument pattern, and an undefined term is a member of no pattern. So a step never
//!   drops an argument subterm whose definedness it cannot show; it keeps the subterm or carries
//!   its `\ceil`, whether the equation consumes that subterm with a variable or with a pattern.
//! - A pattern denotes the values it can be instantiated to, so an application of a computed
//!   symbol in a pattern matches the value it computes, as the same pattern with that value
//!   written in its place does.
//! - The taint closure is a least fixpoint of its rules: an equation whose left-hand side
//!   mentions a withdrawn symbol is withdrawn (T1), and an equation the check does not reason
//!   about is withdrawn like a pair that does not join.
//! - The critical pairs the check classifies include every two equations the evaluator can offer
//!   at one subject.
//! - Every admission route refuses the patterns the verifier refuses for their sorts.
//! - An equation applies to a term when one of its instances does, whichever instance the
//!   matcher enumerates first.

use std::collections::BTreeSet;

use k_rust_backend::{
    confluence::ViolationKind,
    definition::BackendDefinition,
    externalize,
    rewrite::Pattern,
    rule::{RuleRhs, TermIndex},
    simplify::SimplificationOptions,
    term::{HeadRole, Term, TermKind},
};
use k_rust_kore::kore::{
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

use crate::support::{internal_term, unstopped};

const PRELUDE: &str = r#"
    sort SortKItem{} []
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    symbol inj{From, To}(From) : To [sortInjection{}()]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    sort SortFoo{} []
    sort SortS{} []
    axiom{R} \exists{R}(Value:SortKItem{},
        \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortFoo{}, SortKItem{}}(From:SortFoo{})))
        [subsort{SortFoo{}, SortKItem{}}()]
    axiom{R} \exists{R}(Value:SortKItem{},
        \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
        [subsort{SortInt{}, SortKItem{}}()]
    symbol c{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol d{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol one{}() : SortS{} [constructor{}(), functional{}(), injective{}()]

    hooked-sort SortMap{}
      [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
       concat{}(Lbl'Unds'Map'Unds'{}())]
    hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
      [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
      [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

    hooked-sort SortSet{}
      [hook{}("SET.Set"), unit{}(Lbl'Stop'Set{}()), element{}(LblSetItem{}()),
       concat{}(Lbl'Unds'Set'Unds'{}())]
    hooked-symbol Lbl'Stop'Set{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{}
      [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{}
      [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

    hooked-sort SortList{}
      [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
       concat{}(Lbl'Unds'List'Unds'{}())]
    hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
      [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
      [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
"#;

const TOP: &str = r"\top{R}()";

/// A definition: the prelude, then `declarations` and `axioms`, in module `MAIN`.
fn definition(declarations: &str, axioms: &[String]) -> BackendDefinition {
    let source = format!(
        "[] module MAIN {PRELUDE} {declarations} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the fixture parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the fixture internalizes")
}

/// The equation `head(X0, ..., Xn) = right`, each `Xi` bound to `patterns[i]` of sort
/// `sorts[i]`, under `requires` (a KORE predicate, or [`TOP`]) and the axiom attributes
/// `attributes`.
fn equation(
    head: &str,
    sorts: &[&str],
    result: &str,
    patterns: &[&str],
    right: &str,
    requires: &str,
    attributes: &str,
) -> String {
    let memberships = sorts.iter().zip(patterns).enumerate().rev().fold(
        TOP.to_owned(),
        |rest, (index, (sort, pattern))| {
            format!(r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {pattern}), {rest})")
        },
    );
    let parameters = sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("X{index}:{sort}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({right}, \top{{{result}}}()))) [{attributes}]"
    )
}

/// An unconditional `anywhere` equation.
fn anywhere(head: &str, sorts: &[&str], result: &str, patterns: &[&str], right: &str) -> String {
    equation(head, sorts, result, patterns, right, TOP, "anywhere{}()")
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

fn printed_term(term: &Term) -> String {
    Printer::compact().print_pattern(&externalize::term(term))
}

/// The simplification of `subject`, printed with the conditions it carries.
fn simplified(definition: &BackendDefinition, subject: &str) -> String {
    let term = internal_term(definition, subject);
    match unstopped::simplify(definition, &term, SimplificationOptions::default()) {
        Ok(simplification) => {
            let pattern = Pattern {
                term: simplification.term.clone(),
                constraints: simplification.constraints().to_vec(),
            };
            Printer::compact().print_pattern(&externalize::constrained_pattern(&pattern))
        }
        Err(error) => format!("error: {error:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// DF-1: a step never drops an argument subterm whose definedness it cannot show.

/// A partial function `pf`, defined at `c` only, so `pf(d)` is undefined: no equation reduces
/// it, and a declared function's application no equation reduces is `\bottom`.
const PARTIAL: &str = r"
    symbol box{}(SortFoo{}) : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol pf{}(SortFoo{}) : SortFoo{} [function{}()]
    symbol fv{}(SortFoo{}) : SortS{} [function{}()]
    symbol fa{}(SortFoo{}, SortFoo{}) : SortS{} [function{}()]
    symbol fb{}(SortFoo{}, SortFoo{}) : SortS{} [function{}()]
    symbol fk{}(SortFoo{}, SortMap{}) : SortS{} [function{}()]
    symbol fs{}(SortFoo{}, SortSet{}) : SortS{} [function{}()]
";

fn pf_equation() -> String {
    equation(
        "pf",
        &["SortFoo{}"],
        "SortFoo{}",
        &["c{}()"],
        "c{}()",
        TOP,
        "",
    )
}

fn function_equation(head: &str, sorts: &[&str], patterns: &[&str]) -> String {
    equation(head, sorts, "SortS{}", patterns, "one{}()", TOP, "")
}

/// Each case: a label, the definition, the subject, and the subterm `u` of the subject whose
/// definedness nothing shows.
fn consumed_subterm_cases() -> Vec<(&'static str, BackendDefinition, String, String)> {
    let pf_d = "pf{}(d{}())".to_owned();
    let partial = |head: &str, sorts: &[&str], patterns: &[&str]| {
        definition(
            PARTIAL,
            &[pf_equation(), function_equation(head, sorts, patterns)],
        )
    };
    let key = |key: &str| {
        format!(
            "Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}({key}), inj{{SortFoo{{}}, SortKItem{{}}}}(c{{}}()))"
        )
    };
    let element =
        |element: &str| format!("LblSetItem{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}({element}))");
    vec![
        // The control: a variable consumes `pf(d)`, and the step carries `\ceil(pf(d))`.
        (
            "variable",
            partial("fv", &["SortFoo{}"], &["VarX:SortFoo{}"]),
            "fv{}(pf{}(d{}()))".to_owned(),
            pf_d.clone(),
        ),
        (
            "argument pattern",
            partial(
                "fa",
                &["SortFoo{}", "SortFoo{}"],
                &["VarX:SortFoo{}", "pf{}(VarX:SortFoo{})"],
            ),
            "fa{}(d{}(), pf{}(d{}()))".to_owned(),
            pf_d.clone(),
        ),
        (
            "below a constructor",
            partial(
                "fb",
                &["SortFoo{}", "SortFoo{}"],
                &["VarX:SortFoo{}", "box{}(pf{}(VarX:SortFoo{}))"],
            ),
            "fb{}(d{}(), box{}(pf{}(d{}())))".to_owned(),
            pf_d.clone(),
        ),
        (
            "map key",
            partial(
                "fk",
                &["SortFoo{}", "SortMap{}"],
                &[
                    "VarX:SortFoo{}",
                    "Lbl'Unds'Map'Unds'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortFoo{}, SortKItem{}}(pf{}(VarX:SortFoo{})), VarV:SortKItem{}), VarM:SortMap{})",
                ],
            ),
            format!("fk{{}}(d{{}}(), {})", key("pf{}(d{}())")),
            pf_d.clone(),
        ),
        (
            "set element",
            partial(
                "fs",
                &["SortFoo{}", "SortSet{}"],
                &[
                    "VarX:SortFoo{}",
                    "Lbl'Unds'Set'Unds'{}(LblSetItem{}(inj{SortFoo{}, SortKItem{}}(pf{}(VarX:SortFoo{}))), VarS:SortSet{})",
                ],
            ),
            format!("fs{{}}(d{{}}(), {})", element("pf{}(d{}())")),
            pf_d,
        ),
        // Evaluator limit 1: `h(m(0), Y) = Y` makes `g(c) = g(h(m(0), c)) = m(1 /Int 0)`
        // undefined in every model; the pair of `g`'s and `h`'s equations does not join, so `g`
        // has no claim, and `k(g(c)) = d` consumes `g(c)` with its pattern.
        (
            "withdrawn equation head",
            definition(
                r"
                symbol m{}(SortInt{}) : SortFoo{} [constructor{}(), functional{}(), injective{}()]
                symbol h{}(SortFoo{}, SortFoo{}) : SortFoo{} [anywhere{}(), value-production{}()]
                symbol g{}(SortFoo{}) : SortFoo{} [anywhere{}(), value-production{}()]
                symbol k{}(SortFoo{}) : SortFoo{} [anywhere{}(), value-production{}()]
                ",
                &[
                    equation(
                        "h",
                        &["SortFoo{}", "SortFoo{}"],
                        "SortFoo{}",
                        &["m{}(VarI:SortInt{})", "VarY:SortFoo{}"],
                        "VarY:SortFoo{}",
                        &format!(
                            r#"\equals{{SortBool{{}}, R}}(eqInt{{}}(VarI:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true"))"#,
                            int(0)
                        ),
                        "anywhere{}()",
                    ),
                    anywhere(
                        "g",
                        &["SortFoo{}"],
                        "SortFoo{}",
                        &[&format!("h{{}}(m{{}}({}), VarY:SortFoo{{}})", int(0))],
                        &format!("m{{}}(divInt{{}}({}, {}))", int(1), int(0)),
                    ),
                    anywhere("k", &["SortFoo{}"], "SortFoo{}", &["g{}(c{}())"], "d{}()"),
                ],
            ),
            "k{}(g{}(c{}()))".to_owned(),
            "g{}(c{}())".to_owned(),
        ),
    ]
}

/// An equation binds each argument of its head by membership in its argument pattern, and an
/// undefined term is a member of no pattern, so a step at a subject one of whose argument
/// subterms `u` may be undefined either is not taken (the result still holds `u`) or carries
/// `\ceil(u)` (a constraint mentions `u`). That does not depend on whether the equation consumes
/// `u` with a variable or with a pattern; the variable case is the control.
#[test]
#[ignore = "reproduces FOLLOWUPS: Evaluator limit 1 (argument patterns); Evaluator limit 2 (below-root applications); Unjustified positions for a function symbol on a collection hook's left side"]
fn a_step_keeps_or_carries_every_consumed_subterm_it_cannot_show_defined() {
    let mut failures = Vec::new();
    for (label, definition, subject, undefined) in consumed_subterm_cases() {
        let printed_undefined = printed_term(&internal_term(&definition, &undefined));
        let result = simplified(&definition, &subject);
        if !result.contains(&printed_undefined) {
            failures.push(format!(
                "{label}: {subject} simplifies to {result}, which neither holds nor carries the definedness of {printed_undefined}"
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// A pattern denotes the values its instances take, so an application of the partial function
/// `pf` in a pattern matches the value it computes: with `pf(c) = c`, the subject `fa(c, c)`
/// is an instance of `fa(X, pf(X))` at `X = c`, as it is of `fa(X, c)`, and so for a map key and
/// a set element. The subject is written `fa(c, pf(c))` and evaluates innermost to `fa(c, c)`.
#[test]
#[ignore = "reproduces FOLLOWUPS: Evaluator limit 2 (below-root applications); Unjustified positions for a function symbol on a collection hook's left side"]
fn a_computed_pattern_position_matches_the_value_it_computes() {
    let mut failures = Vec::new();
    let one = printed_term(&internal_term(&definition(PARTIAL, &[]), "one{}()"));
    for (label, definition, subject, _) in consumed_subterm_cases()
        .into_iter()
        .filter(|(label, ..)| ["argument pattern", "map key", "set element"].contains(label))
    {
        let subject = subject.replace("d{}()", "c{}()");
        let result = simplified(&definition, &subject);
        if result != one {
            failures.push(format!(
                "{label}: {subject} simplifies to {result}, not {one}"
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// ---------------------------------------------------------------------------------------------
// DF-3: the taint closure's seeds and edges.

/// Whether `term` mentions a symbol named in `names`.
fn mentions(term: &Term, names: &BTreeSet<String>) -> bool {
    let mut found = false;
    term.visit_symbols(&mut |symbol| found |= names.contains(symbol.name.as_ref()));
    found
}

/// The unhooked equation heads `term` mentions: the symbols T-sym withdraws when an equation
/// that mentions them is withdrawn.
fn unhooked_heads(term: &Term, into: &mut BTreeSet<String>) {
    term.visit_symbols(&mut |symbol| {
        if symbol.attributes.head_role() == HeadRole::EquationHead
            && symbol.attributes.hook.is_none()
        {
            into.insert(symbol.name.as_ref().to_owned());
        }
    });
}

fn rhs_terms(rhs: &RuleRhs) -> Vec<&Term> {
    match rhs {
        RuleRhs::Term(term) => vec![term],
        RuleRhs::Disjunction(alternatives) => alternatives.iter().map(|a| &a.term).collect(),
        RuleRhs::Top | RuleRhs::Bottom | RuleRhs::Predicates(_) => Vec::new(),
    }
}

/// The T1 fixture (`repro/definedness/t1-hooked-head.k`): the pair of `p`'s equations does not
/// join, so `hh`, an equation head of the sort of their variable, is withdrawn (T-obs), and
/// `k(hh(5)) = d` mentions `hh` on its left-hand side. `hooked` makes `hh` a hooked head.
fn t1_definition(hooked: bool) -> BackendDefinition {
    let hh = if hooked {
        r#"hooked-symbol hh{}(SortInt{}) : SortFoo{} [anywhere{}(), value-production{}(), hook{}("T1.hh")]"#
    } else {
        r"symbol hh{}(SortInt{}) : SortFoo{} [anywhere{}(), value-production{}()]"
    };
    definition(
        &format!(
            r"
            symbol e{{}}() : SortFoo{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            {hh}
            sort SortBar{{}} []
            symbol b{{}}() : SortBar{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol q{{}}(SortFoo{{}}) : SortBar{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol p{{}}(SortFoo{{}}) : SortBar{{}} [anywhere{{}}(), value-production{{}}()]
            symbol k{{}}(SortFoo{{}}) : SortBar{{}} [anywhere{{}}(), value-production{{}}()]
            "
        ),
        &[
            anywhere("hh", &["SortInt{}"], "SortFoo{}", &[&int(0)], "e{}()"),
            anywhere(
                "p",
                &["SortFoo{}"],
                "SortBar{}",
                &["VarX:SortFoo{}"],
                "q{}(VarX:SortFoo{})",
            ),
            anywhere(
                "p",
                &["SortFoo{}"],
                "SortBar{}",
                &["VarX:SortFoo{}"],
                &format!("q{{}}(hh{{}}({}))", int(6)),
            ),
            anywhere(
                "k",
                &["SortFoo{}"],
                "SortBar{}",
                &[&format!("hh{{}}({})", int(5))],
                "b{}()",
            ),
        ],
    )
}

/// T1 and T-sym, read on the result: an executable equation whose left-hand side mentions a
/// withdrawn symbol is withdrawn, and so is every unhooked equation head it mentions. The
/// closure is the least set closed under its rules, so its result is closed under each; the
/// unhooked variant is the control.
#[test]
#[ignore = "reproduces FOLLOWUPS: Closure rule T1 ignores tainted hooked heads"]
fn the_withdrawn_symbols_are_closed_under_t1() {
    let mut failures = Vec::new();
    for hooked in [false, true] {
        let definition = t1_definition(hooked);
        let tainted = definition
            .value_claims()
            .tainted_symbols()
            .iter()
            .map(|name| name.as_ref().to_owned())
            .collect::<BTreeSet<_>>();
        if !tainted.contains("hh") {
            failures.push(format!("hooked={hooked}: hh is not withdrawn: {tainted:?}"));
        }
        for rule in definition
            .function_theory()
            .values()
            .flat_map(|groups| groups.values().flatten())
        {
            if !mentions(&rule.lhs, &tainted) {
                continue;
            }
            let mut heads = BTreeSet::new();
            unhooked_heads(&rule.lhs, &mut heads);
            for term in rhs_terms(&rule.rhs) {
                unhooked_heads(term, &mut heads);
            }
            let missing = heads.difference(&tainted).collect::<Vec<_>>();
            if !missing.is_empty() {
                failures.push(format!(
                    "hooked={hooked}: {} mentions a withdrawn symbol on its left-hand side, yet {missing:?} keep their claims ({tainted:?})",
                    rule.attributes.unique_id
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// `_List_(L, .List) = ListItem(g(2))`, which internalizes to an equation whose left-hand side
/// is the bare variable `L` (indexed at `Variable`), with `requires`.
fn variable_indexed_equation() -> String {
    equation(
        "Lbl'Unds'List'Unds'",
        &["SortList{}", "SortList{}"],
        "SortList{}",
        &["VarL:SortList{}", "Lbl'Stop'List{}()"],
        &format!(
            "LblListItem{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}(g{{}}({})))",
            int(2)
        ),
        &format!(
            "\\equals{{SortList{{}}, R}}(VarL:SortList{{}}, LblListItem{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}(g{{}}({}))))",
            int(1)
        ),
        r#"UNIQUE'Unds'ID{}("variable-indexed")"#,
    )
}

const G_HEAD: &str = r"
    symbol a{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
    symbol g{}(SortInt{}) : SortFoo{} [anywhere{}(), value-production{}()]
";

/// An equation the check does not reason about (a precondition row: headed by a free
/// constructor or an injection, or indexed at a collection or a bare variable) has overlaps the
/// check never classifies, so it is withdrawn like a pair that does not join: every unhooked
/// equation head it mentions loses its claims. Here the row's equation equates `ListItem(g(1))`
/// with `ListItem(g(2))`, so `g` cannot keep its freeness claim.
#[test]
#[ignore = "reproduces FOLLOWUPS: Unclassified root overlaps of Variable-indexed equations"]
fn every_precondition_row_seeds_the_closure() {
    let definition = definition(
        G_HEAD,
        &[
            anywhere("g", &["SortInt{}"], "SortFoo{}", &[&int(0)], "a{}()"),
            variable_indexed_equation(),
        ],
    );
    let claims = definition.value_claims();
    let tainted = claims
        .tainted_symbols()
        .iter()
        .map(|name| name.as_ref().to_owned())
        .collect::<BTreeSet<_>>();
    let mut rows = 0;
    let mut failures = Vec::new();
    for violation in claims.violations() {
        let Some(rule) = &violation.rule else {
            continue;
        };
        if !matches!(
            violation.kind,
            ViolationKind::ConstructorHeaded(_)
                | ViolationKind::InjectionHeaded
                | ViolationKind::IndexedAt(_)
        ) {
            continue;
        }
        rows += 1;
        let mut heads = BTreeSet::new();
        unhooked_heads(&rule.lhs, &mut heads);
        for term in rhs_terms(&rule.rhs) {
            unhooked_heads(term, &mut heads);
        }
        for predicate in rule.requires.iter() {
            predicate.visit_terms(&mut |term| unhooked_heads(term, &mut heads));
        }
        let missing = heads.difference(&tainted).collect::<Vec<_>>();
        if !missing.is_empty() {
            failures.push(format!(
                "{} ({:?}) mentions {missing:?}, which keep their claims",
                rule.attributes.unique_id, violation.kind
            ));
        }
    }
    assert!(
        rows > 0,
        "the fixture has no precondition row: {:?}",
        claims.violations()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The evaluator offers a subject indexed at a symbol the equations indexed there and those
/// indexed at a bare variable, in one priority group (`rule::applicable_groups`). So the root
/// pair of `foo(X) = .List` and the `Variable`-indexed equation is an overlap of two steps from
/// `foo(X)`, and the check must classify it; its sides `ListItem(g(2))` and `.List` differ under
/// a `requires` it cannot refute, so it is reported.
#[test]
#[ignore = "reproduces FOLLOWUPS: Unclassified root overlaps of Variable-indexed equations"]
fn the_check_pairs_every_two_equations_offered_at_one_subject() {
    let definition = definition(
        &format!("{G_HEAD} symbol foo{{}}(SortInt{{}}) : SortList{{}} [function{{}}()]"),
        &[
            anywhere("g", &["SortInt{}"], "SortFoo{}", &[&int(0)], "a{}()"),
            variable_indexed_equation(),
            equation(
                "foo",
                &["SortInt{}"],
                "SortList{}",
                &["VarI:SortInt{}"],
                "Lbl'Stop'List{}()",
                TOP,
                r#"UNIQUE'Unds'ID{}("foo")"#,
            ),
        ],
    );
    let variable = definition
        .function_theory()
        .get(&TermIndex::Variable)
        .map(|groups| groups.values().flatten().count())
        .unwrap_or(0);
    assert_eq!(
        variable, 1,
        "the fixture's equation is not indexed at Variable"
    );
    let claims = definition.value_claims_in_scope(k_rust_backend::confluence::CheckScope::All);
    let ids = |first: &str, second: &str| {
        claims.unjoined().iter().any(|pair| {
            let pair = [
                pair.first.attributes.unique_id.as_str(),
                pair.second.attributes.unique_id.as_str(),
            ];
            pair == [first, second] || pair == [second, first]
        })
    };
    assert!(
        ids("variable-indexed", "foo"),
        "the root pair is not reported: {:#?}",
        claims
            .unjoined()
            .iter()
            .map(|pair| (
                pair.first.attributes.unique_id.clone(),
                pair.second.attributes.unique_id.clone(),
                pair.reason.clone()
            ))
            .collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------------------------
// DF-4: one admission check.

/// Internalization is the step every admission route shares, so whether a pattern is
/// well-sorted cannot depend on the route: a pattern the verifier refuses for a sort reason is
/// refused by internalization too. The ordinary symbol is the control.
#[test]
#[ignore = "reproduces FOLLOWUPS: Injection operands are not checked against the injection's source sort at internalization"]
fn internalization_refuses_what_the_verifier_refuses_for_its_sorts() {
    let definition = definition(
        r"symbol wrap{}(SortFoo{}) : SortS{} [constructor{}(), functional{}(), injective{}()]",
        &[],
    );
    let mut failures = Vec::new();
    for pattern in [
        r"inj{SortFoo{}, SortKItem{}}(c{}())".to_owned(),
        format!(r"inj{{SortFoo{{}}, SortKItem{{}}}}({})", int(1)),
        format!(r"inj{{SortInt{{}}, SortKItem{{}}}}({})", int(1)),
        r"inj{SortInt{}, SortKItem{}}(c{}())".to_owned(),
        r"wrap{}(c{}())".to_owned(),
        format!(r"wrap{{}}({})", int(1)),
    ] {
        let syntax = parse_pattern(&pattern).expect("the pattern parses");
        let verified = definition.verify_standalone_pattern(&syntax, &[]).is_ok();
        let internalized = definition
            .admit_unverified(&syntax, &[])
            .internalize_term()
            .is_ok();
        if verified != internalized {
            failures.push(format!(
                "{pattern}: verified {verified}, internalized unverified {internalized}"
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// ---------------------------------------------------------------------------------------------
// DF-5: the instances of an equation have one enumeration.

/// `fm((K |-> V) M) = \top requires K = n`, a simplification lemma whose map pattern matches
/// `{1 |-> 0, 2 |-> 0}` with `K = 1` and with `K = 2`: each matching is an instance of the
/// lemma, and the lemma applies when one instance does. So `e /\ fm({1 |-> 0, 2 |-> 0})`
/// simplifies alike for `n = 1` and `n = 2`, whichever key the matcher enumerates first.
#[test]
#[ignore = "reproduces FOLLOWUPS: matches_top_equation decides a top equation's requires on the first collection matching only"]
fn a_top_lemma_applies_whichever_instance_holds() {
    let entry = |key: i64| {
        format!(
            "Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}), inj{{SortInt{{}}, SortKItem{{}}}}({}))",
            int(key),
            int(0)
        )
    };
    let subject = format!(
        r"\and{{SortFoo{{}}}}(e{{}}(), fm{{}}(Lbl'Unds'Map'Unds'{{}}({}, {})))",
        entry(1),
        entry(2)
    );
    let results = [1, 2]
        .map(|key| {
            let lemma = format!(
                r#"axiom{{R}} \implies{{R}}(\equals{{SortKItem{{}}, R}}(VarK:SortKItem{{}}, inj{{SortInt{{}}, SortKItem{{}}}}({})), \equals{{SortFoo{{}}, R}}(fm{{}}(Lbl'Unds'Map'Unds'{{}}(Lbl'UndsPipe'-'-GT-Unds'{{}}(VarK:SortKItem{{}}, VarV:SortKItem{{}}), VarM:SortMap{{}})), \and{{SortFoo{{}}}}(\top{{SortFoo{{}}}}(), \top{{SortFoo{{}}}}()))) [UNIQUE'Unds'ID{{}}("top-{key}"), simplification{{}}()]"#,
                int(key)
            );
            let definition = definition(
                r"
                symbol e{}() : SortFoo{} [constructor{}(), functional{}(), injective{}()]
                symbol fm{}(SortMap{}) : SortFoo{} [function{}(), functional{}(), total{}()]
                ",
                &[lemma],
            );
            simplified(&definition, &subject)
        });
    assert_eq!(
        results[0], results[1],
        "the lemma's result depends on the key"
    );
    assert!(!results[0].starts_with("error"), "{results:?}");
}

#[test]
fn the_fixtures_load() {
    // The fixtures above must stay meaningful when their tests are ignored: each loads, and
    // the shapes they rely on internalize as the tests assume.
    for (label, definition, subject, _) in consumed_subterm_cases() {
        let term = internal_term(&definition, &subject);
        assert!(
            matches!(term.kind(), TermKind::Application { .. }),
            "{label}: {subject}"
        );
    }
    for hooked in [false, true] {
        let _ = t1_definition(hooked);
    }
}
