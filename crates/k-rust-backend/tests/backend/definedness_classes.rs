//! Class tests of the taint closure's inputs (`draft/open-issues-2026-10/TICKETS.md` K5).
//!
//! Each test states one invariant that follows from what the closure means, and checks krust
//! against itself on small definitions; none compares with another implementation.
//!
//! - The taint closure is a least fixpoint of its rules: an equation whose left-hand side
//!   mentions a withdrawn symbol is withdrawn (T1), a withdrawn equation withdraws every equation
//!   head it mentions, hooked or not (T-sym), and an equation the check does not reason about is
//!   withdrawn like a pair that does not join.
//! - A claim the load keeps is true in every model: two equations that equate two terms leave
//!   no freeness claim that tells them apart.

use std::collections::BTreeSet;

use k_rust_backend::{
    definition::BackendDefinition,
    externalize,
    rewrite::Pattern,
    rule::{RuleRhs, TermIndex},
    simplify::SimplificationOptions,
    term::{HeadRole, Term},
};
use k_rust_kore::kore::{parser::parse_definition, printer::Printer};

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

/// Whether `term` mentions a symbol named in `names`.
fn mentions(term: &Term, names: &BTreeSet<String>) -> bool {
    let mut found = false;
    term.visit_symbols(&mut |symbol| found |= names.contains(symbol.name.as_ref()));
    found
}

/// The equation heads `term` mentions, hooked or not: the symbols T-sym withdraws when an
/// equation that mentions them is withdrawn. An equation head's applications denote what its
/// equations make of them, and a hooked head may be partial, so a hook does not exempt it.
fn equation_heads(term: &Term, into: &mut BTreeSet<String>) {
    term.visit_symbols(&mut |symbol| {
        if symbol.attributes.head_role() == HeadRole::EquationHead {
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
/// withdrawn symbol is withdrawn, and so is every equation head it mentions, hooked or not. The
/// closure is the least set closed under its rules, so its result is closed under each; the
/// unhooked variant is the control.
#[test]
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
            equation_heads(&rule.lhs, &mut heads);
            for term in rhs_terms(&rule.rhs) {
                equation_heads(term, &mut heads);
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
/// check never classifies, so it is withdrawn like a pair that does not join: every equation
/// head it mentions loses its claims. Here the row's equation equates `ListItem(g(1))`
/// with `ListItem(g(2))`, so `g` cannot keep its freeness claim.
#[test]
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
        if !violation.kind.withdraws() {
            continue;
        }
        rows += 1;
        let mut heads = BTreeSet::new();
        equation_heads(&rule.lhs, &mut heads);
        for term in rhs_terms(&rule.rhs) {
            equation_heads(term, &mut heads);
        }
        for predicate in rule.requires.iter() {
            predicate.visit_terms(&mut |term| equation_heads(term, &mut heads));
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
///
/// Step-back review (`definedness-stepback.md`, DF-3): this is not an acceptance test as written.
/// The overlap's `requires` is `foo(I) = ListItem(g(1))`, and `foo(I)` evaluates to `.List`, so a
/// check that classifies the pair refutes it and reports nothing; more generally, under innermost
/// evaluation a root overlap of a `Variable`-indexed equation with another equation joins (the
/// other reduct is the value the `requires` was evaluated on). Kept only as a record; the
/// semantic test is `no_kept_claim_is_contradicted_by_two_equations`.
///
/// K5 (`TICKETS.md`) seeds the closure with every precondition row instead of pairing these
/// equations: under T-obs the `Variable`-indexed equation's variable ranges over its whole sort,
/// so its seed withdraws every equation head that a root overlap with it could constrain, which
/// is what classifying the pair as not joined would withdraw. This test therefore keeps failing.
#[test]
#[ignore = "a record, not an acceptance test: a check that pairs these equations refutes the overlap and reports nothing (draft/open-issues-2026-10/tickets/definedness-stepback.md, DF-3)"]
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

/// The definition of [`no_kept_claim_is_contradicted_by_two_equations`]: `bar(t) = a` where `t`
/// is `pattern`, else `bar(_) = b` at a lower priority, beside `declarations` and `axioms`.
fn bar_definition(declarations: &str, pattern: &str, axioms: Vec<String>) -> BackendDefinition {
    let mut axioms = axioms;
    axioms.push(equation(
        "bar",
        &["SortFoo{}"],
        "SortFoo{}",
        &[pattern],
        "a{}()",
        TOP,
        "",
    ));
    axioms.push(equation(
        "bar",
        &["SortFoo{}"],
        "SortFoo{}",
        &["VarX:SortFoo{}"],
        "b{}()",
        TOP,
        r#"priority{}("200")"#,
    ));
    definition(
        &format!(
            r"{declarations}
            symbol b{{}}() : SortFoo{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol bar{{}}(SortFoo{{}}) : SortFoo{{}} [function{{}}()]"
        ),
        &axioms,
    )
}

/// The semantic form of the closure invariants: a claim the load keeps is true in every model.
/// Each case has two equations that equate `t1` and `t2` in every model where they are defined
/// (`t1` and `t2` are total, or `bar(t1)` is undefined anyway), so `bar(t1)` is `a` or undefined,
/// and never `b`; `b` can only come from a freeness claim that refutes `t2` against `t1`.
///
/// - The `Variable`-indexed equation `L = ListItem(g(2)) requires L = ListItem(g(1))` equates
///   `g(1)` and `g(2)`; only its precondition row's seed withdraws `g`.
/// - `r(0) = hh(5)` beside `r(0) = hh(6)` equates the total `hh(5)` and `hh(6)`; the pair does
///   not join, and T-obs does not reach `hh` (the pair has no variable), so only T-sym withdraws
///   it, hooked or not. The unhooked `hh` is the control.
#[test]
fn no_kept_claim_is_contradicted_by_two_equations() {
    let mut failures = Vec::new();
    let variable = bar_definition(
        G_HEAD,
        &format!("g{{}}({})", int(2)),
        vec![
            anywhere("g", &["SortInt{}"], "SortFoo{}", &[&int(0)], "a{}()"),
            variable_indexed_equation(),
        ],
    );
    let subject = format!("bar{{}}(g{{}}({}))", int(1));
    failures.push(("variable-indexed equation", simplified(&variable, &subject)));
    for hooked in [false, true] {
        let hh = if hooked {
            r#"hooked-symbol hh{}(SortInt{}) : SortFoo{} [anywhere{}(), functional{}(), hook{}("TSYM.hh")]"#
        } else {
            r"symbol hh{}(SortInt{}) : SortFoo{} [anywhere{}(), functional{}()]"
        };
        let definition = bar_definition(
            &format!(
                r"symbol a{{}}() : SortFoo{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                {hh}
                symbol r{{}}(SortInt{{}}) : SortFoo{{}} [anywhere{{}}(), functional{{}}()]"
            ),
            &format!("hh{{}}({})", int(5)),
            vec![
                anywhere("hh", &["SortInt{}"], "SortFoo{}", &[&int(0)], "a{}()"),
                anywhere(
                    "r",
                    &["SortInt{}"],
                    "SortFoo{}",
                    &[&int(0)],
                    &format!("hh{{}}({})", int(5)),
                ),
                anywhere(
                    "r",
                    &["SortInt{}"],
                    "SortFoo{}",
                    &[&int(0)],
                    &format!("hh{{}}({})", int(6)),
                ),
            ],
        );
        let subject = format!("bar{{}}(hh{{}}({}))", int(6));
        failures.push((
            if hooked {
                "pair over a hooked head"
            } else {
                "pair over an unhooked head"
            },
            simplified(&definition, &subject),
        ));
    }
    failures.retain(|(_, result)| result == "b{}()");
    assert!(
        failures.is_empty(),
        "a kept claim gives a value no model has: {failures:#?}"
    );
}
