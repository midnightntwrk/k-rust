//! A closed collection pattern of an equation against a subject collection with a frame. A
//! frame of sort `List`, `Set` or `Map` ranges over every collection of its sort, the empty one
//! and one holding exactly the pattern's leftover items among them. Where the items the subject
//! fixes agree with the pattern's, some instance of the subject is an instance of the pattern,
//! so the equation is not refuted, and an `owise` equation, whose premise is that no other
//! equation applies, must not apply either: the application stays. Where the subject fixes an
//! item the closed pattern cannot hold, the equation is refuted on every instance and the
//! `owise` equation applies.

use k_rust_backend::{
    definition::BackendDefinition,
    implication::{Coverage, check_implication},
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::Term,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::support::{internal_term, unstopped::simplify};

/// An equation of the unary function `symbol` over `sort` whose argument is `pattern`, with the
/// integer result `value`.
fn equation(symbol: &str, sort: &str, pattern: &str, value: &str, label: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, {pattern}), \top{{R}}())),
            \equals{{SortInt{{}}, R}}({symbol}{{}}(X0:{sort}),
                \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("{value}"), \top{{SortInt{{}}}}()))
        ) [label{{}}("{label}")]"#
    )
}

/// The `owise` equation of `symbol`: 0.
fn otherwise(symbol: &str, sort: &str, label: &str) -> String {
    format!(
        r#"axiom{{R}} \implies{{R}}(
            \and{{R}}(\top{{R}}(), \and{{R}}(\in{{{sort}, R}}(X0:{sort}, VarO:{sort}), \top{{R}}())),
            \equals{{SortInt{{}}, R}}({symbol}{{}}(X0:{sort}),
                \and{{SortInt{{}}}}(\dv{{SortInt{{}}}}("0"), \top{{SortInt{{}}}}()))
        ) [label{{}}("{label}"), owise{{}}()]"#
    )
}

fn int(value: &str) -> String {
    format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
}

fn list_item(item: &str) -> String {
    format!("LblListItem{{}}({item})")
}

fn list_concat(left: &str, right: &str) -> String {
    format!("Lbl'Unds'List'Unds'{{}}({left}, {right})")
}

fn set_item(item: &str) -> String {
    format!("LblSetItem{{}}({item})")
}

fn set_concat(left: &str, right: &str) -> String {
    format!("Lbl'Unds'Set'Unds'{{}}({left}, {right})")
}

fn map_entry(key: &str, value: &str) -> String {
    format!("Lbl'UndsPipe'-'-GT-Unds'{{}}({key}, {value})")
}

fn map_concat(left: &str, right: &str) -> String {
    format!("Lbl'Unds'Map'Unds'{{}}({left}, {right})")
}

/// `isSingleton(ListItem(_)) = 1`, `single(SetItem(1)) = 1`, `has1(1 |-> _) = 1` and
/// `two(1 |-> _ K |-> _) = 1`, each 0 otherwise (`owise`).
fn definition() -> BackendDefinition {
    let equations = [
        equation(
            "isSingleton",
            "SortList{}",
            &list_item("VarX:SortKItem{}"),
            "1",
            "singleton-one",
        ),
        otherwise("isSingleton", "SortList{}", "singleton-other"),
        equation(
            "single",
            "SortSet{}",
            &set_item(&int("1")),
            "1",
            "single-one",
        ),
        otherwise("single", "SortSet{}", "single-other"),
        equation(
            "has1",
            "SortMap{}",
            &map_entry(&int("1"), "VarV:SortKItem{}"),
            "1",
            "has1-one",
        ),
        otherwise("has1", "SortMap{}", "has1-other"),
        equation(
            "two",
            "SortMap{}",
            &map_concat(
                &map_entry(&int("1"), "VarV:SortKItem{}"),
                &map_entry("VarK:SortKItem{}", "VarW:SortKItem{}"),
            ),
            "1",
            "two-one",
        ),
        otherwise("two", "SortMap{}", "two-other"),
    ]
    .join("\n");
    let source = format!(
        r#"[] module MAIN
        hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
        sort SortKItem{{}} []
        hooked-sort SortList{{}}
            [hook{{}}("LIST.List"), unit{{}}(Lbl'Stop'List{{}}()), element{{}}(LblListItem{{}}()),
             concat{{}}(Lbl'Unds'List'Unds'{{}}())]
        hooked-symbol Lbl'Stop'List{{}}() : SortList{{}}
            [function{{}}(), total{{}}(), hook{{}}("LIST.unit")]
        hooked-symbol LblListItem{{}}(SortKItem{{}}) : SortList{{}}
            [function{{}}(), total{{}}(), hook{{}}("LIST.element")]
        hooked-symbol Lbl'Unds'List'Unds'{{}}(SortList{{}}, SortList{{}}) : SortList{{}}
            [function{{}}(), total{{}}(), hook{{}}("LIST.concat"), assoc{{}}()]
        hooked-sort SortSet{{}}
            [hook{{}}("SET.Set"), unit{{}}(Lbl'Stop'Set{{}}()), element{{}}(LblSetItem{{}}()),
             concat{{}}(Lbl'Unds'Set'Unds'{{}}())]
        hooked-symbol Lbl'Stop'Set{{}}() : SortSet{{}}
            [function{{}}(), total{{}}(), hook{{}}("SET.unit")]
        hooked-symbol LblSetItem{{}}(SortKItem{{}}) : SortSet{{}}
            [function{{}}(), total{{}}(), hook{{}}("SET.element")]
        hooked-symbol Lbl'Unds'Set'Unds'{{}}(SortSet{{}}, SortSet{{}}) : SortSet{{}}
            [function{{}}(), hook{{}}("SET.concat"), assoc{{}}(), comm{{}}(), idem{{}}()]
        hooked-sort SortMap{{}}
            [hook{{}}("MAP.Map"), unit{{}}(Lbl'Stop'Map{{}}()),
             element{{}}(Lbl'UndsPipe'-'-GT-Unds'{{}}()), concat{{}}(Lbl'Unds'Map'Unds'{{}}())]
        hooked-symbol Lbl'Stop'Map{{}}() : SortMap{{}}
            [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
        hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{{}}(SortKItem{{}}, SortKItem{{}}) : SortMap{{}}
            [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
        hooked-symbol Lbl'Unds'Map'Unds'{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
            [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
        symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
        axiom{{R}} \exists{{R}}(Val:SortKItem{{}},
            \equals{{SortKItem{{}}, R}}(Val:SortKItem{{}}, inj{{SortInt{{}}, SortKItem{{}}}}(From:SortInt{{}})))
            [subsort{{SortInt{{}}, SortKItem{{}}}}()]
        symbol isSingleton{{}}(SortList{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
        symbol single{{}}(SortSet{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
        symbol has1{{}}(SortMap{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
        symbol two{{}}(SortMap{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
        {equations}
    endmodule []"#
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// `source` simplified: the result and the equations applied.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<String>) {
    let result = simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (result.term, result.applied_rules.to_vec())
}

/// Each application stays as it is, no equation applied.
fn assert_kept(definition: &BackendDefinition, sources: &[String]) {
    for source in sources {
        let (term, applied) = simplified(definition, source);
        assert_eq!(term, internal_term(definition, source), "{source}");
        assert!(applied.is_empty(), "{source}: {applied:?}");
    }
}

/// Each application is evaluated by `label` to `value`.
fn assert_evaluated(definition: &BackendDefinition, cases: &[(String, &str, &str)]) {
    for (source, value, label) in cases {
        let (term, applied) = simplified(definition, source);
        assert_eq!(
            term,
            internal_term(definition, &format!(r#"\dv{{SortInt{{}}}}("{value}")"#)),
            "{source}"
        );
        assert_eq!(applied, [*label], "{source}");
    }
}

/// `isSingleton(ListItem(A) L)` is 1 at `L = .List` and 0 elsewhere: neither equation applies.
/// `isSingleton(ListItem(A) ListItem(B) L)` holds two items on every instance, which the
/// one-item pattern cannot, so it is 0.
#[test]
fn a_closed_list_pattern_against_a_list_frame_blocks_owise() {
    let definition = definition();
    let a = "VarA:SortKItem{}";
    let frame = "VarL:SortList{}";
    assert_kept(
        &definition,
        &[format!(
            "isSingleton{{}}({})",
            list_concat(&list_item(a), frame)
        )],
    );
    assert_evaluated(
        &definition,
        &[
            (
                format!("isSingleton{{}}({})", list_item(a)),
                "1",
                "singleton-one",
            ),
            (
                format!(
                    "isSingleton{{}}({})",
                    list_concat(
                        &list_item(a),
                        &list_concat(&list_item("VarB:SortKItem{}"), frame)
                    )
                ),
                "0",
                "singleton-other",
            ),
        ],
    );
}

/// `single(SetItem(1) S)` is 1 at `S = .Set`: the `owise` equation does not apply. With the
/// element 2 beside the frame, no instance is `SetItem(1)`, so it is 0.
#[test]
fn a_closed_set_pattern_against_a_set_frame_blocks_owise() {
    let definition = definition();
    let frame = "VarS:SortSet{}";
    assert_kept(
        &definition,
        &[format!(
            "single{{}}({})",
            set_concat(&set_item(&int("1")), frame)
        )],
    );
    assert_evaluated(
        &definition,
        &[(
            format!(
                "single{{}}({})",
                set_concat(
                    &set_item(&int("1")),
                    &set_concat(&set_item(&int("2")), frame)
                )
            ),
            "0",
            "single-other",
        )],
    );
}

/// `has1(1 |-> 5 M)` is 1 at `M = .Map`, and `two(1 |-> 5 M)` is 1 where `M` binds one key other
/// than 1: neither `owise` equation applies. With the key 2 beside the frame `has1` is 0 on every
/// instance, and without a frame `two(1 |-> 5)` binds one key, not two, so it is 0.
#[test]
fn a_closed_map_pattern_against_a_map_frame_blocks_owise() {
    let definition = definition();
    let frame = "VarM:SortMap{}";
    let one = map_entry(&int("1"), &int("5"));
    let framed = map_concat(&one, frame);
    assert_kept(
        &definition,
        &[format!("has1{{}}({framed})"), format!("two{{}}({framed})")],
    );
    assert_evaluated(
        &definition,
        &[
            (
                format!(
                    "has1{{}}({})",
                    map_concat(&one, &map_concat(&map_entry(&int("2"), &int("6")), frame))
                ),
                "0",
                "has1-other",
            ),
            (format!("two{{}}({one})"), "0", "two-other"),
        ],
    );
}

/// The state `1 |-> 5 M` lies in the destination `1 |-> X` exactly where `M` is the empty map:
/// some instances lie in it, so the destination's term does not mismatch the state's, whatever
/// else the check establishes without a solver.
#[test]
fn a_closed_map_destination_does_not_mismatch_a_framed_state() {
    let definition = definition();
    let pattern = |source: &str| {
        let syntax = parse_pattern(source).expect("the pattern parses");
        definition
            .admit_unverified(&syntax, &[])
            .internalize_pattern()
            .expect("the pattern internalizes")
    };
    let state = pattern(&map_concat(
        &map_entry(&int("1"), &int("5")),
        "VarM:SortMap{}",
    ));
    let destination = pattern(&map_entry(&int("1"), "VarX:SortKItem{}"));
    let result = check_implication(&definition, &state, &destination, &NoSolver)
        .expect("the check does not stop");
    assert!(!matches!(result, Ok(Coverage::TermMismatch)), "{result:?}");
}
