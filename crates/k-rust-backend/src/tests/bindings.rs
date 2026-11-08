//! Bindings of fired instances (`crate::coverage::bindings`): a run that asks for them records,
//! per axiom, the named symbols that were the head of an operand of a fired instance (a value
//! bound to a left-hand-side variable the axiom reads elsewhere), the values selected template
//! binders were bound to, capped, and the alternatives of an axiom with several that its fired
//! instances took.
//!
//! The axioms carry labels and, but for `scaleAny`, no `UNIQUE_ID`, so each other one's id is
//! its label. Every run here
//! ends by itself well inside its depth bound and sets no step timeout, so none depends on a
//! clock.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use num_bigint::BigInt;

use crate::{
    coverage::{
        BinderKey, BinderValues, BindingCollection, FiredAlternative, RunBindings, RunCoverage,
    },
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, ExecutionResult, Pattern, execute},
};

/// The instruction `inner` as an item of a `K` sequence.
fn item(inner: &str) -> String {
    format!("inj{{SortInstr{{}}, SortKItem{{}}}}({inner})")
}

/// A `K` sequence of `items`.
fn sequence(items: &[String]) -> String {
    items
        .iter()
        .rev()
        .fold("dotk{}()".to_owned(), |rest, first| {
            format!("kseq{{}}({first}, {rest})")
        })
}

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// A rewrite rule `st(kseq(head, K)) => rhs requires b` of sort `SortS` at `priority`; no
/// condition when `b` is empty.
fn rule(label: &str, head: &str, rhs: &str, b: &str, priority: u32) -> String {
    let requires = if b.is_empty() {
        r"\top{SortS{}}()".to_owned()
    } else {
        format!(r#"\equals{{SortBool{{}}, SortS{{}}}}({b}, \dv{{SortBool{{}}}}("true"))"#)
    };
    format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(st{{}}(kseq{{}}({head}, K:SortK{{}})), {requires}),
                \and{{SortS{{}}}}({rhs}, \top{{SortS{{}}}}())
            ) [label{{}}("{label}"), priority{{}}("{priority}")]"#,
    )
}

/// A rewrite rule `sf(kseq(head, K), F) => rhs` of sort `SortS`, a state with one cell `F`.
fn cell_rule(label: &str, head: &str, rhs: &str, priority: u32) -> String {
    format!(
        r#"
            axiom{{}} \rewrites{{SortS{{}}}}(
                \and{{SortS{{}}}}(sf{{}}(kseq{{}}({head}, K:SortK{{}}), F:SortInstr{{}}), \top{{SortS{{}}}}()),
                \and{{SortS{{}}}}({rhs}, \top{{SortS{{}}}}())
            ) [label{{}}("{label}"), priority{{}}("{priority}")]"#,
    )
}

/// The authored symbols, which a front end names.
const AUTHORED: [&str; 12] = [
    "Lblinc", "Lblhalt", "Lblghost", "Lblop", "Lblev", "Lblnop", "Lblgate", "Lblmark", "Lblcopy",
    "Lblpair", "Lblleft", "Lblright",
];

fn definition() -> BackendDefinition {
    let axioms = [
        // Matched on every `inc`, fired only above 100.
        rule(
            "guarded",
            &item("Lblinc{}(N:SortInt{})"),
            "st{}(K:SortK{})",
            &format!("gtInt{{}}(N:SortInt{{}}, {})", int(100)),
            40,
        ),
        // Matched on every `gate`, fired only above 100; its operand `I` has a head, and the
        // step runs it next.
        rule(
            "gate",
            &item("Lblgate{}(N:SortInt{}, I:SortInstr{})"),
            &format!(
                "st{{}}(kseq{{}}({}, K:SortK{{}}))",
                item("I:SortInstr{}")
            ),
            &format!("gtInt{{}}(N:SortInt{{}}, {})", int(100)),
            40,
        ),
        // Passes its operand to the function `scale`, whose result `op` then takes.
        rule(
            "sc",
            &item("Lblsc{}(B:SortInt{})"),
            &format!(
                "st{{}}(kseq{{}}({}, K:SortK{{}}))",
                item("Lblop{}(scale{}(B:SortInt{}))")
            ),
            "",
            40,
        ),
        // The rest of the program, `K`, is a continuation.
        rule("stop", &item("Lblhalt{}()"), "done{}()", "", 40),
        // A template-like binder `B`.
        rule("op", &item("Lblop{}(B:SortInt{})"), "st{}(K:SortK{})", "", 40),
        // An operand bound without an injection, passed to a function.
        rule(
            "ev",
            &item("Lblev{}(I:SortInstr{})"),
            "out{}(weight{}(I:SortInstr{}))",
            "",
            40,
        ),
        // An item bound at sort `KItem` and dropped: no other part of the rule reads `X`.
        rule("drop", "X:SortKItem{}", "st{}(K:SortK{})", "", 50),
        // Passes its operand to the function `wrap`, whose equation `wrapAny` gives it back.
        rule(
            "wr",
            &item("Lblwr{}(I:SortInstr{})"),
            &format!(
                "st{{}}(kseq{{}}({}, K:SortK{{}}))",
                item("wrap{}(I:SortInstr{})")
            ),
            "",
            40,
        ),
        // `mark` overwrites the cell, whose old value `F` it never reads (`<f> _ => ghost </f>`);
        // `copy` runs the cell's value next and keeps it.
        cell_rule(
            "mark",
            &item("Lblmark{}()"),
            "sf{}(K:SortK{}, Lblghost{}())",
            40,
        ),
        cell_rule(
            "copy",
            &item("Lblcopy{}()"),
            &format!(
                "sf{{}}(kseq{{}}({}, K:SortK{{}}), F:SortInstr{{}})",
                item("F:SortInstr{}")
            ),
            40,
        ),
        // `A` occurs twice in the left-hand side: the match compares the two values.
        cell_rule(
            "twice",
            &item("Lblpair{}(A:SortInstr{}, A:SortInstr{})"),
            "sf{}(K:SortK{}, F:SortInstr{})",
            40,
        ),
        // Drops the item and keeps the cell.
        cell_rule(
            "sfdrop",
            "X:SortKItem{}",
            "sf{}(K:SortK{}, F:SortInstr{})",
            50,
        ),
        // One rule per disjunct of its left-hand side.
        rule(
            "either",
            &format!(
                r"\or{{SortKItem{{}}}}({}, {})",
                item("Lblleft{}()"),
                item("Lblright{}()")
            ),
            "st{}(K:SortK{})",
            "",
            40,
        ),
        // One successor per alternative of its right-hand side.
        rule(
            "split",
            &item("Lblsplit{}()"),
            &format!(
                r"\or{{SortS{{}}}}(st{{}}(kseq{{}}({}, K:SortK{{}})), st{{}}(kseq{{}}({}, K:SortK{{}})))",
                item("Lblleft{}()"),
                item("Lblhalt{}()")
            ),
            "",
            40,
        ),
        r#"
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortInstr{}, R}(X0:SortInstr{}, I:SortInstr{}), \top{R}())),
                \equals{SortInstr{}, R}(wrap{}(X0:SortInstr{}), \and{SortInstr{}}(I:SortInstr{}, \top{SortInstr{}}()))
            ) [label{}("wrapAny")]"#
            .to_owned(),
        r#"
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortInstr{}, R}(X0:SortInstr{}, I:SortInstr{}), \top{R}())),
                \equals{SortInt{}, R}(weight{}(X0:SortInstr{}), \and{SortInt{}}(\dv{SortInt{}}("7"), \top{SortInt{}}()))
            ) [label{}("weightAny")]"#
            .to_owned(),
        // A function equation whose binder `V` is named by its `\in`, as a template's is; it
        // has a `UNIQUE_ID` besides its label.
        r#"
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, V:SortInt{}), \top{R}())),
                \equals{SortInt{}, R}(scale{}(X0:SortInt{}), \and{SortInt{}}(V:SortInt{}, \top{SortInt{}}()))
            ) [label{}("scaleAny"), UNIQUE'Unds'ID{}("scale-id")]"#
            .to_owned(),
    ];
    let source = format!(
        r#"[]
        module MAIN
            hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
            hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
            sort SortKItem{{}} []
            sort SortK{{}} []
            sort SortInstr{{}} []
            sort SortS{{}} []
            hooked-symbol gtInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                [function{{}}(), total{{}}(), hook{{}}("INT.gt"), smt-hook{{}}(">")]
            symbol kseq{{}}(SortKItem{{}}, SortK{{}}) : SortK{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol dotk{{}}() : SortK{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
            axiom{{R}} \exists{{R}}(Val:SortKItem{{}}, \equals{{SortKItem{{}}, R}}(Val:SortKItem{{}}, inj{{SortInstr{{}}, SortKItem{{}}}}(From:SortInstr{{}}))) [subsort{{SortInstr{{}}, SortKItem{{}}}}()]
            symbol Lblinc{{}}(SortInt{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblhalt{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblghost{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblop{{}}(SortInt{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblev{{}}(SortInstr{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblnop{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblgate{{}}(SortInt{{}}, SortInstr{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblsc{{}}(SortInt{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblwr{{}}(SortInstr{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol Lblmark{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblcopy{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblleft{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblright{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblsplit{{}}() : SortInstr{{}} [constructor{{}}(), functional{{}}()]
            symbol Lblpair{{}}(SortInstr{{}}, SortInstr{{}}) : SortInstr{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol sf{{}}(SortK{{}}, SortInstr{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol wrap{{}}(SortInstr{{}}) : SortInstr{{}} [function{{}}(), total{{}}()]
            symbol st{{}}(SortK{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol out{{}}(SortInt{{}}) : SortS{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
            symbol done{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
            symbol weight{{}}(SortInstr{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            symbol scale{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
            {axioms}
        endmodule []"#,
        axioms = axioms.join("\n"),
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The state `st(program)`.
fn state(definition: &BackendDefinition, program: &[String]) -> Pattern {
    let source = format!("st{{}}({})", sequence(program));
    Pattern {
        term: definition
            .internalize_term(&parse_pattern(&source).expect("term should parse"), &[])
            .expect("term should internalize"),
        constraints: Vec::new(),
    }
}

/// A run with coverage, collecting `bindings` when given.
fn options(bindings: Option<BindingCollection>) -> ExecutionOptions {
    ExecutionOptions {
        collect_coverage: true,
        collect_bindings: bindings,
        max_depth: 50,
        ..ExecutionOptions::default()
    }
}

/// Run `initial` collecting `bindings` under `options`, check that collecting changed nothing
/// else in the result, and return the bindings with the run's other coverage.
fn bindings_of(
    definition: &BackendDefinition,
    initial: Pattern,
    bindings: BindingCollection,
    configure: impl Fn(&mut ExecutionOptions),
) -> (RunBindings, RunCoverage) {
    let mut with_options = options(Some(bindings));
    configure(&mut with_options);
    let mut without_options = options(None);
    configure(&mut without_options);
    let mut with = execute(definition, initial.clone(), with_options);
    let without = execute(definition, initial, without_options);
    let collected = with
        .coverage
        .as_mut()
        .and_then(|coverage| coverage.bindings.take())
        .expect("the run collected bindings");
    assert_eq!(
        without.coverage.as_ref().map(|coverage| &coverage.bindings),
        Some(&None)
    );
    assert_results_equal(&with, &without);
    let coverage = with.coverage.expect("the run collected coverage");
    (collected, coverage)
}

fn assert_results_equal(with: &ExecutionResult, without: &ExecutionResult) {
    assert_eq!(with, without, "collecting bindings changed the result");
}

fn authored() -> BindingCollection {
    BindingCollection::new(AUTHORED)
}

/// The recorded heads of `axiom`'s operands; empty when it recorded none.
fn heads(bindings: &RunBindings, axiom: &str) -> BTreeSet<String> {
    bindings
        .operands
        .iter()
        .find(|operands| operands.axiom == axiom)
        .map(|operands| operands.symbols.clone())
        .unwrap_or_default()
}

fn binder<'a>(bindings: &'a RunBindings, axiom: &str, variable: &str) -> Option<&'a BinderValues> {
    bindings
        .binders
        .iter()
        .find(|values| values.binder.axiom == axiom && values.binder.variable == variable)
}

fn set(symbols: &[&str]) -> BTreeSet<String> {
    symbols.iter().map(|symbol| (*symbol).to_owned()).collect()
}

/// `gate` is entered at `gate(1, nop)` and its guard refuted: it is matched, records neither
/// the head of its operand `I` nor a value of its binder `N`, and `drop`, which takes the step
/// and discards the instruction, records nothing either. Where its guard holds, at
/// `gate(200, nop)`, the same rule records both, so what the refuted entry did not record is
/// what an instance that fired records.
#[test]
fn a_matched_rule_whose_guard_was_refuted_records_no_binding() {
    let definition = definition();
    let gate = |n| item(&format!("Lblgate{{}}({}, Lblnop{{}}())", int(n)));
    let collection = || authored().with_binder("gate", "N", 8);
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &[gate(1), item("Lblhalt{}()")]),
        collection(),
        |_| {},
    );
    assert!(coverage.matched.contains("gate"), "{coverage:?}");
    assert!(!coverage.applied.contains("gate"), "{coverage:?}");
    assert!(heads(&bindings, "gate").is_empty(), "{bindings:?}");
    assert_eq!(binder(&bindings, "gate", "N"), None, "{bindings:?}");
    assert!(coverage.applied.contains("drop"), "{coverage:?}");
    assert!(heads(&bindings, "drop").is_empty(), "{bindings:?}");
    let (fired, coverage) = bindings_of(
        &definition,
        state(&definition, &[gate(200)]),
        collection(),
        |_| {},
    );
    assert!(coverage.applied.contains("gate"), "{coverage:?}");
    assert_eq!(heads(&fired, "gate"), set(&["Lblnop"]), "{fired:?}");
    assert_eq!(
        binder(&fired, "gate", "N").map(|values| values.values.clone()),
        Some(values(&[200])),
        "{fired:?}"
    );
}

/// A committed step records the head of each operand it reads: `ev`'s `I:Instr` bound to
/// `nop()`, which its result passes to `weight`, records `nop`; `wr`'s `I`, passed to `wrap`,
/// records `ghost`, and so does the equation `wrapAny`, whose instance in `wr`'s successor gave
/// it back. A value bound to a variable no other part of the axiom reads was carried past or
/// dropped, not taken: `drop` discards the item it binds (`ghost`, and later the item `wrap`
/// gave back), and `weightAny` gives `7` whatever its argument, so neither records a head. With
/// no `collect_committed`, they are recorded all the same.
#[test]
fn a_committed_step_records_the_heads_of_the_operands_it_reads() {
    let definition = definition();
    let program = [
        item("Lblghost{}()"),
        item(&format!("Lblinc{{}}({})", int(200))),
        item("Lblev{}(Lblnop{}())"),
    ];
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &program),
        authored(),
        |_| {},
    );
    assert_eq!(coverage.committed, None, "{coverage:?}");
    assert!(coverage.applied.contains("drop"), "{coverage:?}");
    assert!(heads(&bindings, "drop").is_empty(), "{bindings:?}");
    assert!(heads(&bindings, "guarded").is_empty(), "{bindings:?}");
    assert!(coverage.applied.contains("guarded"), "{coverage:?}");
    assert_eq!(heads(&bindings, "ev"), set(&["Lblnop"]), "{bindings:?}");
    assert!(coverage.applied.contains("weightAny"), "{coverage:?}");
    assert!(heads(&bindings, "weightAny").is_empty(), "{bindings:?}");
    let (wrapped, coverage) = bindings_of(
        &definition,
        state(&definition, &[item("Lblwr{}(Lblghost{}())")]),
        authored(),
        |_| {},
    );
    assert!(coverage.applied.contains("drop"), "{coverage:?}");
    assert_eq!(heads(&wrapped, "wr"), set(&["Lblghost"]), "{wrapped:?}");
    assert_eq!(
        heads(&wrapped, "wrapAny"),
        set(&["Lblghost"]),
        "{wrapped:?}"
    );
    assert!(heads(&wrapped, "drop").is_empty(), "{wrapped:?}");
    // A symbol the collection does not name is not recorded: here nothing is named, and nothing
    // is recorded.
    let (unnamed, _) = bindings_of(
        &definition,
        state(&definition, &program),
        BindingCollection::default(),
        |_| {},
    );
    assert_eq!(unnamed, RunBindings::default());
}

/// `guarded` fires on `inc(200)` with `N = 200`, an operand that is no application: it records
/// no head. `stop` binds the continuation `K` to the rest of the program, a sequence: `ghost`,
/// which only that rest holds, is recorded nowhere, and neither is `halt`, which `stop` only
/// inspects.
#[test]
fn a_continuation_variable_records_nothing() {
    let definition = definition();
    let program = [
        item(&format!("Lblinc{{}}({})", int(200))),
        item("Lblhalt{}()"),
        item("Lblghost{}()"),
    ];
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &program),
        authored(),
        |_| {},
    );
    assert!(coverage.applied.contains("stop"), "{coverage:?}");
    assert!(coverage.applied.contains("guarded"), "{coverage:?}");
    assert_eq!(bindings, RunBindings::default());
}

/// A cut-point rule's proposed successor is not committed: `wr` records nothing, while the
/// equation its successor's normalization applied gave a result and records as `applied` does.
#[test]
fn a_proposed_step_records_nothing() {
    let definition = definition();
    let program = [item("Lblwr{}(Lblnop{}())")];
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &program),
        authored(),
        |options| {
            options.cut_point_rules = BTreeSet::from(["wr".to_owned()]);
            options.collect_committed = true;
        },
    );
    assert!(coverage.applied.contains("wr"), "{coverage:?}");
    assert!(
        !coverage
            .committed
            .as_ref()
            .is_some_and(|committed| committed.contains("wr")),
        "{coverage:?}"
    );
    assert!(heads(&bindings, "wr").is_empty(), "{bindings:?}");
    assert_eq!(
        heads(&bindings, "wrapAny"),
        set(&["Lblnop"]),
        "{bindings:?}"
    );
}

fn op(value: i64) -> String {
    item(&format!("Lblop{{}}({})", int(value)))
}

fn values(values: &[i64]) -> Vec<BigInt> {
    values.iter().copied().map(BigInt::from).collect()
}

/// A selected binder keeps the least `cap` literals it was bound to, whatever order they came
/// in, and says that a further one was left out; a binder bound to a term with variables says
/// so. It is named by the axiom's label, and the binder of an axiom that never fired is absent.
#[test]
fn a_template_binders_values_are_capped() {
    let definition = definition();
    let selected = |cap| {
        authored()
            .with_binder("op", "B", cap)
            .with_binder("guarded", "N", cap)
    };
    let run = |program: &[String], cap| {
        bindings_of(
            &definition,
            state(&definition, program),
            selected(cap),
            |_| {},
        )
        .0
    };
    let forward = run(&[op(5), op(3), op(9), op(3)], 2);
    let backward = run(&[op(3), op(9), op(3), op(5)], 2);
    let expected = BinderValues {
        binder: BinderKey {
            axiom: "op".to_owned(),
            variable: "B".to_owned(),
        },
        values: values(&[3, 5]),
        truncated: true,
        nonliteral: false,
    };
    assert_eq!(binder(&forward, "op", "B"), Some(&expected), "{forward:?}");
    assert_eq!(forward, backward);
    assert_eq!(binder(&forward, "guarded", "N"), None, "{forward:?}");
    let whole = run(&[op(5), op(3), op(9), op(3)], 3);
    assert_eq!(
        binder(&whole, "op", "B"),
        Some(&BinderValues {
            values: values(&[3, 5, 9]),
            truncated: false,
            ..expected.clone()
        }),
        "{whole:?}"
    );
    // `op(Y)`: the binder is bound to a variable.
    let symbolic = bindings_of(
        &definition,
        state(&definition, &[item("Lblop{}(Y:SortInt{})"), op(4)]),
        selected(2),
        |_| {},
    )
    .0;
    assert_eq!(
        binder(&symbolic, "op", "B"),
        Some(&BinderValues {
            values: values(&[4]),
            truncated: false,
            nonliteral: true,
            ..expected
        }),
        "{symbolic:?}"
    );
}

/// The bindings, like the result, are the same however the run explores: a state-set run and a
/// path-set run of one deterministic program record the same bindings, and collecting changes
/// neither result.
#[test]
fn bindings_are_isolated_from_the_run() {
    use crate::search::ResultModality;
    let definition = definition();
    let program = [
        item(&format!("Lblinc{{}}({})", int(1))),
        op(7),
        item("Lblev{}(Lblnop{}())"),
    ];
    let collection = authored().with_binder("op", "B", 4);
    let runs = [ResultModality::PathSet, ResultModality::StateSet].map(|modality| {
        bindings_of(
            &definition,
            state(&definition, &program),
            collection.clone(),
            |options| options.result_modality = modality,
        )
        .0
    });
    assert_eq!(runs[0], runs[1]);
    assert_eq!(heads(&runs[0], "ev"), set(&["Lblnop"]), "{:?}", runs[0]);
    assert_eq!(
        binder(&runs[0], "op", "B").map(|values| values.values.clone()),
        Some(values(&[7])),
        "{:?}",
        runs[0]
    );
}

/// An equation's binder keeps the `Int` literals its fired instances bound, as a rule's does:
/// `sc` passes its operand to `scale`, whose equation `scaleAny` binds `V` by its `\in` to the
/// value. Selected under the equation's label and under its `UNIQUE_ID`, the binder is one
/// variable of one axiom: it is reported once, under the `UNIQUE_ID`, keeping the larger cap.
#[test]
fn an_equation_binders_literals_are_recorded_once_under_its_unique_id() {
    let definition = definition();
    let sc = |value: i64| item(&format!("Lblsc{{}}({})", int(value)));
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &[sc(6), sc(2), sc(9), item("Lblhalt{}()")]),
        authored()
            .with_binder("scaleAny", "V", 1)
            .with_binder("scale-id", "V", 2),
        |_| {},
    );
    assert!(coverage.applied.contains("scale-id"), "{coverage:?}");
    assert_eq!(
        bindings.binders,
        vec![BinderValues {
            binder: BinderKey {
                axiom: "scale-id".to_owned(),
                variable: "V".to_owned(),
            },
            values: values(&[2, 6]),
            truncated: true,
            nonliteral: false,
        }],
        "{bindings:?}"
    );
    assert_eq!(
        authored()
            .with_binder("scaleAny", "V", 1)
            .with_binder("scale-id", "V", 2)
            .selected_twice(&definition),
        Some((
            BinderKey {
                axiom: "scale-id".to_owned(),
                variable: "V".to_owned(),
            },
            BinderKey {
                axiom: "scaleAny".to_owned(),
                variable: "V".to_owned(),
            },
        ))
    );
    assert_eq!(
        authored()
            .with_binder("scaleAny", "V", 1)
            .with_binder("op", "B", 2)
            .selected_twice(&definition),
        None
    );
}

/// The state `sf(program, cell)`.
fn cell_state(definition: &BackendDefinition, program: &[String], cell: &str) -> Pattern {
    let source = format!("sf{{}}({}, {cell})", sequence(program));
    Pattern {
        term: definition
            .internalize_term(&parse_pattern(&source).expect("term should parse"), &[])
            .expect("term should internalize"),
        constraints: Vec::new(),
    }
}

/// `mark` overwrites the cell, `<f> _ => ghost </f>`: its `F` binds the cell's `nop` and no other
/// part of the rule reads it, so the step carried `nop` to its end and dropped it, and records no
/// head. `copy` puts the cell's value in its result: its `F` records `ghost`. `sfdrop` discards
/// the item it binds and keeps the cell, so it records the cell's head and not the item's.
/// `twice` names `A` twice in its left-hand side, so the match compares the two values: `A`
/// records `nop`. Whether a variable is read is decided per axiom when it is loaded.
#[test]
fn a_value_the_step_never_reads_records_no_head() {
    let definition = definition();
    let unread = |label: &str| {
        definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values().flatten())
            .find(|rule| rule.rule.attributes.label.as_deref() == Some(label))
            .map(|rule| {
                rule.rule
                    .computed_attributes
                    .unread_variables
                    .iter()
                    .map(|variable| {
                        crate::term::names::rule_variable_definition_name(&variable.name)
                    })
                    .collect::<BTreeSet<_>>()
            })
            .expect("the rule is in the definition")
    };
    assert_eq!(unread("mark"), set(&["F"]));
    assert_eq!(unread("copy"), set(&[]));
    assert_eq!(unread("twice"), set(&[]));
    assert_eq!(unread("sfdrop"), set(&["X"]));
    let (bindings, coverage) = bindings_of(
        &definition,
        cell_state(
            &definition,
            &[
                item("Lblmark{}()"),
                item("Lblcopy{}()"),
                item("Lblpair{}(Lblnop{}(), Lblnop{}())"),
            ],
            "Lblnop{}()",
        ),
        authored(),
        |_| {},
    );
    for label in ["mark", "copy", "sfdrop", "twice"] {
        assert!(coverage.applied.contains(label), "{label}: {coverage:?}");
    }
    assert!(heads(&bindings, "mark").is_empty(), "{bindings:?}");
    assert_eq!(heads(&bindings, "copy"), set(&["Lblghost"]), "{bindings:?}");
    assert_eq!(
        heads(&bindings, "sfdrop"),
        set(&["Lblghost"]),
        "{bindings:?}"
    );
    assert_eq!(
        heads(&bindings, "twice"),
        set(&["Lblnop", "Lblghost"]),
        "{bindings:?}"
    );
}

/// `either`'s left-hand side is a disjunction, loaded as one rule per disjunct under one id:
/// `committed` names the axiom, and the bindings name the disjunct its fired instance took,
/// `left` (0) and never `right` (1). `split` builds a successor per alternative of its
/// right-hand side, and the run committed to both: each is named. An axiom with one alternative
/// of each side is never listed.
#[test]
fn a_fired_instance_names_the_alternative_it_took() {
    let definition = definition();
    let alternative = |axiom: &str, lhs, rhs| FiredAlternative {
        axiom: axiom.to_owned(),
        lhs,
        rhs,
    };
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &[item("Lblleft{}()"), item("Lblhalt{}()")]),
        BindingCollection::default(),
        |options| options.collect_committed = true,
    );
    assert!(
        coverage
            .committed
            .as_ref()
            .is_some_and(|committed| committed.contains("either")),
        "{coverage:?}"
    );
    assert_eq!(
        bindings.alternatives,
        vec![alternative("either", Some(0), None)],
        "{bindings:?}"
    );
    let (bindings, _) = bindings_of(
        &definition,
        state(&definition, &[item("Lblsplit{}()")]),
        BindingCollection::default(),
        |_| {},
    );
    assert_eq!(
        bindings.alternatives,
        vec![
            alternative("either", Some(0), None),
            alternative("split", None, Some(0)),
            alternative("split", None, Some(1)),
        ],
        "{bindings:?}"
    );
}
