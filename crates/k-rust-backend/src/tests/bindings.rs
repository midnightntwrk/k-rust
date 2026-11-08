//! Bindings of fired instances (`crate::coverage::bindings`): a run that asks for them records,
//! per axiom, the named symbols that were the head of an operand of a fired instance, and the
//! values selected template binders were bound to, capped.
//!
//! The axioms carry labels and, but for `scaleAny`, no `UNIQUE_ID`, so each other one's id is
//! its label. Every run here
//! ends by itself well inside its depth bound and sets no step timeout, so none depends on a
//! clock.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use num_bigint::BigInt;

use crate::{
    coverage::{BinderKey, BinderValues, BindingCollection, RunBindings, RunCoverage},
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

/// The authored symbols, which a front end names.
const AUTHORED: [&str; 7] = [
    "Lblinc", "Lblhalt", "Lblghost", "Lblop", "Lblev", "Lblnop", "Lblgate",
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
        // Matched on every `gate`, fired only above 100; its operand `I` has a head.
        rule(
            "gate",
            &item("Lblgate{}(N:SortInt{}, I:SortInstr{})"),
            "st{}(K:SortK{})",
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
        // An item bound at sort `KItem`, through its injection.
        rule("drop", "X:SortKItem{}", "st{}(K:SortK{})", "", 50),
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
/// the head of its operand `I` nor a value of its binder `N`, while `drop`, which takes the
/// step, records the instruction it took through its injection. Where its guard holds, at
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
    assert_eq!(heads(&bindings, "drop"), set(&["Lblgate"]), "{bindings:?}");
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

/// A committed step records the head of each operand: `drop`'s `X:KItem` bound to
/// `inj{Instr, KItem}(inc(200))` records `inc`, `ev`'s `I:Instr` bound to `nop()` records `nop`,
/// and so does the equation `weightAny`, whose instance in `ev`'s successor gave a result. With
/// no `collect_committed`, they are recorded all the same.
#[test]
fn a_committed_step_records_its_operands_heads_through_injections() {
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
    assert_eq!(heads(&bindings, "drop"), set(&["Lblghost"]), "{bindings:?}");
    assert!(heads(&bindings, "guarded").is_empty(), "{bindings:?}");
    assert!(coverage.applied.contains("guarded"), "{coverage:?}");
    assert_eq!(heads(&bindings, "ev"), set(&["Lblnop"]), "{bindings:?}");
    assert_eq!(
        heads(&bindings, "weightAny"),
        set(&["Lblnop"]),
        "{bindings:?}"
    );
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

/// A cut-point rule's proposed successor is not committed: `ev` records nothing, while the
/// equation its successor's normalization applied gave a result and records as `applied` does.
#[test]
fn a_proposed_step_records_nothing() {
    let definition = definition();
    let program = [item("Lblev{}(Lblnop{}())")];
    let (bindings, coverage) = bindings_of(
        &definition,
        state(&definition, &program),
        authored(),
        |options| {
            options.cut_point_rules = BTreeSet::from(["ev".to_owned()]);
            options.collect_committed = true;
        },
    );
    assert!(coverage.applied.contains("ev"), "{coverage:?}");
    assert!(
        !coverage
            .committed
            .as_ref()
            .is_some_and(|committed| committed.contains("ev")),
        "{coverage:?}"
    );
    assert!(heads(&bindings, "ev").is_empty(), "{bindings:?}");
    assert_eq!(
        heads(&bindings, "weightAny"),
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
    assert_eq!(heads(&runs[0], "drop"), set(&["Lblinc"]), "{:?}", runs[0]);
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
