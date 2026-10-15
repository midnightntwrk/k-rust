//! What a collection in an execution leaf denotes, and how the leaf's state writes it
//! (`docs/compatibility.md`, "Collections in results").
//!
//! A leaf's state writes each collection with its sort's own unit, element and concat symbols,
//! one element application per item, and internalizes back to an equal term. Its content is its
//! items, not the order they were inserted in. No leaf whose state was normalised holds a map or
//! set with two syntactically equal keys or elements, since such a collection is undefined where
//! it is built; a leaf taken before its state was normalised (work-bound, breadth-bound, timeout)
//! keeps the state as given. Keys or elements that are neither equal nor apart split the step on
//! their definedness condition.
//! Every run goes through the facade as a consumer does: strategy `all`, the path-set modality,
//! and `execute` and `execute_observed` giving the same leaves.

use std::sync::Arc;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionLeaf, ExecutionResult, ExecutionStrategy,
        HaltReasonOutput, ObservedRequest, ResultModalityOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{ast::Pattern as KorePattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_backend::{
    confluence::ViolationKind,
    definition::BackendDefinition,
    externalize,
    rule::TermIndex,
    term::{CollectionMetadata, Sort, Term, TermKind},
};
use k_rust_kore::kore::walk;

#[path = "support/shared.rs"]
mod shared;

const SOURCE: &str = r#"module COLL
  imports INT
  imports BOOL
  imports MAP
  imports SET
  imports LIST
  imports STRING

  syntax Prog ::= p(Int) [symbol(p)] | done(KItem) [symbol(done)]
  syntax Map ::= f(Int) [function, symbol(f)]
  syntax Int ::= g(Int) [function, symbol(g)]
  syntax Map ::= dup(Int) [function, total, symbol(dup)]
  syntax List ::= lf(Int) [function, symbol(lf)]
  syntax Int ::= id(Int) [function, symbol(id)]
  rule f(0) => .Map
  rule id(X) => X
  rule dup(I) => (I |-> 1) (I |-> 2)

  configuration <k> $PGM:Prog </k>

  rule [p1]: p(1) => done(.Map [1 <- 10] [2 <- 20] ["x" <- SetItem(3) SetItem(4)])
  rule [p2]: p(2) => done(.Map ["x" <- SetItem(4) SetItem(3)] [2 <- 20] [1 <- 10])
  rule [p3]: p(3) => done((2 |-> 20) (1 |-> 10))
  rule [p4]: p(4) => done((1 |-> 10) (1 |-> 20))
  rule [p5]: p(5) => done((1 |-> 10) (1 |-> 10))
  rule [p6]: p(6) => done(SetItem(1) SetItem(1))
  rule [p7]: p(7) => done(dup(1))
  rule [p8]: p(8) => done((1 |-> 10) f(3))
  rule [p9]: p(9) => done((g(1) |-> 10) (2 |-> 20))
  rule [p10]: p(10) => done(ListItem(1) ListItem(2))
  rule [p11]: p(11) => done(ListItem(2) ListItem(1))
  rule [p12]: p(12) => done(ListItem(1) lf(1) ListItem(2) lf(2))
  rule [p13]: p(13) => done((1 |-> 10) f(3) f(4))
  rule [p14]: p(14) => done((g(1) |-> 10) (g(1) |-> 20))
  rule [p15]: p(15) => done(SetItem(g(1)) SetItem(g(2)))
  rule [p16]: p(16) => done((1 |-> 10) (2 |-> 20))
  rule [p17]: p(17) => done((1 |-> 1) (2 |-> 2) (1 |-> 3))
  rule [p18]: p(18) => done(SetItem(id(1)) SetItem(1))
  rule [p19]: p(19) => done(ListItem(1) ListItem(1))
endmodule
"#;

fn definition_kore() -> std::sync::Arc<String> {
    static KORE: shared::Shared<String> = shared::Shared::new();
    KORE.get(|| compile(SOURCE, "COLL"))
}

fn compile(source: &str, main: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("coll.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

fn backend() -> Backend {
    Backend::new(&definition_kore(), "COLL", BackendOptions::default()).unwrap()
}

fn top(k: &str) -> String {
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}({k}, dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn program(number: u32) -> String {
    top(&format!(
        "inj{{SortProg{{}}, SortKItem{{}}}}(Lblp{{}}(\\dv{{SortInt{{}}}}(\"{number}\")))"
    ))
}

/// The last program of `SOURCE`.
const LAST: u32 = 19;

/// The request of `state`, with `bound` applied to it (a work, breadth or step-time bound).
fn request(state: &str, assume_state_defined: bool, bound: Bound) -> ExecuteRequest {
    let mut request = ExecuteRequest {
        result_modality: ResultModalityOutput::PathSet,
        strategy: ExecutionStrategy::All,
        assume_state_defined,
        ..ExecuteRequest::new(parse_pattern(state).unwrap())
    };
    bound(&mut request);
    request
}

/// A change to a request that bounds its run.
type Bound = fn(&mut ExecuteRequest);

fn text(leaf: &ExecutionLeaf) -> String {
    Printer::compact().print_pattern(&state(leaf))
}

fn state(leaf: &ExecutionLeaf) -> KorePattern {
    codec::from_value(&leaf.state).unwrap()
}

type Summary = Vec<(HaltReasonOutput, u64, Option<String>, String)>;

fn summary(result: &ExecutionResult) -> Summary {
    result
        .leaves
        .iter()
        .map(|leaf| (leaf.reason, leaf.depth, leaf.rule_id.clone(), text(leaf)))
        .collect()
}

/// The leaves of `state` under strategy `all` and the path-set modality, which `execute` and
/// `execute_observed` must give alike.
fn run_state(backend: &mut Backend, state: &str, assume_state_defined: bool) -> ExecutionResult {
    run_bounded(backend, state, assume_state_defined, |_| {})
}

/// [`run_state`] with `bound` applied to both requests.
fn run_bounded(
    backend: &mut Backend,
    state: &str,
    assume_state_defined: bool,
    bound: Bound,
) -> ExecutionResult {
    let plain = backend
        .execute(request(state, assume_state_defined, bound))
        .unwrap();
    let observed = backend
        .execute_observed(ObservedRequest {
            request: request(state, assume_state_defined, bound),
            rules: Some(Vec::new()),
        })
        .unwrap();
    assert_eq!(summary(&plain), summary(&observed), "{state}");
    plain
}

fn run(backend: &mut Backend, number: u32) -> ExecutionResult {
    run_state(backend, &program(number), false)
}

const BOTTOM: &str = r"\bottom{SortGeneratedTopCell{}}()";

fn definition(backend: &mut Backend) -> Arc<BackendDefinition> {
    backend.select_definition(None).unwrap()
}

/// The internal term of a leaf state and its constraints, as a consumer reads the state back.
fn internalized(
    definition: &BackendDefinition,
    state: &KorePattern,
) -> k_rust_backend::rewrite::Pattern {
    definition
        .admit_unverified(state, &[])
        .internalize_pattern()
        .unwrap_or_else(|error| panic!("{error}: {}", Printer::compact().print_pattern(state)))
}

/// Every subterm of `term` that is a collection, outermost first, through applications,
/// injections and the items and rests of collections.
fn collections(term: &Term) -> Vec<Term> {
    let mut found = Vec::new();
    let mut pending = vec![term.clone()];
    while let Some(term) = pending.pop() {
        match term.kind() {
            TermKind::Application { arguments, .. } => pending.extend(arguments.iter().cloned()),
            TermKind::Injection { term: inner, .. } => pending.push(inner.clone()),
            TermKind::And(left, right) => pending.extend([left.clone(), right.clone()]),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries.iter() {
                    pending.extend([key.clone(), value.clone()]);
                }
                pending.extend(rest.iter().cloned());
                found.push(term.clone());
            }
            TermKind::Set { elements, rest, .. } => {
                pending.extend(elements.iter().cloned());
                pending.extend(rest.iter().cloned());
                found.push(term.clone());
            }
            TermKind::List { heads, rest, .. } => {
                pending.extend(heads.iter().cloned());
                if let Some((middle, tails)) = rest {
                    pending.push(middle.clone());
                    pending.extend(tails.iter().cloned());
                }
                found.push(term.clone());
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }
    found
}

/// The outermost collection in a leaf's configuration: a collection term, or an application of
/// a collection's concat symbol that holds two opaque parts.
fn done_collection(definition: &BackendDefinition, leaf: &ExecutionLeaf) -> Term {
    let pattern = internalized(definition, &state(leaf));
    let mut pending = std::collections::VecDeque::from([pattern.term.clone()]);
    while let Some(term) = pending.pop_front() {
        match term.kind() {
            TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. } => return term,
            TermKind::Application {
                symbol, arguments, ..
            } => {
                if symbol.attributes.collection.is_some() {
                    return term.clone();
                }
                pending.extend(arguments.iter().cloned());
            }
            TermKind::Injection { term: inner, .. } => pending.push_back(inner.clone()),
            TermKind::And(..) | TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }
    panic!("no collection in {}", text(leaf))
}

fn leaf(result: &ExecutionResult, reason: HaltReasonOutput) -> &ExecutionLeaf {
    let mut found = result.leaves.iter().filter(|leaf| leaf.reason == reason);
    let leaf = found
        .next()
        .unwrap_or_else(|| panic!("no {reason:?} leaf: {:#?}", summary(result)));
    assert!(
        found.next().is_none(),
        "one {reason:?} leaf: {:#?}",
        summary(result)
    );
    leaf
}

fn rule_id(backend: &Backend, label: &str) -> String {
    let label = format!("COLL.{label}");
    backend
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .find(|rule| rule.label.as_deref() == Some(label.as_str()))
        .unwrap_or_else(|| panic!("no rule {label}"))
        .id
}

/// Whether a map or set in `term` holds two syntactically equal keys or elements.
fn has_repeat(term: &Term) -> bool {
    collections(term).iter().any(|collection| {
        let items = match collection.kind() {
            TermKind::Map { entries, .. } => entries.iter().map(|(key, _)| key.clone()).collect(),
            TermKind::Set { elements, .. } => elements.iter().cloned().collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        items
            .iter()
            .enumerate()
            .any(|(index, item)| items[..index].contains(item))
    })
}

#[test]
fn a_map_and_a_set_built_in_two_orders_give_equal_leaf_states() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    let one = run(&mut backend, 1);
    let two = run(&mut backend, 2);
    let stuck = leaf(&one, HaltReasonOutput::Stuck);
    assert_eq!(stuck.state, leaf(&two, HaltReasonOutput::Stuck).state);
    let map = done_collection(&definition, stuck);
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        panic!("{map:?}");
    };
    assert!(rest.is_none() && entries.len() == 3, "{map:?}");
    let sets = collections(&map)
        .into_iter()
        .filter(|term| matches!(term.kind(), TermKind::Set { rest: None, .. }))
        .count();
    assert_eq!(sets, 1, "{map:?}");
    // The same map written in the other order.
    assert_eq!(
        leaf(&run(&mut backend, 3), HaltReasonOutput::Stuck).state,
        leaf(&run(&mut backend, 16), HaltReasonOutput::Stuck).state
    );
}

#[test]
fn a_list_keeps_its_order() {
    let mut backend = backend();
    let item = |value: i64| {
        format!(
            "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    let list = |first: i64, second: i64| {
        format!("Lbl'Unds'List'Unds'{{}}({}, {})", item(first), item(second))
    };
    let ten = text(leaf(&run(&mut backend, 10), HaltReasonOutput::Stuck));
    let eleven = text(leaf(&run(&mut backend, 11), HaltReasonOutput::Stuck));
    assert!(ten.contains(&list(1, 2)), "{ten}");
    assert!(eleven.contains(&list(2, 1)), "{eleven}");
    // A list may hold equal items: it is a sequence, and `ListItem(1) ListItem(1)` has two.
    let definition = definition(&mut backend);
    let result = run(&mut backend, 19);
    let stuck = leaf(&result, HaltReasonOutput::Stuck);
    assert!(text(stuck).contains(&list(1, 1)), "{}", text(stuck));
    let held = done_collection(&definition, stuck);
    let TermKind::List {
        heads, rest: None, ..
    } = held.kind()
    else {
        panic!("{held:?}");
    };
    assert_eq!(heads.len(), 2);
}

#[test]
fn no_leaf_state_holds_a_repeated_key_or_element() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    // The step's own right-hand side builds the repeat: an undefined step, reported over the
    // pre-step configuration, with no constraint.
    // A function's equation that is not `total` gives the same leaf (p(18), `id(1)` beside `1`),
    // and so does a repeat whose equal keys are not adjacent as written (p(17)).
    for (number, label) in [
        (4, "p4"),
        (5, "p5"),
        (6, "p6"),
        (14, "p14"),
        (17, "p17"),
        (18, "p18"),
    ] {
        let result = run(&mut backend, number);
        let [trivial] = &result.leaves[..] else {
            panic!("p({number}): {:#?}", summary(&result));
        };
        assert_eq!(trivial.reason, HaltReasonOutput::Trivial);
        assert_eq!(trivial.depth, 0);
        assert_eq!(trivial.rule_id, Some(rule_id(&backend, label)));
        assert_eq!(text(trivial), program(number), "p({number})");
        assert!(trivial.contradicted_total.is_none());
    }
    // A `total` function's equation builds it after the step: the same pre-step leaf, naming the
    // contradicted attribute.
    let result = run(&mut backend, 7);
    let [trivial] = &result.leaves[..] else {
        panic!("p(7): {:#?}", summary(&result));
    };
    assert_eq!(trivial.reason, HaltReasonOutput::Trivial);
    assert_eq!(trivial.depth, 0);
    assert_eq!(trivial.rule_id, Some(rule_id(&backend, "p7")));
    assert_eq!(text(trivial), program(7));
    assert!(trivial.contradicted_total.is_some());
    // An initial configuration holding a repeat is undefined: one vacuous leaf, whether or not
    // the request assumes the state defined.
    let entry = |key: i64, value: i64| {
        format!(
            "Lbl'UndsPipe'-'-GT-Unds'{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{key}\")), inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    let initial = top(&format!(
        "inj{{SortProg{{}}, SortKItem{{}}}}(Lbldone{{}}(inj{{SortMap{{}}, SortKItem{{}}}}(Lbl'Unds'Map'Unds'{{}}({}, {}))))",
        entry(1, 10),
        entry(1, 20)
    ));
    for assume_state_defined in [false, true] {
        let result = run_state(&mut backend, &initial, assume_state_defined);
        let [vacuous] = &result.leaves[..] else {
            panic!("{assume_state_defined}: {:#?}", summary(&result));
        };
        assert_eq!(vacuous.reason, HaltReasonOutput::Vacuous);
        assert_eq!(vacuous.depth, 0);
        assert_eq!(text(vacuous), BOTTOM, "{assume_state_defined}");
    }
    // The exception: a leaf taken before its state is normalised keeps the state as it was
    // given, repeat included. A work budget of 0, a breadth bound of 0 and a step time of 0 each
    // stop before the initial state is normalised, deterministically. The leaf still reads back
    // and is written again alike.
    let bounds: [(Bound, HaltReasonOutput); 3] = [
        (
            |request| request.max_work = Some(0),
            HaltReasonOutput::WorkBound,
        ),
        (
            |request| request.max_breadth = Some(0),
            HaltReasonOutput::BreadthBound,
        ),
        (
            |request| request.step_timeout_ms = Some(0),
            HaltReasonOutput::Timeout,
        ),
    ];
    for ((bound, reason), assume_state_defined) in bounds
        .into_iter()
        .flat_map(|bound| [(bound, false), (bound, true)])
    {
        let result = run_bounded(&mut backend, &initial, assume_state_defined, bound);
        let [bound] = &result.leaves[..] else {
            panic!("{reason:?} {assume_state_defined}: {:#?}", summary(&result));
        };
        assert_eq!(bound.reason, reason, "{assume_state_defined}");
        assert_eq!(bound.depth, 0);
        let pattern = internalized(&definition, &state(bound));
        assert!(has_repeat(&pattern.term), "{}", text(bound));
        assert_eq!(externalize::term(&pattern.term), state(bound));
        assert_eq!(
            internalized(&definition, &externalize::constrained_pattern(&pattern)),
            pattern
        );
    }
    // No leaf of the file holds one.
    for number in 1..=LAST {
        for leaf in &run(&mut backend, number).leaves {
            if text(leaf) != BOTTOM {
                let pattern = internalized(&definition, &state(leaf));
                assert!(!has_repeat(&pattern.term), "p({number}): {}", text(leaf));
            }
        }
    }
}

#[test]
fn a_definedness_condition_splits_the_step() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    for (number, label) in [(8, "p8"), (9, "p9"), (15, "p15")] {
        let result = run(&mut backend, number);
        assert_eq!(
            result.leaves.len(),
            2,
            "p({number}): {:#?}",
            summary(&result)
        );
        let trivial = leaf(&result, HaltReasonOutput::Trivial);
        assert_eq!(trivial.depth, 0);
        assert_eq!(trivial.rule_id, Some(rule_id(&backend, label)));
        let trivial = internalized(&definition, &state(trivial));
        assert_eq!(
            externalize::term(&trivial.term),
            parse_pattern(&program(number)).unwrap(),
            "p({number}): the Trivial leaf is the pre-step configuration"
        );
        assert!(
            !trivial.constraints.is_empty(),
            "p({number}): under the negated condition"
        );
        let stuck = leaf(&result, HaltReasonOutput::Stuck);
        assert_eq!(stuck.depth, 1);
        assert!(
            !internalized(&definition, &state(stuck))
                .constraints
                .is_empty(),
            "p({number}): the successor is under the condition"
        );
    }
    let result = run(&mut backend, 8);
    let trivial = text(leaf(&result, HaltReasonOutput::Trivial));
    assert!(
        trivial.ends_with(
            r#", \not{SortGeneratedTopCell{}}(\and{SortGeneratedTopCell{}}(\ceil{SortMap{}, SortGeneratedTopCell{}}(Lblf{}(\dv{SortInt{}}("3"))), \not{SortGeneratedTopCell{}}(\equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), Lblf{}(\dv{SortInt{}}("3"))))))))"#
        ),
        "{trivial}"
    );
    let stuck = leaf(&result, HaltReasonOutput::Stuck);
    assert!(
        text(stuck).contains(r#"Lbl'Unds'Map'Unds'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("1")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("10"))), Lblf{}(\dv{SortInt{}}("3")))"#),
        "{}",
        text(stuck)
    );
    let map = done_collection(&definition, stuck);
    let TermKind::Map { entries, rest, .. } = map.kind() else {
        panic!("{map:?}");
    };
    assert_eq!(entries.len(), 1);
    let Some(rest) = rest else { panic!("{map:?}") };
    assert!(
        matches!(rest.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "Lblf"),
        "{rest:?}"
    );
}

#[test]
fn raw_concat_nodes_are_written_as_built() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    // Two opaque middles: the list is a raw concat of a list with a middle and the second one.
    let result = run(&mut backend, 12);
    let stuck = leaf(&result, HaltReasonOutput::Stuck);
    let item = |value: i64| {
        format!(
            "LblListItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\")))"
        )
    };
    let lf = |value: i64| format!("Lbllf{{}}(\\dv{{SortInt{{}}}}(\"{value}\"))");
    assert!(
        text(stuck).contains(&format!(
            "Lbl'Unds'List'Unds'{{}}(Lbl'Unds'List'Unds'{{}}({}, Lbl'Unds'List'Unds'{{}}({}, {})), {})",
            item(1),
            lf(1),
            item(2),
            lf(2)
        )),
        "{}",
        text(stuck)
    );
    let list = done_collection(&definition, stuck);
    let TermKind::Application {
        symbol, arguments, ..
    } = list.kind()
    else {
        panic!("{list:?}");
    };
    assert_eq!(symbol.name.as_ref(), "Lbl'Unds'List'Unds'");
    let TermKind::List {
        heads,
        rest: Some((middle, tails)),
        ..
    } = arguments[0].kind()
    else {
        panic!("{list:?}");
    };
    assert_eq!((heads.len(), tails.len()), (1, 1), "{list:?}");
    assert!(
        matches!(middle.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "Lbllf")
    );
    assert!(
        matches!(arguments[1].kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "Lbllf")
    );
    // Two opaque rests: the map's rest is a raw concat of the two.
    let result = run(&mut backend, 13);
    let stuck = leaf(&result, HaltReasonOutput::Stuck);
    let map = done_collection(&definition, stuck);
    let TermKind::Map {
        entries,
        rest: Some(rest),
        ..
    } = map.kind()
    else {
        panic!("{map:?}");
    };
    assert_eq!(entries.len(), 1);
    assert!(
        matches!(rest.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == "Lbl'Unds'Map'Unds'"),
        "{rest:?}"
    );
}

/// A leaf state reads back to its internal pattern: its configuration, which holds the
/// collections, is written again exactly as it was, and reading the written pattern gives an equal
/// pattern. A constraint over partial terms may gain the definedness conjuncts the reading states
/// for it (`\not(P)` over `f(3)` is read as `\not(\ceil(f(3)) and P)`), after which it too is
/// written again exactly.
#[test]
fn a_collection_leaf_state_round_trips() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    for number in 1..=LAST {
        for leaf in &run(&mut backend, number).leaves {
            if text(leaf) == BOTTOM {
                continue;
            }
            let pattern = internalized(&definition, &state(leaf));
            let written_state = state(leaf);
            let configuration = match &written_state {
                KorePattern::And { arguments, .. } => &arguments[0],
                configuration => configuration,
            };
            assert_eq!(
                &externalize::term(&pattern.term),
                configuration,
                "p({number})"
            );
            let written = externalize::constrained_pattern(&pattern);
            if pattern.constraints.is_empty() {
                assert_eq!(Printer::compact().print_pattern(&written), text(leaf));
            }
            let read = internalized(&definition, &written);
            assert_eq!(read, pattern, "p({number})");
            assert_eq!(
                externalize::constrained_pattern(&read),
                written,
                "p({number})"
            );
        }
    }
}

#[test]
fn collection_states_use_only_their_own_role_symbols() {
    let mut backend = backend();
    let definition = definition(&mut backend);
    let symbols = definition.symbols();
    let collection_sort = |collection: &CollectionMetadata| Sort::Application {
        name: match collection {
            CollectionMetadata::Map(map) => map.map_sort.clone(),
            CollectionMetadata::List(list) | CollectionMetadata::Set(list) => {
                list.list_sort.clone()
            }
        },
        arguments: Vec::new(),
    };
    let mut nodes = 0;
    for number in 1..=LAST {
        for leaf in &run(&mut backend, number).leaves {
            let mut pending = vec![state(leaf)];
            while let Some(pattern) = pending.pop() {
                if let KorePattern::Application { symbol, arguments } = &pattern
                    && let Some(collection) = symbols
                        .get(symbol.name.as_str())
                        .and_then(|symbol| symbol.attributes.collection.as_ref())
                {
                    nodes += 1;
                    let roles = match collection {
                        CollectionMetadata::Map(map) => &map.symbols,
                        CollectionMetadata::List(list) | CollectionMetadata::Set(list) => {
                            &list.symbols
                        }
                    };
                    if symbol.name.as_str() == roles.concat.as_ref() {
                        // Each operand is a node of the same collection or an opaque term of
                        // its sort, never an item outside an element application.
                        for operand in arguments {
                            let own = matches!(operand, KorePattern::Application { symbol, .. }
                                if symbols.get(symbol.name.as_str()).and_then(|symbol| symbol.attributes.collection.as_ref()) == Some(collection));
                            if !own {
                                let term = definition
                                    .admit_unverified(operand, &[])
                                    .internalize_term()
                                    .unwrap();
                                assert_eq!(
                                    term.sort(),
                                    collection_sort(collection),
                                    "p({number}): {}",
                                    Printer::compact().print_pattern(operand)
                                );
                            }
                        }
                    }
                }
                pending.extend(walk::children(&pattern).into_iter().cloned());
            }
        }
    }
    assert!(nodes > 0);
}

/// The kinds of the violated value-claim preconditions of the definition `ROLES` whose rule
/// `axiom` is rooted at a collection role symbol.
fn violations_with(axiom: &str) -> Vec<ViolationKind> {
    let source = format!(
        "module ROLES\n  imports INT\n  imports BOOL\n  imports LIST\n  imports SET\n  syntax Prog ::= start(Int) | done(List, Set)\n  {axiom}\n  configuration <k> $PGM:Prog </k>\n  rule start(I) => done(ListItem(I), SetItem(I))\nendmodule\n"
    );
    let kore = compile(&source, "ROLES");
    let mut backend = Backend::new(&kore, "ROLES", BackendOptions::default()).unwrap();
    let definition = definition(&mut backend);
    definition
        .value_claims()
        .violations()
        .iter()
        .map(|violation| violation.kind.clone())
        .collect()
}

/// An axiom rooted at a collection role symbol is never applied. The load reports an executable
/// equation without `symbolic` (`concrete` or not) as indexed at the collection; it reports
/// neither a `symbolic` equation nor a `simplification` rooted there, which a consumer checks
/// itself (docs, "Collections in results").
#[test]
fn an_equation_rooted_at_a_role_symbol_is_reported() {
    let indexed = |violations: &[ViolationKind], index: TermIndex| {
        violations.contains(&ViolationKind::IndexedAt(index))
    };
    for axiom in [
        "rule ListItem(1) => ListItem(2)",
        "rule ListItem(X:Int) => ListItem(0) [concrete]",
    ] {
        let violations = violations_with(axiom);
        assert!(
            indexed(&violations, TermIndex::List),
            "{axiom}: {violations:#?}"
        );
    }
    for (axiom, index) in [
        (
            "rule ListItem(X:Int) => ListItem(0) [symbolic]",
            TermIndex::List,
        ),
        (
            "rule SetItem(1) => SetItem(2) [simplification]",
            TermIndex::Set,
        ),
    ] {
        let violations = violations_with(axiom);
        assert!(!indexed(&violations, index), "{axiom}: {violations:#?}");
    }
}
