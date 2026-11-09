//! Variable identity at the response level (`docs/compatibility.md` "Variable names").
//!
//! A name read from KORE is kept verbatim and printed unchanged; every other name the backend
//! prints is escaped injectively (`term::names::encode_variable_name`), and every free variable
//! a rewrite request introduces is minted from the request's one counter
//! (`fresh::FreshCounter`), spelled like no variable of the request. These tests check the
//! contract on what an execution emits, not on the functions that implement it:
//!
//! - (a) the map-selection execution whose initial frame is spelled `ExFrame0`;
//! - (b) a response-level property over a corpus of rewrite definitions (below), with every
//!   state an execution reports observed: the initial state, the endpoints of every
//!   normalization and transition, every rule binding, every leaf;
//! - (c) two narrowings whose rule variables are `VarI1` and `VarI`, separated by nine burns.
//!
//! A printed pattern read back is the internal pattern up to a renaming of its variables that
//! is a bijection and the identity on the request's names: printing it again gives the same
//! text. Round trips are compared at the level of names (free variables with kind and sort,
//! and bound names), not as whole patterns: collection and predicate normalizations unrelated
//! to names may re-associate a re-internalized pattern.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_backend::{
    definition::BackendDefinition,
    externalize::{self, Printable},
    rewrite::{ExecutionOptions, ExecutionResult, Pattern, execute_observed_with_solver},
    rule::Predicate,
    smt::SmtSolver,
    term::{
        Term, Variable,
        names::{encode_variable_name, split_fresh_counter},
    },
    transition::{ObservationEvent, ObservationOptions},
};
use k_rust_kore::kore::{
    ast as kore,
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

// ---------------------------------------------------------------------------------------
// Name-level views of patterns.

fn free_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    let mut variables = pattern.term.attributes().variables.to_btree_set();
    for predicate in &pattern.constraints {
        variables.extend(predicate.free_variables());
    }
    variables
}

fn bound_names_of(predicate: &Predicate, names: &mut BTreeSet<String>) {
    match predicate {
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Defined(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        // An absence prints with a binder of its own (`Absence::binder`), named apart from
        // its key and rest; it reads back as the absence, not as a quantifier.
        | Predicate::Absent(_) => {}
        Predicate::Not(inner) => bound_names_of(inner, names),
        Predicate::And(inner) | Predicate::Or(inner) => {
            for predicate in inner.iter() {
                bound_names_of(predicate, names);
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            bound_names_of(left, names);
            bound_names_of(right, names);
        }
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            names.insert(variable.name.to_string());
            bound_names_of(inner, names);
        }
    }
}

/// The names bound in `pattern` (terms bind nothing; quantifiers occur in constraints).
fn bound_names(pattern: &Pattern) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for predicate in &pattern.constraints {
        bound_names_of(predicate, &mut names);
    }
    names
}

/// Every variable spelling of a printed pattern, occurrences and binders, with its sort.
#[cfg(feature = "z3")]
fn printed_names(pattern: &kore::Pattern, names: &mut BTreeSet<(String, String)>) {
    match pattern {
        kore::Pattern::Variable(variable) => {
            names.insert((variable.name.clone(), format!("{:?}", variable.sort)));
        }
        kore::Pattern::Exists { variable, .. } | kore::Pattern::Forall { variable, .. } => {
            names.insert((variable.name.clone(), format!("{:?}", variable.sort)));
        }
        _ => {}
    }
    for child in k_rust_kore::kore::walk::children(pattern) {
        printed_names(child, names);
    }
}

/// `variable` as it reads back from its printed spelling.
fn printed(variable: &Variable) -> Variable {
    variable.with_name(encode_variable_name(&variable.name))
}

// ---------------------------------------------------------------------------------------
// The contract.

/// A request: its initial state, its free variables, and the names of all its variables.
struct Request {
    initial: Pattern,
    free: BTreeSet<Variable>,
    names: BTreeSet<String>,
}

impl Request {
    fn new(initial: Pattern) -> Self {
        let free = free_variables(&initial);
        let mut names = bound_names(&initial);
        names.extend(free.iter().map(|variable| variable.name.to_string()));
        Self {
            initial,
            free,
            names,
        }
    }

    /// Whether `name` is a rewrite mint: `{base}!{N}`. No name read from KORE contains `!`.
    fn is_rewrite_mint(name: &str) -> bool {
        !split_fresh_counter(name).1.is_empty() && !name.contains("!apart")
    }
}

/// What the property saw, so a corpus that exercises nothing fails.
#[derive(Debug, Default)]
struct Coverage {
    patterns: usize,
    bindings: usize,
    mints: BTreeSet<String>,
    disappearances: usize,
}

/// KORE text, as a consumer receives it, and its parse.
fn reparse(label: &str, printed: &kore::Pattern) -> (String, kore::Pattern) {
    let text = Printer::compact().print_pattern(printed);
    let parsed = parse_pattern(&text)
        .unwrap_or_else(|error| panic!("{label}: {text} does not parse: {error}"));
    (text, parsed)
}

/// The printed pattern read back as a consumer reads it: verified as a standalone pattern of the
/// definition, then internalized.
fn read_back(label: &str, definition: &BackendDefinition, printed: &kore::Pattern) -> Pattern {
    definition
        .verify_standalone_pattern(printed, &[])
        .unwrap_or_else(|error| panic!("{label}: {printed:?} does not verify: {error}"))
        .internalize_pattern()
        .unwrap_or_else(|error| panic!("{label}: {printed:?} does not re-internalize: {error}"))
}

/// The printed pattern, as KORE text, reads back to the internal pattern under a renaming that
/// is a bijection and the identity on the request's names: each free variable reads back as
/// its spelling, distinct free variables have distinct spellings, the binders read back as the
/// printed binders, and printing what was read gives the same text.
fn assert_round_trips(
    label: &str,
    definition: &BackendDefinition,
    request: &Request,
    pattern: &Pattern,
) {
    if pattern.constraints.contains(&Predicate::False) {
        // A refuted pattern prints as `\bottom`, which names no variable.
        return;
    }
    let (text, printed_pattern) = reparse(label, &externalize::constrained_pattern(pattern));
    let back = read_back(label, definition, &printed_pattern);
    let free = free_variables(pattern);
    let renamed = free.iter().map(printed).collect::<BTreeSet<_>>();
    assert_eq!(
        renamed.len(),
        free.len(),
        "{label}: two free variables print alike in {text}"
    );
    assert_eq!(
        free_variables(&back),
        renamed,
        "{label}: free variables of {text}"
    );
    for variable in &free {
        if request.names.contains(variable.name.as_ref()) {
            assert_eq!(
                &printed(variable),
                variable,
                "{label}: a request name is renamed"
            );
        }
    }
    let apart = Printable::pattern(pattern);
    let printed_binders = bound_names(&apart.source())
        .iter()
        .map(|name| encode_variable_name(name))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        bound_names(&back),
        printed_binders,
        "{label}: bound names of {text}"
    );
    let (again, _) = reparse(label, &externalize::constrained_pattern(&back));
    assert_eq!(again, text, "{label}: printing what was read");
}

/// The rule binding's value re-internalizes to its variables, each read back as its spelling.
fn assert_term_round_trips(label: &str, definition: &BackendDefinition, term: &Term) {
    let (text, printed_term) = reparse(label, &externalize::term(term));
    let back = definition
        .verify_standalone_pattern(&printed_term, &[])
        .unwrap_or_else(|error| panic!("{label}: {text} does not verify: {error}"))
        .internalize_term()
        .unwrap_or_else(|error| panic!("{label}: {text} does not re-internalize: {error}"));
    let renamed = term
        .attributes()
        .variables
        .iter()
        .map(printed)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        renamed.len(),
        term.attributes().variables.len(),
        "{label}: {text}"
    );
    assert_eq!(
        back.attributes().variables.to_btree_set(),
        renamed,
        "{label}: variables of {text}"
    );
}

/// The free variables of an emitted pattern or binding follow the output contract.
fn assert_free_names(
    label: &str,
    request: &Request,
    free: &BTreeSet<Variable>,
    bound: &BTreeSet<String>,
    coverage: &mut Coverage,
) {
    for variable in free {
        let name = variable.name.to_string();
        if request.names.contains(&name) {
            assert!(
                request.free.contains(variable),
                "{label}: the free {variable:?} is named like a request variable but is not one"
            );
        } else {
            assert!(
                Request::is_rewrite_mint(&name),
                "{label}: the free {name} is neither a request variable nor a rewrite mint"
            );
            assert!(
                !request.names.contains(&encode_variable_name(&name)),
                "{label}: the mint {name} prints like a request variable"
            );
            coverage.mints.insert(name.clone());
        }
        assert!(
            !bound.contains(&name),
            "{label}: {name} is both free and bound"
        );
    }
}

/// Check every state and binding an observed execution reports, and that along each leaf's
/// path a free name that left the state never returns.
fn assert_response(
    label: &str,
    definition: &BackendDefinition,
    request: &Request,
    result: &ExecutionResult,
    coverage: &mut Coverage,
) {
    assert!(!result.leaves.is_empty(), "{label}: no leaf");
    for (index, leaf) in result.leaves.iter().enumerate() {
        let label = format!("{label} leaf {index}");
        let mut path = vec![request.initial.clone()];
        for event in &leaf.observations {
            match event {
                ObservationEvent::Transition(transition) => {
                    for (key, value) in &transition.bindings {
                        let label = format!("{label} binding {}", key.name);
                        assert_term_round_trips(&label, definition, value);
                        assert_free_names(
                            &label,
                            request,
                            &value.attributes().variables.to_btree_set(),
                            &BTreeSet::new(),
                            coverage,
                        );
                        coverage.bindings += 1;
                    }
                    path.push(transition.before.clone());
                    path.push(transition.after.clone());
                }
                ObservationEvent::Evaluation(evaluation) => {
                    path.push(evaluation.before.clone());
                    path.push(evaluation.after.clone());
                }
                ObservationEvent::Uncommitted(_) => {}
            }
        }
        path.push(leaf.pattern.clone());
        let mut seen = BTreeSet::new();
        let mut gone = BTreeSet::new();
        for (position, pattern) in path.iter().enumerate() {
            let label = format!("{label} state {position}");
            assert_round_trips(&label, definition, request, pattern);
            let free = free_variables(pattern);
            assert_free_names(&label, request, &free, &bound_names(pattern), coverage);
            let names = free
                .iter()
                .map(|variable| variable.name.to_string())
                .collect::<BTreeSet<_>>();
            for name in &names {
                assert!(
                    !gone.contains(name),
                    "{label}: {name} left the state earlier on this path and reappears"
                );
            }
            for name in seen.difference(&names) {
                if gone.insert(name.clone()) {
                    coverage.disappearances += 1;
                }
            }
            seen.extend(names);
            coverage.patterns += 1;
        }
    }
}

// ---------------------------------------------------------------------------------------
// Execution.

fn internalize(source: &str, module: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, module).expect("definition should internalize")
}

fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
    let parsed = parse_pattern(source).expect("pattern should parse");
    definition
        .verify_standalone_pattern(&parsed, &[])
        .and_then(|admitted| admitted.internalize_pattern())
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

#[cfg(feature = "z3")]
fn solver(definition: &BackendDefinition) -> Box<dyn SmtSolver> {
    Box::new(k_rust_backend::smt::Z3Solver::new(definition).expect("Z3 should start"))
}

#[cfg(not(feature = "z3"))]
fn solver(_: &BackendDefinition) -> Box<dyn SmtSolver> {
    Box::new(k_rust_backend::smt::NoSolver)
}

fn execute(definition: &BackendDefinition, initial: &Pattern, max_depth: u64) -> ExecutionResult {
    let solver = solver(definition);
    execute_observed_with_solver(
        definition,
        initial.clone(),
        ExecutionOptions {
            max_depth,
            ..ExecutionOptions::default()
        },
        solver.as_ref(),
        &ObservationOptions::all(),
    )
}

// ---------------------------------------------------------------------------------------
// Definitions.

const MAP_SELECTION: &str = r#"[]
module MAIN
    sort SortKey{} [hasDomainValues{}()]
    sort SortValue{} [hasDomainValues{}()]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    sort SortState{} []
    hooked-symbol mapUnit{}() : SortMap{}
        [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortKey{}, SortValue{}) : SortMap{}
        [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    symbol mapState{}(SortMap{}) : SortState{} [constructor{}()]
    symbol mapPicked{}(SortKey{}, SortValue{}, SortMap{}) : SortState{} [constructor{}()]
    axiom{} \rewrites{SortState{}}(
        \and{SortState{}}(
            mapState{}(mapConcat{}(mapItem{}(KEY:SortKey{}, VALUE:SortValue{}), REST:SortMap{})),
            \top{SortState{}}()
        ),
        mapPicked{}(KEY:SortKey{}, VALUE:SortValue{}, REST:SortMap{})
    ) [label{}("map-select")]
endmodule []"#;

/// Two known entries and a symbolic frame named `frame`.
fn map_state(frame: &str) -> String {
    format!(
        r#"mapState{{}}(mapConcat{{}}(mapConcat{{}}(
            mapItem{{}}(\dv{{SortKey{{}}}}("first"), \dv{{SortValue{{}}}}("v1")),
            mapItem{{}}(\dv{{SortKey{{}}}}("second"), \dv{{SortValue{{}}}}("v2"))), {frame}:SortMap{{}}))"#
    )
}

/// The conflate3 shape: `new1` and `new2` each create a box `?B` that `go1`/`go` narrow to
/// `c(VarI1)`/`c(VarI)`; `burnNew` creates and narrows a box `c(VarZ)` that is dropped.
const CONFLATE3: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    sort SortBox{} []
    sort SortOp{} []
    sort SortProg{} []
    hooked-symbol le{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.le"), smt-hook{}("<=")]
    hooked-symbol gt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    symbol c{}(SortInt{}) : SortBox{} [constructor{}(), functional{}(), injective{}()]
    symbol new1{}() : SortOp{} [constructor{}(), functional{}()]
    symbol burnNew{}() : SortOp{} [constructor{}(), functional{}()]
    symbol new2{}() : SortOp{} [constructor{}(), functional{}()]
    symbol go1{}(SortBox{}) : SortOp{} [constructor{}(), functional{}(), injective{}()]
    symbol burn{}(SortBox{}) : SortOp{} [constructor{}(), functional{}(), injective{}()]
    symbol go{}(SortBox{}) : SortOp{} [constructor{}(), functional{}(), injective{}()]
    symbol t1{}(SortInt{}) : SortOp{} [constructor{}(), functional{}(), injective{}()]
    symbol t{}(SortInt{}) : SortOp{} [constructor{}(), functional{}(), injective{}()]
    symbol done{}() : SortProg{} [constructor{}(), functional{}()]
    symbol fail{}() : SortProg{} [constructor{}(), functional{}()]
    symbol fail2{}() : SortProg{} [constructor{}(), functional{}()]
    symbol seq{}(SortOp{}, SortProg{}) : SortProg{} [constructor{}(), functional{}(), injective{}()]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(new1{}(), VarP:SortProg{}), \top{SortProg{}}()),
        \exists{SortProg{}}(Var'Ques'B:SortBox{}, seq{}(go1{}(Var'Ques'B:SortBox{}), VarP:SortProg{}))
    ) [label{}("new1")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(go1{}(c{}(VarI1:SortInt{})), VarP:SortProg{}), \top{SortProg{}}()),
        seq{}(t1{}(VarI1:SortInt{}), VarP:SortProg{})
    ) [label{}("go1")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(t1{}(VarJ:SortInt{}), VarP:SortProg{}),
            \equals{SortBool{}, SortProg{}}(le{}(VarJ:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
        VarP:SortProg{}
    ) [label{}("t1Pos")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(t1{}(VarJ:SortInt{}), VarP:SortProg{}),
            \equals{SortBool{}, SortProg{}}(gt{}(VarJ:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
        fail{}()
    ) [label{}("t1Neg")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(burnNew{}(), VarP:SortProg{}), \top{SortProg{}}()),
        \exists{SortProg{}}(Var'Ques'B:SortBox{}, seq{}(burn{}(Var'Ques'B:SortBox{}), VarP:SortProg{}))
    ) [label{}("burnNew")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(burn{}(c{}(VarZ:SortInt{})), VarP:SortProg{}), \top{SortProg{}}()),
        VarP:SortProg{}
    ) [label{}("burn")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(new2{}(), VarP:SortProg{}), \top{SortProg{}}()),
        \exists{SortProg{}}(Var'Ques'B:SortBox{}, seq{}(go{}(Var'Ques'B:SortBox{}), VarP:SortProg{}))
    ) [label{}("new2")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(go{}(c{}(VarI:SortInt{})), VarP:SortProg{}), \top{SortProg{}}()),
        seq{}(t{}(VarI:SortInt{}), VarP:SortProg{})
    ) [label{}("go")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(t{}(VarJ:SortInt{}), VarP:SortProg{}),
            \equals{SortBool{}, SortProg{}}(gt{}(VarJ:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
        done{}()
    ) [label{}("tPos")]
    axiom{} \rewrites{SortProg{}}(
        \and{SortProg{}}(seq{}(t{}(VarJ:SortInt{}), VarP:SortProg{}),
            \equals{SortBool{}, SortProg{}}(le{}(VarJ:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true"))),
        fail2{}()
    ) [label{}("tNeg")]
endmodule []"#;

/// `new1; burnNew` `burns` times`; new2; done`.
fn conflate3_program(burns: usize) -> String {
    let mut program = "seq{}(new2{}(), done{}())".to_owned();
    for _ in 0..burns {
        program = format!("seq{{}}(burnNew{{}}(), {program})");
    }
    format!("seq{{}}(new1{{}}(), {program})")
}

/// Rules whose right-hand sides introduce variables: an existential, a rule variable the
/// left-hand side does not bind, and a function whose equation is total over a constructor
/// argument.
const INTRODUCTIONS: &str = r#"[]
module MAIN
    sort SortS{} []
    symbol a{}() : SortS{} [constructor{}(), functional{}()]
    symbol b{}() : SortS{} [constructor{}(), functional{}()]
    symbol wrap{}(SortS{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol pair{}(SortS{}, SortS{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol d{}() : SortS{} [constructor{}(), functional{}()]
    symbol state{}(SortS{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol hold{}(SortS{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol swap{}(SortS{}) : SortS{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X:SortS{}, pair{}(Y:SortS{}, Z:SortS{})), \top{R}())),
        \equals{SortS{}, R}(swap{}(X:SortS{}), \and{SortS{}}(pair{}(Z:SortS{}, Y:SortS{}), \top{SortS{}}()))
    ) [label{}("swap-pair")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
        \exists{SortS{}}(Y:SortS{}, hold{}(pair{}(X:SortS{}, Y:SortS{})))
    ) [label{}("existential")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(hold{}(pair{}(X:SortS{}, Y:SortS{})), \top{SortS{}}()),
        state{}(swap{}(pair{}(X:SortS{}, Y:SortS{})))
    ) [label{}("swap")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(state{}(pair{}(X:SortS{}, Y:SortS{})), \top{SortS{}}()), d{}()
    ) [label{}("release")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(d{}(), \top{SortS{}}()), wrap{}(X:SortS{})
    ) [label{}("introduce")]
endmodule []"#;

// ---------------------------------------------------------------------------------------
// (a)

/// (a) With the initial frame spelled `ExFrame0`, map selection's narrowed frame (a rewrite
/// mint) is printed apart from it, every leaf round-trips at the level of names, and no free
/// variable other than the request's frame is named or spelled `ExFrame0`.
#[cfg(feature = "z3")]
#[test]
fn map_selection_keeps_the_initial_frame_apart_from_the_narrowed_frame() {
    let definition = internalize(MAP_SELECTION, "MAIN");
    let initial = pattern(&definition, &map_state("ExFrame0"));
    let request = Request::new(initial.clone());
    let frame = request
        .free
        .iter()
        .find(|variable| variable.name.as_ref() == "ExFrame0")
        .expect("the request's frame")
        .clone();
    let result = execute(&definition, &initial, 1);
    let mut coverage = Coverage::default();
    assert_response(
        "map selection",
        &definition,
        &request,
        &result,
        &mut coverage,
    );
    let mut selected = 0;
    for (index, leaf) in result.leaves.iter().enumerate() {
        for variable in free_variables(&leaf.pattern) {
            if variable.name.as_ref() == "ExFrame0" {
                assert_eq!(variable, frame, "leaf {index}");
            }
            assert!(
                variable == frame || encode_variable_name(&variable.name) != "ExFrame0",
                "leaf {index}: {variable:?} prints as the request's frame"
            );
        }
        let mut spellings = BTreeSet::new();
        printed_names(
            &externalize::constrained_pattern(&leaf.pattern),
            &mut spellings,
        );
        let frames = spellings
            .iter()
            .filter(|(spelling, _)| spelling == "ExFrame0")
            .count();
        assert!(frames <= 1, "leaf {index}: {spellings:?}");
        if leaf.depth == 1 {
            selected += 1;
        }
    }
    assert!(selected > 0, "map selection applies: {result:#?}");
    assert!(
        coverage.mints.iter().any(|name| name.starts_with("Ex#")),
        "the narrowing minted a frame: {coverage:?}"
    );
}

// ---------------------------------------------------------------------------------------
// (b)

/// One request of the corpus.
struct Case {
    label: &'static str,
    definition: fn() -> BackendDefinition,
    initial: String,
    max_depth: u64,
}

fn corpus() -> Vec<Case> {
    let map_selection = || internalize(MAP_SELECTION, "MAIN");
    let conflate3 = || internalize(CONFLATE3, "MAIN");
    let introductions = || internalize(INTRODUCTIONS, "MAIN");
    let rewrite_coverage = || {
        internalize(
            include_str!("../fixtures/rewrite-coverage.kore"),
            "REWRITE-COVERAGE",
        )
    };
    let cell_map_coverage = || {
        internalize(
            include_str!("../fixtures/cell-map-coverage.kore"),
            "CELL-MAP-COVERAGE",
        )
    };
    let k_growth = || internalize(include_str!("../fixtures/k-growth.kore"), "MAIN");
    vec![
        Case {
            label: "rewrite-coverage fixture, symbolic box",
            definition: rewrite_coverage,
            initial: "state{}(box{}(E:SortS{}))".to_owned(),
            max_depth: 3,
        },
        Case {
            label: "rewrite-coverage fixture, symbolic state",
            definition: rewrite_coverage,
            initial: "state{}(X:SortS{})".to_owned(),
            max_depth: 3,
        },
        Case {
            label: "cell-map-coverage fixture, symbolic frame",
            definition: cell_map_coverage,
            initial: r#"cellState{}(mapConcat{}(
                mapItem{}(\dv{SortKey{}}("first"), thread{}(\dv{SortKey{}}("first"),
                    kseq{}(inj{SortExp{}, SortKItem{}}(heat{}(expA{}(), expB{}())), dotk{}()))),
                FRAME:SortThreadMap{}))"#
                .to_owned(),
            max_depth: 2,
        },
        Case {
            label: "k-growth fixture, symbolic head",
            definition: k_growth,
            initial: "k{}(kseq{}(head{}(N:SortInt{}), dotk{}()))".to_owned(),
            max_depth: 4,
        },
        Case {
            label: "map selection, frame ExFrame0",
            definition: map_selection,
            initial: map_state("ExFrame0"),
            max_depth: 2,
        },
        Case {
            label: "map selection, frame REST",
            definition: map_selection,
            initial: map_state("REST"),
            max_depth: 2,
        },
        Case {
            label: "map selection, frame spelled as the first frame mint",
            definition: map_selection,
            initial: map_state("Ex-hFrame-b0"),
            max_depth: 2,
        },
        Case {
            label: "conflate3, 8 burns",
            definition: conflate3,
            initial: conflate3_program(8),
            max_depth: 40,
        },
        Case {
            label: "conflate3, 9 burns",
            definition: conflate3,
            initial: conflate3_program(9),
            max_depth: 40,
        },
        Case {
            label: "introductions from a ground state",
            definition: introductions,
            initial: "wrap{}(a{}())".to_owned(),
            max_depth: 12,
        },
        Case {
            label: "introductions from a symbolic state",
            definition: introductions,
            initial: "wrap{}(X:SortS{})".to_owned(),
            max_depth: 12,
        },
        Case {
            label: "introductions from a state spelled with mints",
            definition: introductions,
            initial: r#"\and{SortS{}}(wrap{}(Ex-hY-b0:SortS{}),
                \equals{SortS{}, SortS{}}(Ex-hX-b3:SortS{}, Ex-hX-b3:SortS{}))"#
                .to_owned(),
            max_depth: 12,
        },
        Case {
            label: "introductions from a state with a bound mint spelling",
            definition: introductions,
            initial: r#"\and{SortS{}}(wrap{}(X:SortS{}),
                \exists{SortS{}}(Ex-hY-b0:SortS{}, \equals{SortS{}, SortS{}}(Ex-hY-b0:SortS{}, X:SortS{})))"#
                .to_owned(),
            max_depth: 12,
        },
    ]
}

/// (b) Over the corpus, every emitted state and binding round-trips at the level of names, no
/// free variable that is not the request's carries a request name or prints like one, no name
/// is both free and bound, every free non-request name is a rewrite mint, and along
/// each path a name that left the state never reappears. An identical request gets an identical
/// response, names included.
#[test]
fn every_emitted_name_follows_the_output_contract() {
    let mut coverage = Coverage::default();
    for case in corpus() {
        let definition = (case.definition)();
        let initial = pattern(&definition, &case.initial);
        let request = Request::new(initial.clone());
        let result = execute(&definition, &initial, case.max_depth);
        assert_response(case.label, &definition, &request, &result, &mut coverage);
        assert_eq!(
            result,
            execute(&definition, &initial, case.max_depth),
            "{}: an identical request",
            case.label
        );
    }
    assert!(
        coverage.patterns > 0 && coverage.bindings > 0,
        "{coverage:?}"
    );
    assert!(
        !coverage.mints.is_empty() && coverage.disappearances > 0,
        "the corpus mints and drops names: {coverage:?}"
    );
}

// ---------------------------------------------------------------------------------------
// (c)

/// (c) The rule variables `VarI1` and `VarI` are narrowed apart by nine burns: every internal
/// name the execution emits prints as its own spelling. Under Z3 both narrowings run, and the
/// mints of `VarI1` and of `VarI` are distinct names with distinct spellings (before the
/// injective printer, `Ex#VarI1!0` and `Ex#VarI!10` both printed `ExVarI10`).
#[test]
fn narrowed_rule_variables_print_distinctly() {
    let definition = internalize(CONFLATE3, "MAIN");
    let initial = pattern(&definition, &conflate3_program(9));
    let request = Request::new(initial.clone());
    let result = execute(&definition, &initial, 40);
    let mut coverage = Coverage::default();
    assert_response("conflate3", &definition, &request, &result, &mut coverage);
    let mut spellings = BTreeMap::<String, BTreeSet<String>>::new();
    for name in &coverage.mints {
        spellings
            .entry(encode_variable_name(name))
            .or_default()
            .insert(name.clone());
    }
    for (spelling, names) in &spellings {
        assert_eq!(names.len(), 1, "{spelling} prints {names:?}");
    }
    let minted = |base: &str| {
        coverage
            .mints
            .iter()
            .filter(|name| split_fresh_counter(name).0 == base)
            .cloned()
            .collect::<BTreeSet<_>>()
    };
    let first = minted("Ex#VarI1");
    let second = minted("Ex#VarI");
    // Without a solver the narrowing of `go1` is indeterminate and neither rule variable is
    // minted; the name checks above still hold for what the execution emits.
    if cfg!(feature = "z3") {
        assert!(!first.is_empty(), "go1 narrows c(VarI1): {coverage:?}");
        assert!(!second.is_empty(), "go narrows c(VarI): {coverage:?}");
    }
    for one in &first {
        for other in &second {
            assert_ne!(encode_variable_name(one), encode_variable_name(other));
        }
    }
}
