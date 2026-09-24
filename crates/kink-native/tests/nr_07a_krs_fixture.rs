//! NR-07A fixture-only qualification across the KRS and k-rust boundary.
//!
//! This ignored gate consumes KORE compiled in a separate KRS process graph.
//! `kink-native` therefore retains its exact no-Z3 feature profile.

use std::{fs, path::PathBuf, thread};

use k_rust::{
    backend::{Backend, BackendOptions, SearchRequest},
    kore::{
        ast::{Attributes, Pattern, Sentence, Sort, Symbol, Variable, VariableKind},
        json as kore_json,
        parser::parse_definition,
    },
};
use kink_native::{
    ProvenanceStatus,
    observation::{InstalledObservationManifest, NativeEvent, RuleObservationSpec},
    search::{PositiveBoundedOutcome, ReplaySearch, SearchAdapter, SolverProfile, compare_replay},
};

const MODULE: &str = "EXPR";
const RULE_LABEL: &str = "EXPR.expr.and-true";
const AND_SYMBOL: &str = "LblLblAnd";
const INJECTION_SYMBOL: &str = "inj";
const BOOL_SORT: &str = "SortBool";
const EXPR_SORT: &str = "SortExpr";
const INT_SORT: &str = "SortInt";
const K_SORT: &str = "SortK";
const K_ITEM_SORT: &str = "SortKItem";
const STATE_SORT: &str = "SortGeneratedTopCell";
const GENERATED_COUNTER_SORT: &str = "SortGeneratedCounterCell";

struct RuleFixture {
    identity: String,
    initial_state: serde_json::Value,
    final_state: serde_json::Value,
    binding_variable: serde_json::Value,
    semantic_value: serde_json::Value,
}

#[test]
#[ignore = "run through draft/tasks/rust-upfront/verify-nr-07a.sh"]
fn krs_definition_ir_reaches_positive_observed_state_and_path() {
    thread::Builder::new()
        .name("nr-07a-krs-fixture".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(run_gate)
        .expect("NR-07A gate thread must start")
        .join()
        .expect("NR-07A gate thread must not panic");
}

fn run_gate() {
    let definition_source = fs::read_to_string(required_path("NR_07A_COMPILED_KORE"))
        .expect("the isolated KRS compiler must publish one readable KORE fixture");
    let definition = parse_definition(&definition_source)
        .expect("the pinned k-rust parser must accept KRS KORE");
    let fixture = selected_rule_fixture(&definition.modules, RULE_LABEL);
    drop(definition);

    let manifest = InstalledObservationManifest::install(vec![RuleObservationSpec {
        label: RULE_LABEL.into(),
        backend_rule_identity: fixture.identity.clone(),
        emit_rule_applied: true,
        domain_events: Vec::new(),
    }])
    .expect("the one-rule observation manifest must install atomically");

    let state_first =
        run_state_search(&definition_source, &manifest, fixture.initial_state.clone());
    assert_eq!(
        state_first.outcome,
        PositiveBoundedOutcome::Positive,
        "the exact positive state search must retain a witness: {state_first:#?}"
    );
    assert_eq!(state_first.states.len(), 1);
    assert!(state_first.effects.is_empty());
    assert!(state_first.incomplete.is_empty());
    assert_no_authority(state_first.authority);
    let state_branch = state_first.states[0].clone();
    assert_branch(&state_branch, &fixture);

    let state_second =
        run_state_search(&definition_source, &manifest, fixture.initial_state.clone());
    compare_replay(
        &ReplaySearch::State(state_first),
        &ReplaySearch::State(state_second),
    )
    .expect("fresh state search must replay exactly");

    let path_first = run_path_search(&definition_source, &manifest, fixture.initial_state.clone());
    assert_eq!(
        path_first.outcome,
        PositiveBoundedOutcome::Positive,
        "the exact positive path search must retain a witness: {path_first:#?}"
    );
    assert_eq!(
        path_first.witnesses.as_slice(),
        std::slice::from_ref(&state_branch)
    );
    assert!(path_first.effects.is_empty());
    assert!(path_first.incomplete.is_empty());
    assert_no_authority(path_first.authority);

    let path_second = run_path_search(&definition_source, &manifest, fixture.initial_state);
    compare_replay(
        &ReplaySearch::Path(path_first),
        &ReplaySearch::Path(path_second),
    )
    .expect("fresh path search must replay exactly");
}

fn required_path(name: &str) -> PathBuf {
    PathBuf::from(
        std::env::var_os(name).unwrap_or_else(|| panic!("{name} must be set by the gate")),
    )
}

fn attribute_string<'a>(attributes: &'a Attributes, name: &str) -> Option<&'a str> {
    attributes.0.iter().find_map(|attribute| {
        let Pattern::Application { symbol, arguments } = attribute else {
            return None;
        };
        let [Pattern::String(value)] = arguments.as_slice() else {
            return None;
        };
        (symbol.name == name)
            .then(|| value.as_utf8().ok())
            .flatten()
    })
}

fn selected_rule_fixture(modules: &[k_rust::kore::ast::Module], label: &str) -> RuleFixture {
    let selected = modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| {
            let Sentence::Axiom {
                pattern,
                attributes,
                ..
            } = sentence
            else {
                return None;
            };
            (attribute_string(attributes, "label") == Some(label)).then(|| {
                let identity = attribute_string(attributes, "UNIQUE'Unds'ID")
                    .expect("the selected executable rule must have a unique identity");
                (identity.to_owned(), pattern.as_ref())
            })
        })
        .collect::<Vec<_>>();
    let [(identity, pattern)] = selected.as_slice() else {
        panic!(
            "expected one compiled rule labelled {label:?}, found {}",
            selected.len()
        )
    };
    let Pattern::Rewrites { left, right, .. } = pattern else {
        panic!("the selected transition must compile to one rewrites pattern")
    };
    let Pattern::And {
        arguments: left_arguments,
        ..
    } = left.as_ref()
    else {
        panic!("the selected transition left side must retain state and requires")
    };
    let Pattern::And {
        arguments: right_arguments,
        ..
    } = right.as_ref()
    else {
        panic!("the selected transition right side must retain state and ensures")
    };
    let [initial_state, requires] = left_arguments.as_slice() else {
        panic!("the selected transition must have exactly one state and requires predicate")
    };
    let [final_state, ensures] = right_arguments.as_slice() else {
        panic!("the selected transition must have exactly one state and ensures predicate")
    };
    let state_sort = application_sort(STATE_SORT);
    assert!(matches!(
        pattern,
        Pattern::Rewrites { sort, .. } if sort == &state_sort
    ));
    assert!(matches!(
        left.as_ref(),
        Pattern::And { sort, .. } if sort == &state_sort
    ));
    assert!(matches!(
        right.as_ref(),
        Pattern::And { sort, .. } if sort == &state_sort
    ));
    assert_eq!(
        requires,
        &Pattern::Top {
            sort: state_sort.clone()
        }
    );
    assert_eq!(ensures, &Pattern::Top { sort: state_sort });

    let bool_sort = application_sort(BOOL_SORT);
    let expr_sort = application_sort(EXPR_SORT);
    let k_item_sort = application_sort(K_ITEM_SORT);
    assert_declared_symbol_signature(
        modules,
        AND_SYMBOL,
        &[expr_sort.clone(), expr_sort.clone()],
        &expr_sort,
    );

    let semantic_variable = Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: "VarV62".into(),
        sort: bool_sort.clone(),
    });
    let true_value = Pattern::DomainValue {
        sort: bool_sort.clone(),
        value: "true".into(),
    };
    let false_value = Pattern::DomainValue {
        sort: bool_sort.clone(),
        value: "false".into(),
    };
    let symbolic_lhs_core = Pattern::Application {
        symbol: Symbol {
            name: AND_SYMBOL.into(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![
            injection(bool_sort.clone(), expr_sort.clone(), true_value.clone()),
            injection(
                bool_sort.clone(),
                expr_sort.clone(),
                semantic_variable.clone(),
            ),
        ],
    };
    let symbolic_rhs_core = injection(
        bool_sort.clone(),
        k_item_sort.clone(),
        semantic_variable.clone(),
    );
    assert_directed_semantics(
        initial_state,
        final_state,
        &symbolic_lhs_core,
        &symbolic_rhs_core,
    );
    assert_eq!(pattern_occurrences(initial_state, &semantic_variable), 1);
    assert_eq!(pattern_occurrences(final_state, &semantic_variable), 1);

    let (concrete_initial_state, initial_substitutions) =
        substitute_pattern(initial_state, &semantic_variable, &false_value);
    let (concrete_final_state, final_substitutions) =
        substitute_pattern(final_state, &semantic_variable, &false_value);
    assert_eq!(initial_substitutions, 1);
    assert_eq!(final_substitutions, 1);
    assert_eq!(
        pattern_occurrences(&concrete_initial_state, &semantic_variable),
        0
    );
    assert_eq!(
        pattern_occurrences(&concrete_final_state, &semantic_variable),
        0
    );

    let k_tail_variable = Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: "Var'Unds'DotVar0".into(),
        sort: application_sort(K_SORT),
    });
    let empty_k = application("dotk", Vec::new());
    let (concrete_initial_state, initial_k_tail_substitutions) =
        substitute_pattern(&concrete_initial_state, &k_tail_variable, &empty_k);
    let (concrete_final_state, final_k_tail_substitutions) =
        substitute_pattern(&concrete_final_state, &k_tail_variable, &empty_k);
    assert_eq!(initial_k_tail_substitutions, 1);
    assert_eq!(final_k_tail_substitutions, 1);

    let counter_variable = Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: "Var'Unds'DotVar1".into(),
        sort: application_sort(GENERATED_COUNTER_SORT),
    });
    let counter_cell = application(
        "Lbl'-LT-'generatedCounter'-GT-'",
        vec![Pattern::DomainValue {
            sort: application_sort(INT_SORT),
            value: "0".into(),
        }],
    );
    let (concrete_initial_state, initial_counter_substitutions) =
        substitute_pattern(&concrete_initial_state, &counter_variable, &counter_cell);
    let (concrete_final_state, final_counter_substitutions) =
        substitute_pattern(&concrete_final_state, &counter_variable, &counter_cell);
    assert_eq!(initial_counter_substitutions, 1);
    assert_eq!(final_counter_substitutions, 1);

    let concrete_lhs_core = Pattern::Application {
        symbol: Symbol {
            name: AND_SYMBOL.into(),
            sort_parameters: Vec::new(),
        },
        arguments: vec![
            injection(bool_sort.clone(), expr_sort.clone(), true_value),
            injection(bool_sort.clone(), expr_sort.clone(), false_value.clone()),
        ],
    };
    let concrete_rhs_core = injection(bool_sort, k_item_sort, false_value.clone());
    assert_directed_semantics(
        &concrete_initial_state,
        &concrete_final_state,
        &concrete_lhs_core,
        &concrete_rhs_core,
    );

    RuleFixture {
        identity: identity.clone(),
        initial_state: kore_json::to_value(&concrete_initial_state)
            .expect("the concrete compiled initial state must encode"),
        final_state: kore_json::to_value(&concrete_final_state)
            .expect("the concrete compiled final state must encode"),
        binding_variable: kore_json::to_value(&Pattern::Variable(Variable {
            kind: VariableKind::Element,
            name: "Rule#VarV62".into(),
            sort: application_sort(BOOL_SORT),
        }))
        .expect("the independently constructed normalized binding variable must encode"),
        semantic_value: kore_json::to_value(&false_value)
            .expect("the independently constructed semantic value must encode"),
    }
}

fn application_sort(name: &str) -> Sort {
    Sort::Application {
        name: name.into(),
        arguments: Vec::new(),
    }
}

fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.into(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

fn assert_declared_symbol_signature(
    modules: &[k_rust::kore::ast::Module],
    name: &str,
    expected_argument_sorts: &[Sort],
    expected_result_sort: &Sort,
) {
    let declarations = modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| {
            let Sentence::SymbolDeclaration {
                symbol,
                argument_sorts,
                result_sort,
                ..
            } = sentence
            else {
                return None;
            };
            (symbol.name == name).then_some((symbol, argument_sorts, result_sort))
        })
        .collect::<Vec<_>>();
    let [(symbol, argument_sorts, result_sort)] = declarations.as_slice() else {
        panic!(
            "expected one declaration for semantic symbol {name:?}, found {}",
            declarations.len()
        )
    };
    assert!(symbol.sort_parameters.is_empty());
    assert_eq!(argument_sorts.as_slice(), expected_argument_sorts);
    assert_eq!(*result_sort, expected_result_sort);
}

fn injection(from_sort: Sort, to_sort: Sort, argument: Pattern) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: INJECTION_SYMBOL.into(),
            sort_parameters: vec![from_sort, to_sort],
        },
        arguments: vec![argument],
    }
}

fn assert_directed_semantics(
    initial_state: &Pattern,
    final_state: &Pattern,
    expected_lhs_core: &Pattern,
    expected_rhs_core: &Pattern,
) {
    assert_ne!(expected_lhs_core, expected_rhs_core);
    assert_eq!(pattern_occurrences(initial_state, expected_lhs_core), 1);
    assert_eq!(pattern_occurrences(initial_state, expected_rhs_core), 0);
    assert_eq!(pattern_occurrences(final_state, expected_lhs_core), 0);
    assert_eq!(pattern_occurrences(final_state, expected_rhs_core), 1);
}

fn substitute_pattern(
    pattern: &Pattern,
    expected: &Pattern,
    replacement: &Pattern,
) -> (Pattern, usize) {
    let mut substituted = pattern.clone();
    let substitutions = substitute_pattern_in_place(&mut substituted, expected, replacement);
    (substituted, substitutions)
}

fn substitute_pattern_in_place(
    pattern: &mut Pattern,
    expected: &Pattern,
    replacement: &Pattern,
) -> usize {
    if pattern == expected {
        *pattern = replacement.clone();
        return 1;
    }
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments
            .iter_mut()
            .map(|argument| substitute_pattern_in_place(argument, expected, replacement))
            .sum(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => {
            substitute_pattern_in_place(argument, expected, replacement)
        }
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            substitute_pattern_in_place(left, expected, replacement)
                + substitute_pattern_in_place(right, expected, replacement)
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => 0,
    }
}

fn pattern_occurrences(pattern: &Pattern, expected: &Pattern) -> usize {
    let here = usize::from(pattern == expected);
    let children = match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => arguments
            .iter()
            .map(|argument| pattern_occurrences(argument, expected))
            .sum(),
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Exists { body: argument, .. }
        | Pattern::Forall { body: argument, .. }
        | Pattern::Mu { body: argument, .. }
        | Pattern::Nu { body: argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => pattern_occurrences(argument, expected),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            pattern_occurrences(left, expected) + pattern_occurrences(right, expected)
        }
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => 0,
    };
    here + children
}

fn run_state_search(
    definition: &str,
    manifest: &InstalledObservationManifest,
    state: serde_json::Value,
) -> kink_native::search::AdaptedStateSearch {
    let mut backend = Backend::new(definition, MODULE, BackendOptions::default())
        .expect("the no-Z3 backend must load the KRS fixture");
    SearchAdapter::new(SolverProfile::StructuredNoZ3Inference, manifest.clone())
        .expect("the exact no-Z3 profile must be accepted")
        .search(
            &mut backend,
            SearchRequest {
                state,
                ..SearchRequest::default()
            },
        )
        .expect("observed state search must succeed")
}

fn run_path_search(
    definition: &str,
    manifest: &InstalledObservationManifest,
    state: serde_json::Value,
) -> kink_native::search::AdaptedPathSearch {
    let mut backend = Backend::new(definition, MODULE, BackendOptions::default())
        .expect("the no-Z3 backend must load the KRS fixture");
    SearchAdapter::new(SolverProfile::StructuredNoZ3Inference, manifest.clone())
        .expect("the exact no-Z3 profile must be accepted")
        .search_paths(
            &mut backend,
            SearchRequest {
                state,
                ..SearchRequest::default()
            },
        )
        .expect("observed path search must succeed")
}

fn assert_branch(branch: &kink_native::observation::AdaptedBranch, fixture: &RuleFixture) {
    assert_eq!(branch.depth, 1);
    assert_eq!(branch.state, fixture.final_state);
    assert_eq!(branch.identity.len(), 1);
    assert_eq!(branch.identity[0].rule, fixture.identity);
    assert_eq!(branch.events.len(), 1);
    assert!(branch.rollbacks.is_empty());
    let NativeEvent::RuleApplied(event) = &branch.events[0] else {
        panic!("the fixture emits only the generic ordered RuleApplied event")
    };
    assert_eq!(event.event_ordinal, 0);
    assert_eq!(event.transition_ordinal, 0);
    assert_eq!(event.emission_ordinal, 0);
    assert_eq!(event.transition, branch.identity[0]);
    assert_eq!(event.rule_label, RULE_LABEL);
    assert_eq!(
        event
            .bindings
            .iter()
            .filter(|binding| {
                binding.variable.eq(&fixture.binding_variable)
                    && binding.value.eq(&fixture.semantic_value)
            })
            .count(),
        1,
        "the ordered observation bindings must contain normalized Rule#VarV62 -> false exactly once: {:#?}",
        event.bindings
    );
    assert!(event.introduced_predicates.is_empty());
    assert!(event.effects.is_empty());
    assert_eq!(event.before, fixture.initial_state);
    assert_eq!(event.after, fixture.final_state);
    assert_eq!(event.provenance, ProvenanceStatus::SidecarOnlyMissingBridge);
}

fn assert_no_authority(authority: kink_native::search::AdapterAuthority) {
    assert_eq!(
        authority.provenance(),
        ProvenanceStatus::SidecarOnlyMissingBridge
    );
    assert!(!authority.grants_native_authority());
    assert!(!authority.proves_exhaustive_absence());
    assert!(!authority.has_production_receipt());
}
