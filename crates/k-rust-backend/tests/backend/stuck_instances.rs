//! Bounded ground-instance oracle for symbolic `Stuck` leaves.

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{
        ExecutionMode, ExecutionOptions, HaltReason, Pattern, execute_with_solver,
        substitute_predicates,
    },
    search::ResultModality,
    simplify::{SimplificationOptions, simplify_predicates_with_solver},
    smt::{NoSolver, SmtSolver},
    substitution::{Substitution, substitute},
    term::{Sort, Term, Variable},
};
use k_rust_kore::kore::parser::parse_definition;

#[cfg(feature = "z3")]
use k_rust_backend::rewrite::TraceKind;

use crate::support::internal_term;

const DEFINITION: &str = r#"[]
module STUCK-INSTANCES
    sort SortNat{} []
    sort SortW{} []
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    symbol z{}() : SortNat{} [constructor{}(), total{}()]
    symbol s{}(SortNat{}) : SortNat{} [constructor{}(), total{}()]
    symbol other{}() : SortNat{} [constructor{}(), total{}()]
    symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), total{}(), injective{}()]
    symbol done{}() : SortW{} [constructor{}(), total{}()]
    symbol idle{}() : SortW{} [constructor{}(), total{}()]
    symbol pair{}(SortNat{}, SortNat{}) : SortW{} [constructor{}(), total{}()]
    symbol sealed{}(SortNat{}) : SortW{} [constructor{}(), total{}()]
    symbol markInt{}(SortInt{}) : SortW{} [constructor{}(), total{}()]
    symbol markBool{}(SortBool{}) : SortW{} [constructor{}(), total{}()]
    symbol f{}(SortNat{}) : SortW{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortNat{},R}(X0:SortNat{}, s{}(z{}())), \top{R}())),
        \equals{SortW{},R}(wrap{}(X0:SortNat{}), \and{SortW{}}(wrap{}(z{}()), \top{SortW{}}()))
    ) [anywhere{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortNat{},R}(X0:SortNat{}, other{}()), \top{R}())),
        \equals{SortW{},R}(wrap{}(X0:SortNat{}), \and{SortW{}}(idle{}(), \top{SortW{}}()))
    ) [anywhere{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortNat{},R}(X0:SortNat{}, z{}()), \top{R}())),
        \equals{SortW{},R}(f{}(X0:SortNat{}), \and{SortW{}}(idle{}(), \top{SortW{}}()))
    ) []
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(wrap{}(z{}()), \top{SortW{}}()), done{}()) [label{}("finish")]
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(idle{}(), \top{SortW{}}()), done{}()) [label{}("after-head-change"), priority{}("50")]
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(pair{}(N:SortNat{}, N:SortNat{}), \top{SortW{}}()), done{}()) [label{}("repeat"), priority{}("40")]
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(pair{}(z{}(), N:SortNat{}), \top{SortW{}}()), idle{}()) [label{}("fallback"), owise{}()]
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(markInt{}(\dv{SortInt{}}("1")), \top{SortW{}}()), done{}()) [label{}("integer")]
    axiom{} \rewrites{SortW{}}(\and{SortW{}}(markBool{}(\dv{SortBool{}}("true")), \top{SortW{}}()), done{}()) [label{}("boolean")]
endmodule []"#;

fn definition(repeated_rule_priority: u8) -> BackendDefinition {
    let source = DEFINITION.replace(
        "[label{}(\"repeat\"), priority{}(\"40\")]",
        &format!("[label{{}}(\"repeat\"), priority{{}}(\"{repeated_rule_priority}\")]"),
    );
    BackendDefinition::internalize(&parse_definition(&source).unwrap(), "STUCK-INSTANCES").unwrap()
}

fn options(max_depth: u64) -> ExecutionOptions {
    ExecutionOptions {
        max_depth,
        mode: ExecutionMode::All,
        result_modality: ResultModality::PathSet,
        ..ExecutionOptions::default()
    }
}

fn ground_terms(definition: &BackendDefinition, variable: &Variable) -> Vec<Term> {
    let Sort::Application { name, arguments } = &variable.sort else {
        panic!("unexpected sort variable: {:?}", variable.sort);
    };
    assert!(arguments.is_empty());
    let naturals = || {
        let mut level = vec!["z{}()".to_owned(), "other{}()".to_owned()];
        let mut all = level.clone();
        for _ in 0..3 {
            level = level
                .into_iter()
                .map(|term| format!("s{{}}({term})"))
                .collect();
            all.extend(level.iter().cloned());
        }
        all
    };
    let terms: Vec<String> = match name.as_ref() {
        "SortNat" => naturals(),
        "SortInt" => (-2..=2)
            .map(|n| format!(r#"\dv{{SortInt{{}}}}("{n}")"#))
            .collect(),
        "SortBool" => vec![
            r#"\dv{SortBool{}}("false")"#.into(),
            r#"\dv{SortBool{}}("true")"#.into(),
        ],
        "SortFlag" => vec!["yes{}()".into(), "no{}()".into()],
        "SortW" => {
            let mut all = vec!["done{}()".to_owned(), "idle{}()".to_owned()];
            let naturals = naturals();
            all.extend(naturals.iter().map(|term| format!("wrap{{}}({term})")));
            all.extend(naturals.iter().map(|term| format!("f{{}}({term})")));
            all.extend(naturals.iter().map(|term| format!("sealed{{}}({term})")));
            all.extend((-2..=2).map(|n| format!(r#"markInt{{}}(\dv{{SortInt{{}}}}("{n}"))"#)));
            all.extend(
                ["false", "true"]
                    .map(|value| format!(r#"markBool{{}}(\dv{{SortBool{{}}}}("{value}"))"#)),
            );
            for left in &naturals {
                for right in &naturals {
                    all.push(format!("pair{{}}({left}, {right})"));
                }
            }
            all
        }
        sort => panic!("unexpected generated sort {sort}"),
    };
    terms
        .iter()
        .map(|term| internal_term(definition, term))
        .collect()
}

fn visit_instances(
    definition: &BackendDefinition,
    leaf: &Pattern,
    solver: &dyn SmtSolver,
    variables: &[Variable],
    substitution: &mut Substitution,
    checked: &mut usize,
    case: &str,
) {
    if let Some((variable, remaining)) = variables.split_first() {
        for term in ground_terms(definition, variable) {
            substitution.insert(variable.clone(), term);
            visit_instances(
                definition,
                leaf,
                solver,
                remaining,
                substitution,
                checked,
                case,
            );
        }
        substitution.remove(variable);
        return;
    }
    let constraints = substitute_predicates(&leaf.constraints, substitution);
    let simplified = simplify_predicates_with_solver(
        definition,
        &constraints,
        &[],
        SimplificationOptions::default(),
        solver,
    )
    .unwrap();
    if !simplified.is_empty()
        && !simplified
            .iter()
            .all(|predicate| matches!(predicate, k_rust_backend::rule::Predicate::True))
    {
        return;
    }
    let instance = substitute(&leaf.term, substitution);
    let result = execute_with_solver(
        definition,
        Pattern {
            term: instance.clone(),
            constraints: Vec::new(),
        },
        options(1),
        solver,
    );
    *checked += 1;
    assert!(
        matches!(result.leaves.as_slice(), [only] if only.depth == 0 && only.halt_reason == HaltReason::Stuck),
        "Stuck counterexample in {case}: leaf={leaf:?}, substitution={substitution:?}, instance={instance:?}, concrete={result:?}"
    );
}

fn check_profile(name: &str, definition: &BackendDefinition, solver: &dyn SmtSolver) {
    let templates = [
        "wrap{}(s{}(X:SortNat{}))",
        "wrap{}(X:SortNat{})",
        "W:SortW{}",
        "f{}(X:SortNat{})",
        "pair{}(X:SortNat{}, Y:SortNat{})",
        "pair{}(other{}(), Y:SortNat{})",
        "markInt{}(I:SortInt{})",
        "markBool{}(B:SortBool{})",
        "wrap{}(other{}())",
        "pair{}(other{}(), z{}())",
        "sealed{}(X:SortNat{})",
    ];
    // A fixed xorshift permutation varies the order while keeping every failure reproducible.
    let mut seed = 0x5520_2609u64;
    let mut order: Vec<usize> = (0..templates.len()).collect();
    for index in (1..order.len()).rev() {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        order.swap(index, (seed as usize) % (index + 1));
    }
    let mut stuck_leaves = 0;
    let mut symbolic_stuck_leaves = 0;
    let mut checked = 0;
    let mut checked_symbolic = 0;
    for index in order {
        let case = templates[index];
        let symbolic = Pattern {
            term: internal_term(definition, case),
            constraints: Vec::new(),
        };
        let result = execute_with_solver(definition, symbolic, options(u64::MAX), solver);
        for leaf in result
            .leaves
            .iter()
            .filter(|leaf| leaf.halt_reason == HaltReason::Stuck)
        {
            stuck_leaves += 1;
            let variables: Vec<_> = leaf
                .pattern
                .term
                .attributes()
                .variables
                .iter()
                .cloned()
                .chain(
                    leaf.pattern
                        .constraints
                        .iter()
                        .flat_map(|predicate| predicate.free_variables()),
                )
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            if !variables.is_empty() {
                symbolic_stuck_leaves += 1;
            }
            let before = checked;
            visit_instances(
                definition,
                &leaf.pattern,
                solver,
                &variables,
                &mut Substitution::new(),
                &mut checked,
                case,
            );
            if !variables.is_empty() {
                checked_symbolic += checked - before;
            }
        }
    }
    assert!(
        stuck_leaves > 0,
        "{name}: oracle needs a symbolic Stuck leaf"
    );
    assert!(
        symbolic_stuck_leaves > 0,
        "{name}: oracle needs a Stuck leaf with a free variable"
    );
    assert!(
        checked > 0,
        "{name}: oracle needs a feasible ground instance"
    );
    assert!(
        checked_symbolic > 0,
        "{name}: oracle needs a feasible symbolic Stuck instance"
    );
}

#[test]
fn symbolic_stuck_ground_instances_no_solver() {
    for priority in [40, 60] {
        let definition = definition(priority);
        check_profile("NoSolver", &definition, &NoSolver);
    }
}

#[cfg(feature = "z3")]
#[test]
fn symbolic_stuck_ground_instances_z3() {
    for priority in [40, 60] {
        let definition = definition(priority);
        let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
        check_profile("Z3", &definition, &solver);
    }
}

// The high-priority complement fixes B to no. Simplification then changes the <k> head
// from chooser(B) to idle before the lower-priority rule is selected.
#[cfg(feature = "z3")]
fn k_head_definition() -> BackendDefinition {
    let source = DEFINITION.replace(
        "endmodule []",
        r#"
    sort SortKCell{} []
    sort SortTop{} []
    sort SortFlag{} []
    symbol yes{}() : SortFlag{} [constructor{}(), total{}()]
    symbol no{}() : SortFlag{} [constructor{}(), total{}()]
    symbol Lbl'-LT-'k'-GT-'{}(SortW{}) : SortKCell{} [constructor{}(), total{}()]
    symbol top{}(SortKCell{}, SortFlag{}) : SortTop{} [constructor{}(), total{}()]
    symbol topDone{}() : SortTop{} [constructor{}(), total{}()]
    symbol chooser{}(SortFlag{}) : SortW{} [function{}(), total{}()]
    axiom{R} \implies{R}(
        \and{R}(
            \top{R}(),
            \and{R}(\in{SortFlag{},R}(X0:SortFlag{}, no{}()), \top{R}())
        ),
        \equals{SortW{},R}(
            chooser{}(X0:SortFlag{}),
            \and{SortW{}}(idle{}(), \top{SortW{}}())
        )
    ) []
    axiom{} \rewrites{SortTop{}}(
        \and{SortTop{}}(
            top{}(Lbl'-LT-'k'-GT-'{}(W:SortW{}), B:SortFlag{}),
            \not{SortTop{}}(\equals{SortFlag{},SortTop{}}(B:SortFlag{}, no{}()))
        ),
        topDone{}()
    ) [label{}("higher-k"), priority{}("10")]
    axiom{} \rewrites{SortTop{}}(
        \and{SortTop{}}(
            top{}(Lbl'-LT-'k'-GT-'{}(idle{}()), B:SortFlag{}),
            \top{SortTop{}}()
        ),
        topDone{}()
    ) [label{}("lower-k"), priority{}("50")]
endmodule []"#,
    );
    BackendDefinition::internalize(&parse_definition(&source).unwrap(), "STUCK-INSTANCES").unwrap()
}

#[cfg(feature = "z3")]
#[test]
fn simplified_remainder_reselects_a_changed_k_head() {
    let definition = k_head_definition();
    let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
    let initial = Pattern {
        term: internal_term(
            &definition,
            "top{}(Lbl'-LT-'k'-GT-'{}(chooser{}(B:SortFlag{})), B:SortFlag{})",
        ),
        constraints: Vec::new(),
    };
    let result = execute_with_solver(&definition, initial, options(u64::MAX), &solver);
    let lower = result.leaves.iter().find(|leaf| {
        leaf.trace
            .iter()
            .any(|entry| entry.label.as_deref() == Some("lower-k"))
    });
    let Some(lower) = lower else {
        panic!("the false complement must reach the reselected <k> rule: {result:?}");
    };
    assert!(
        lower
            .trace
            .iter()
            .any(|entry| entry.kind == TraceKind::Simplification && entry.depth == 0),
        "the <k> head must simplify before the lower-priority rewrite: {lower:?}"
    );
    let mut checked = 0;
    for leaf in result
        .leaves
        .iter()
        .filter(|leaf| leaf.halt_reason == HaltReason::Stuck)
    {
        let variables: Vec<_> = leaf
            .pattern
            .term
            .attributes()
            .variables
            .iter()
            .cloned()
            .chain(
                leaf.pattern
                    .constraints
                    .iter()
                    .flat_map(|predicate| predicate.free_variables()),
            )
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();
        visit_instances(
            &definition,
            &leaf.pattern,
            &solver,
            &variables,
            &mut Substitution::new(),
            &mut checked,
            "changed <k> head",
        );
    }
    assert!(
        checked > 0,
        "the changed-head fixture needs a feasible Stuck instance"
    );
}
