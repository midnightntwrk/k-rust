//! The contract of `k_rust::backend::ExecutionRole`: removing the `Origin` attributes, the
//! `RuleName` attributes of axioms that carry a `UNIQUE_ID`, and exactly equal axioms keeps what
//! `execute` and `search` answer to a request that names no rule and sets no bound that counts
//! branches, paths, witnesses or work. The requests outside the contract are pinned here too.

use std::collections::BTreeSet;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionRole, ExecutionStrategy,
        HaltReasonOutput, ResultModalityOutput, SearchRequest, SearchTypeArg, execution_role,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::{
        ast::{Attributes, Definition, Pattern, Sentence},
        parser::parse_definition,
    },
    names::KoreAttribute,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

/// IMP of the K tutorial: a byte-identical copy of
/// `k-distribution/tests/regression-new/pl-tutorial/1_k/2_imp/lesson_4/imp.k` from K at commit
/// `4a46d1231473b599c699160132fd6e76a5c46406`, with its copyright header.
const IMP: &str = include_str!("fixtures/kink/imp-lesson-4.k");

struct Compiled {
    artifacts: CompiledKoreArtifacts,
    grammar: ProgramGrammar,
    main: String,
}

impl Compiled {
    fn new(source: &str, main: &str) -> Self {
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("test.k", source),
            main,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                ..CompilationBackend::Rust.load_options()
            },
        )
        .unwrap();
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let grammar = ProgramGrammar::new(&loaded.into_definition()).unwrap();
        Self {
            artifacts,
            grammar,
            main: main.to_owned(),
        }
    }

    /// The initial configuration whose `$PGM` is `program` parsed at `sort`.
    fn initial(&self, sort: &str, program: &str) -> Pattern {
        let mut assembler = ConfigurationAssembler::new(
            &self.grammar,
            &self.main,
            &self.main,
            &self.artifacts.configuration_variables,
        );
        assembler.program(&Sort::new(sort), program).unwrap();
        assembler.finish().unwrap()
    }

    /// D: the compiled `definition.kore`.
    fn definition(&self) -> Definition {
        parse_definition(&self.artifacts.definition_kore).unwrap()
    }

    /// D': D with the origin and rule-name attributes removed and equal axioms identified.
    fn reduced(&self) -> Definition {
        reduce(self.definition())
    }

    fn backend(&self, definition: Definition) -> Backend {
        Backend::from_definition(definition, self.main.clone(), BackendOptions::default()).unwrap()
    }
}

/// The attribute `pattern` names, when it is one the backend knows.
fn kore_attribute(pattern: &Pattern) -> Option<KoreAttribute> {
    let Pattern::Application { symbol, .. } = pattern else {
        return None;
    };
    KoreAttribute::ALL
        .into_iter()
        .find(|attribute| attribute.as_str() == symbol.name)
}

/// Remove the attributes whose role is `roles`.
fn strip(attributes: &mut Attributes, roles: &[ExecutionRole]) {
    attributes.0.retain(|attribute| {
        !kore_attribute(attribute)
            .is_some_and(|attribute| roles.contains(&execution_role(attribute)))
    });
}

/// Whether `attributes` names a `UNIQUE_ID`.
fn has_unique_id(attributes: &Attributes) -> bool {
    attributes
        .0
        .iter()
        .any(|attribute| kore_attribute(attribute) == Some(KoreAttribute::UniqueId))
}

/// Remove the `roles` attributes everywhere.
fn strip_definition(definition: &mut Definition, roles: &[ExecutionRole]) {
    strip(&mut definition.attributes, roles);
    for module in &mut definition.modules {
        strip(&mut module.attributes, roles);
        for sentence in &mut module.sentences {
            let attributes = match sentence {
                Sentence::Import { attributes, .. }
                | Sentence::SortDeclaration { attributes, .. }
                | Sentence::SymbolDeclaration { attributes, .. }
                | Sentence::AliasDeclaration { attributes, .. }
                | Sentence::Axiom { attributes, .. }
                | Sentence::Claim { attributes, .. } => attributes,
            };
            strip(attributes, roles);
        }
    }
}

/// D' of the contract: no origins anywhere, no labels on axioms that carry a `UNIQUE_ID`, and
/// no axiom equal to an earlier one of its module.
fn reduce(mut definition: Definition) -> Definition {
    strip_definition(&mut definition, &[ExecutionRole::Origin]);
    for module in &mut definition.modules {
        for sentence in &mut module.sentences {
            if let Sentence::Axiom { attributes, .. } = sentence
                && has_unique_id(attributes)
            {
                strip(attributes, &[ExecutionRole::RuleName]);
            }
        }
    }
    for module in &mut definition.modules {
        let mut kept: Vec<Sentence> = Vec::new();
        for sentence in std::mem::take(&mut module.sentences) {
            let duplicate = matches!(sentence, Sentence::Axiom { .. }) && kept.contains(&sentence);
            if !duplicate {
                kept.push(sentence);
            }
        }
        module.sentences = kept;
    }
    definition
}

type Leaves = BTreeSet<(String, String)>;

/// The (state, halt reason) leaves of a run, and how many there are.
fn leaves(backend: &mut Backend, request: ExecuteRequest) -> (Leaves, usize) {
    let result = backend.execute(request).unwrap();
    let count = result.leaves.len();
    let set = result
        .leaves
        .into_iter()
        .map(|leaf| (leaf.state.to_string(), format!("{:?}", leaf.reason)))
        .collect();
    (set, count)
}

/// The states a search reaches within `depth` steps.
fn reachable(backend: &mut Backend, initial: &Pattern, depth: u64) -> BTreeSet<String> {
    let response = backend
        .search(SearchRequest {
            search_type: SearchTypeArg::All,
            max_depth: Some(depth),
            ..SearchRequest::new(initial.clone())
        })
        .unwrap();
    response
        .states
        .iter()
        .map(|state| serde_json::to_string(&state.state).unwrap())
        .collect()
}

/// Run `program` on D and on D' with strategy `all`, state-set and path-set, and search its
/// reachable states; assert the contract and return the path-set leaf counts of D and D'.
fn assert_roles_keep_execution(
    compiled: &Compiled,
    sort: &str,
    program: &str,
    depth: u64,
) -> (usize, usize) {
    let initial = compiled.initial(sort, program);
    assert!(
        compiled.definition() != compiled.reduced(),
        "the definition carries origins or rule names to remove"
    );
    let mut original = compiled.backend(compiled.definition());
    let mut reduced = compiled.backend(compiled.reduced());
    let mut path_set_counts = (0, 0);
    for modality in [
        ResultModalityOutput::StateSet,
        ResultModalityOutput::PathSet,
    ] {
        let request = ExecuteRequest {
            max_depth: Some(depth),
            result_modality: modality,
            ..ExecuteRequest::new(initial.clone())
        };
        let (left, left_count) = leaves(&mut original, request.clone());
        let (right, right_count) = leaves(&mut reduced, request);
        assert!(!left.is_empty(), "{program}");
        assert_eq!(left, right, "{program}, {modality:?}");
        if matches!(modality, ResultModalityOutput::PathSet) {
            path_set_counts = (left_count, right_count);
        }
    }
    // Strategy `any` follows one path, so its leaves show the order in which rules are tried.
    let any = ExecuteRequest {
        max_depth: Some(depth),
        strategy: ExecutionStrategy::Any,
        ..ExecuteRequest::new(initial.clone())
    };
    assert_eq!(
        leaf_list(&mut original, any.clone()),
        leaf_list(&mut reduced, any),
        "{program}, any"
    );
    assert_eq!(
        reachable(&mut original, &initial, depth),
        reachable(&mut reduced, &initial, depth),
        "{program}"
    );
    path_set_counts
}

/// The (state, halt reason, depth) leaves of a run, in order.
fn leaf_list(backend: &mut Backend, request: ExecuteRequest) -> Vec<(String, String, u64)> {
    backend
        .execute(request)
        .unwrap()
        .leaves
        .into_iter()
        .map(|leaf| {
            (
                leaf.state.to_string(),
                format!("{:?}", leaf.reason),
                leaf.depth,
            )
        })
        .collect()
}

/// A blank line inserted in IMP moves only the origins of `definition.kore` and
/// `syntaxDefinition.kore`; the macros, the execution order of the rewrite rules and the
/// configuration variables do not move.
#[test]
fn a_blank_line_moves_only_the_origins() {
    let shifted = IMP.replacen("module IMP\n", "module IMP\n\n", 1);
    assert_ne!(shifted, IMP);
    let left = Compiled::new(IMP, "IMP").artifacts;
    let right = Compiled::new(&shifted, "IMP").artifacts;
    for (left, right) in [
        (&left.definition_kore, &right.definition_kore),
        (&left.syntax_definition_kore, &right.syntax_definition_kore),
    ] {
        assert_ne!(left, right);
        let mut left = parse_definition(left).unwrap();
        let mut right = parse_definition(right).unwrap();
        strip_definition(&mut left, &[ExecutionRole::Origin]);
        strip_definition(&mut right, &[ExecutionRole::Origin]);
        assert!(left == right);
    }
    assert_eq!(left.macros_kore, right.macros_kore);
    assert_eq!(left.execution_rewrite_order, right.execution_rewrite_order);
    assert_eq!(left.configuration_variables, right.configuration_variables);
}

#[test]
fn imp_runs_the_same_without_origins_and_rule_names() {
    let imp = Compiled::new(IMP, "IMP");
    assert_roles_keep_execution(&imp, "Pgm", "int x, y; x = 1; y = x + 2;", 40);
    assert_roles_keep_execution(
        &imp,
        "Pgm",
        "int n; n = 2; while (!(n <= 0)) { n = n + -1; }",
        60,
    );
}

/// Two rules equal but for their labels stay two rules, so a path-set run has a leaf for each;
/// with the labels removed they are one axiom. The terminal states are the same.
#[test]
fn rules_equal_but_for_their_labels_add_paths_but_no_states() {
    let duplicate = Compiled::new(
        r"
module DUP
  imports INT
  syntax KItem ::= a() | b()
  configuration <k> $PGM:KItem </k>
  rule [x]: <k> a() => b() </k>
  rule [y]: <k> a() => b() </k>
endmodule
",
        "DUP",
    );
    let (original, reduced) = assert_roles_keep_execution(&duplicate, "KItem", "a()", 10);
    assert_eq!((original, reduced), (2, 1));
}

#[test]
fn owise_priority_and_labelled_function_rules_run_the_same() {
    let rules = Compiled::new(
        r"
module RULES
  imports INT
  syntax KItem ::= f(Int) | g(Int) | s(Int) | zero() | other() | first() | second()
                 | left(Int) | right(Int)
  syntax Int ::= inc(Int) [function]
  configuration <k> $PGM:KItem </k>
  rule [f-zero]: <k> f(0) => zero() </k>
  rule <k> f(_) => other() </k> [owise]
  rule [g-first]: <k> g(_) => first() </k> [priority(10)]
  rule <k> g(_) => second() </k> [priority(20)]
  rule [inc-def]: inc(X) => X +Int 1
  rule <k> s(X) => s(inc(X)) </k> requires X <Int 3
  rule <k> s(X) => left(X) </k> requires X >=Int 3
  rule <k> s(X) => right(X) </k> requires X >=Int 3
endmodule
",
        "RULES",
    );
    for program in ["f(0)", "f(1)", "g(5)", "s(0)"] {
        assert_roles_keep_execution(&rules, "KItem", program, 20);
    }
}

/// A request that names rules selects by `label`, so removing labels changes its leaves: the
/// contract does not cover it.
#[test]
fn a_request_that_names_rules_is_outside_the_contract() {
    let selected = Compiled::new(
        r"
module DUP
  imports INT
  syntax KItem ::= a() | b() | c()
  configuration <k> $PGM:KItem </k>
  rule [x]: <k> a() => b() </k>
  rule <k> b() => c() </k>
endmodule
",
        "DUP",
    );
    let initial = selected.initial("KItem", "a()");
    let mut original = selected.backend(selected.definition());
    let mut reduced = selected.backend(selected.reduced());
    let summary = |backend: &mut Backend, request: ExecuteRequest| {
        backend
            .execute(request)
            .unwrap()
            .leaves
            .into_iter()
            .map(|leaf| (leaf.reason, leaf.depth))
            .collect::<Vec<_>>()
    };
    let terminal = ExecuteRequest {
        terminal_rules: vec!["DUP.x".to_owned()],
        ..ExecuteRequest::new(initial.clone())
    };
    assert_eq!(
        summary(&mut original, terminal.clone()),
        [(HaltReasonOutput::Terminal, 1)]
    );
    assert_eq!(
        summary(&mut reduced, terminal),
        [(HaltReasonOutput::Stuck, 2)]
    );
    let cut_point = ExecuteRequest {
        cut_point_rules: vec!["DUP.x".to_owned()],
        ..ExecuteRequest::new(initial)
    };
    assert_eq!(
        summary(&mut original, cut_point.clone()),
        [(HaltReasonOutput::CutPoint, 0)]
    );
    assert_eq!(
        summary(&mut reduced, cut_point),
        [(HaltReasonOutput::Stuck, 2)]
    );
}

/// Two rules equal but for their labels, then one more step.
const DUPLICATE: &str = r"
module DUP
  imports INT
  syntax KItem ::= a() | b() | c() | d()
  configuration <k> $PGM:KItem </k>
  rule [x]: <k> a() => b() </k>
  rule [y]: <k> a() => b() </k>
  rule <k> b() => c() </k>
endmodule
";

/// Bounds that count branches, paths or witnesses see the extra path that the label variants
/// make, so they stop D and D' differently: the contract excludes them.
#[test]
fn bounds_that_count_paths_are_outside_the_contract() {
    let duplicate = Compiled::new(DUPLICATE, "DUP");
    let initial = duplicate.initial("KItem", "a()");
    let mut original = duplicate.backend(duplicate.definition());
    let mut reduced = duplicate.backend(duplicate.reduced());
    let reasons = |backend: &mut Backend, request: ExecuteRequest| {
        leaf_list(backend, request)
            .into_iter()
            .map(|(_, reason, depth)| (reason, depth))
            .collect::<Vec<_>>()
    };
    let stuck = vec![("Stuck".to_owned(), 2)];
    // Without a counting bound both run to `c()`.
    let plain = ExecuteRequest::new(initial.clone());
    assert_eq!(reasons(&mut original, plain.clone()), stuck);
    assert_eq!(reasons(&mut reduced, plain), stuck);
    // `stop_at_branch`: the label variants are a branch in D only.
    let branch = ExecuteRequest {
        stop_at_branch: true,
        ..ExecuteRequest::new(initial.clone())
    };
    assert_eq!(
        reasons(&mut original, branch.clone()),
        [("Branch".to_owned(), 0)]
    );
    assert_eq!(reasons(&mut reduced, branch), stuck);
    // `max_breadth`: two paths in D exceed a breadth of one; D' has one path.
    for modality in [
        ResultModalityOutput::StateSet,
        ResultModalityOutput::PathSet,
    ] {
        let breadth = ExecuteRequest {
            max_breadth: Some(1),
            result_modality: modality,
            ..ExecuteRequest::new(initial.clone())
        };
        assert!(
            reasons(&mut original, breadth.clone())
                .iter()
                .all(|leaf| *leaf == ("BreadthBound".to_owned(), 1)),
            "{modality:?}"
        );
        assert_eq!(reasons(&mut reduced, breadth), stuck, "{modality:?}");
    }
    // A search under `max_breadth` reaches fewer states in D.
    let search_breadth = |backend: &mut Backend| {
        backend
            .search(SearchRequest {
                search_type: SearchTypeArg::All,
                max_breadth: Some(1),
                ..SearchRequest::new(initial.clone())
            })
            .unwrap()
            .states
            .len()
    };
    assert!(search_breadth(&mut original) < search_breadth(&mut reduced));
    // A path search counts witnesses: with `max_results` the duplicate path of D uses the
    // quota that D' spends on another result.
    let branching = Compiled::new(
        &DUPLICATE.replace("rule <k> b() => c() </k>", "rule <k> a() => d() </k>"),
        "DUP",
    );
    let initial = branching.initial("KItem", "a()");
    let witnesses = |backend: &mut Backend| {
        backend
            .search_paths(SearchRequest {
                search_type: SearchTypeArg::Final,
                max_results: Some(2),
                ..SearchRequest::new(initial.clone())
            })
            .unwrap()
            .witnesses
            .iter()
            .map(|witness| serde_json::to_string(&witness.state).unwrap())
            .collect::<BTreeSet<_>>()
            .len()
    };
    assert_eq!(witnesses(&mut branching.backend(branching.definition())), 1);
    assert_eq!(witnesses(&mut branching.backend(branching.reduced())), 2);
}

/// D with every `UNIQUE_ID` removed, so that each labelled axiom's label is its id.
fn without_unique_ids(mut definition: Definition) -> Definition {
    for module in &mut definition.modules {
        for sentence in &mut module.sentences {
            if let Sentence::Axiom { attributes, .. } = sentence {
                attributes
                    .0
                    .retain(|attribute| kore_attribute(attribute) != Some(KoreAttribute::UniqueId));
            }
        }
    }
    definition
}

/// A label on an axiom without a `UNIQUE_ID` is the rule's id, which keys the guard against a
/// side condition re-entering its own rule: D' keeps it, and removing it changes the result.
#[test]
fn a_label_that_is_a_rules_id_is_kept() {
    let compiled = Compiled::new(
        r"
module RE
  imports INT
  syntax KItem ::= run(Int) | res(Int)
  syntax Int ::= f(Int) [function]
  syntax Int ::= g(Int) [function, total]
  configuration <k> $PGM:KItem </k>
  rule g(_) => 0
  rule <k> run(I) => res(f(I)) </k>
  rule [s1]: f(X) => 20 requires g(X) ==Int 0 [simplification(40)]
  rule [s2]: f(X) => 10 requires f(X) ==Int 20 [simplification(30)]
endmodule
",
        "RE",
    );
    let request = ExecuteRequest::new(compiled.initial("KItem", "run(0)"));
    let result = |definition: Definition| {
        leaf_list(&mut compiled.backend(definition), request.clone())
            .into_iter()
            .map(|(state, ..)| state)
            .collect::<Vec<_>>()
    };
    let labels_as_ids = without_unique_ids(compiled.definition());
    let expected = result(compiled.definition());
    assert_eq!(result(labels_as_ids.clone()), expected);
    assert_eq!(result(reduce(labels_as_ids.clone())), expected);
    let mut unlabelled = labels_as_ids;
    strip_definition(&mut unlabelled, &[ExecutionRole::RuleName]);
    assert_ne!(result(unlabelled), expected);
}
