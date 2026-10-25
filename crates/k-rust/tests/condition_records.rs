//! Condition records of run coverage (G-7): an execute request that sets `collectConditions`
//! beside `collectCoverage` receives, for each rule it names whose `requires` the run began to
//! decide, the bindings of the variables the condition reads, the condition with every node's
//! truth, its atoms' operands evaluated under the instance, and the attempt's verdict
//! (docs/compatibility.md, "Run coverage").
//!
//! The definitions are the fuzz crate's IMP fixture (`crates/k-rust-fuzz/tests/data/imp/imp.k`)
//! and `fixtures/coverage/conditions.k`, compiled in-process and assembled with their programs as
//! `krun --io off` does.

use std::sync::OnceLock;

use k_rust::{
    backend::{Backend, BackendOptions, ConditionCollection, ExecuteRequest, ResultModalityOutput},
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ConfigurationError,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::ast::Pattern,
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use serde_json::{Value, json};

/// A definition compiled in-process, with what assembling its programs needs.
struct Definition {
    main: &'static str,
    kore: String,
    syntax_module: String,
    grammar: ProgramGrammar,
    variables: std::collections::BTreeMap<String, Sort>,
}

fn compile(file: &str, source: &str, main: &'static str) -> Definition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").unwrap()],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(file, source),
        main,
        None,
        &mut resolver,
        &options,
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let grammar = ProgramGrammar::new(&loaded.into_definition()).unwrap();
    Definition {
        main,
        kore: artifacts.definition_kore,
        syntax_module,
        grammar,
        variables: artifacts.configuration_variables,
    }
}

/// The IMP fixture compiled once per test binary.
fn imp() -> &'static Definition {
    static COMPILED: OnceLock<Definition> = OnceLock::new();
    COMPILED.get_or_init(|| {
        compile(
            "imp.k",
            include_str!("../../k-rust-fuzz/tests/data/imp/imp.k"),
            "IMP",
        )
    })
}

/// `fixtures/coverage/conditions.k` compiled once per test binary.
fn shapes() -> &'static Definition {
    static COMPILED: OnceLock<Definition> = OnceLock::new();
    COMPILED.get_or_init(|| {
        compile(
            "conditions.k",
            include_str!("fixtures/coverage/conditions.k"),
            "CONDITIONS",
        )
    })
}

impl Definition {
    /// The initial configuration of `program`.
    fn state(&self, program: &str) -> Pattern {
        let mut assembler = ConfigurationAssembler::new(
            &self.grammar,
            self.main,
            &self.syntax_module,
            &self.variables,
        );
        assembler
            .program_file(&Sort::new("Pgm"), program, "test.pgm")
            .unwrap();
        assembler
            .bind_stream_defaults(false, false, || Ok::<_, ConfigurationError>(b"\n".to_vec()))
            .unwrap();
        assembler.finish().unwrap()
    }

    fn backend(&self) -> Backend {
        Backend::new(&self.kore, self.main, BackendOptions::default()).unwrap()
    }

    fn request(&self, program: &str, conditions: Option<ConditionCollection>) -> ExecuteRequest {
        let mut request = ExecuteRequest::new(self.state(program));
        request.collect_coverage = true;
        request.collect_conditions = conditions;
        request
    }

    /// The wire output of `request` on a fresh backend.
    fn run(&self, request: ExecuteRequest) -> Value {
        serde_json::from_str(&self.backend().execute_json(request).unwrap()).unwrap()
    }

    /// The id of the rule labelled `label`.
    fn rule(&self, label: &str) -> String {
        let label = format!("{}.{label}", self.main);
        self.backend()
            .rule_catalog(None)
            .unwrap()
            .into_iter()
            .find(|rule| rule.label.as_deref() == Some(label.as_str()))
            .unwrap_or_else(|| panic!("no rule {label}"))
            .id
    }

    /// The one record of the rule labelled `label` on `program`, and whether the rule applied.
    fn only_record(&self, label: &str, program: &str) -> (Value, bool) {
        let id = self.rule(label);
        let result = self.run(self.request(program, Some(ConditionCollection::new([id.as_str()]))));
        let records = records(&result, &id).as_array().unwrap().clone();
        let [record] = &records[..] else {
            panic!("{program}: {records:?}")
        };
        let applied = result["coverage"]["applied"]
            .as_array()
            .unwrap()
            .contains(&json!(id));
        (record.clone(), applied)
    }
}

/// The id of the division rule, `I1 / I2 => I1 /Int I2 requires I2 =/=Int 0` (imp.k:57), which
/// has no label: the one rule whose condition, recorded for every rule of the catalog on a
/// division, holds an `INT.ne` atom.
fn division_rule() -> String {
    let every = imp()
        .backend()
        .rule_catalog(None)
        .unwrap()
        .into_iter()
        .map(|rule| rule.id)
        .collect::<Vec<_>>();
    let result = imp().run(imp().request(
        "int x, y, q; x = 10; y = 2; q = x / y;",
        Some(ConditionCollection::new(every)),
    ));
    let ids = result["coverage"]["conditions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|rule| {
            rule["records"].as_array().unwrap().iter().any(|record| {
                record["condition"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|node| node["child"]["hook"] == "INT.ne")
            })
        })
        .map(|rule| rule["rule"].as_str().unwrap().to_owned())
        .collect::<Vec<_>>();
    let [id] = &ids[..] else {
        panic!("rules with an INT.ne atom: {ids:?}")
    };
    id.clone()
}

/// A KORE term as the wire writes one, in its envelope.
fn kore(term: Value) -> Value {
    json!({"format": "KORE", "version": 1, "term": term})
}

fn int(value: i64) -> Value {
    kore(json!({
        "tag": "DV",
        "sort": {"tag": "SortApp", "name": "SortInt", "args": []},
        "value": value.to_string(),
    }))
}

/// The records of rule `id` in a wire result.
fn records<'a>(result: &'a Value, id: &str) -> &'a Value {
    let conditions = result["coverage"]["conditions"]
        .as_array()
        .expect("the result has condition records");
    let rule = conditions
        .iter()
        .find(|rule| rule["rule"] == id)
        .unwrap_or_else(|| panic!("no records of {id}: {conditions:?}"));
    &rule["records"]
}

/// The value of a node or an operand, without its term's envelope where it has one.
fn int_operand(value: i64) -> Value {
    json!({"kind": "value", "term": int(value)})
}

/// A division by zero blocks the division rule: its entry is recorded with the binding of the
/// divisor, the one variable the condition reads, the conjunct `\equals(I2 =/=Int 0, true)`
/// false over the atom `I2 =/=Int 0`, false, with both operands 0, and the verdict refuted.
#[test]
fn a_blocked_imp_rule_reports_its_bindings_and_failing_operands() {
    let id = division_rule();
    let result = imp().run(imp().request(
        "int x, y, q; x = 10; y = 0; q = x / y;",
        Some(ConditionCollection::new([id.as_str()])),
    ));
    assert!(
        !result["coverage"]["applied"]
            .as_array()
            .unwrap()
            .contains(&json!(id)),
        "the division never applies"
    );
    let variable = kore(json!({
        "tag": "EVar",
        "name": "VarI2",
        "sort": {"tag": "SortApp", "name": "SortInt", "args": []},
    }));
    assert_eq!(
        records(&result, &id),
        &json!([{
            "bindings": [{"variable": variable, "value": int_operand(0)}],
            "condition": [{
                "node": "equals",
                "literal": true,
                "child": {
                    "node": "atom",
                    "head": "Lbl'UndsEqlsSlshEqls'Int'Unds'",
                    "hook": "INT.ne",
                    "operands": [int_operand(0), int_operand(0)],
                    "reads": [0],
                    "value": "false",
                },
                "value": "false",
            }],
            "verdict": "refuted",
        }])
    );
}

/// `notBool (X in keys(STATE))` of the `decl` rule, entered for a second declaration of `x`:
/// the membership atom is true (its operands the identifier and the evaluated key set), so the
/// `notBool` node is false, the conjunct false, and the attempt refuted. The rule is named by its
/// label.
#[test]
fn a_negated_atom_is_recorded_under_its_connective() {
    let result = imp().run(imp().request(
        "int x, x; x = 1;",
        Some(ConditionCollection::new(["IMP.decl"])),
    ));
    let conditions = result["coverage"]["conditions"].as_array().unwrap();
    let [rule] = &conditions[..] else {
        panic!("{conditions:?}")
    };
    let records = rule["records"].as_array().unwrap();
    let blocked = records
        .iter()
        .find(|record| record["verdict"] == "refuted")
        .unwrap_or_else(|| panic!("no entry where x is declared: {records:?}"));
    let conjunct = &blocked["condition"][0];
    assert_eq!(conjunct["node"], "equals", "{conjunct}");
    assert_eq!(conjunct["value"], "false", "{conjunct}");
    let negation = &conjunct["child"];
    assert_eq!(negation["connective"], "notBool", "{negation}");
    assert_eq!(negation["value"], "false", "{negation}");
    let atom = &negation["children"][0];
    assert_eq!(atom["hook"], "SET.in", "{atom}");
    assert_eq!(atom["value"], "true", "{atom}");
    let operands = atom["operands"].as_array().unwrap();
    assert_eq!(operands.len(), 2, "{atom}");
    assert!(
        operands.iter().all(|operand| operand["kind"] == "value"),
        "{atom}"
    );
    // The first declaration's entry held.
    assert!(records.iter().any(|record| record["verdict"] == "held"));
}

/// FZ-G7 review S1: `notBool (X /Int Y >Int 3)` at `Y = 0` is never read as satisfied. The
/// division is undefined, so the comparison and the `notBool` over it are undefined, the
/// conjunct is false, and the attempt is refuted; the rule does not apply.
#[test]
fn notbool_of_an_undefined_comparison_is_undefined() {
    let (record, applied) = shapes().only_record("negdiv", "neg(5, 0)");
    assert!(!applied);
    let conjunct = &record["condition"][0];
    assert_eq!(
        (&conjunct["node"], &conjunct["literal"], &conjunct["value"]),
        (&json!("equals"), &json!(true), &json!("false")),
        "{conjunct}"
    );
    let negation = &conjunct["child"];
    assert_eq!(negation["connective"], "notBool", "{negation}");
    assert_eq!(negation["value"], "undefined", "{negation}");
    let comparison = &negation["children"][0];
    assert_eq!(comparison["hook"], "INT.gt", "{comparison}");
    assert_eq!(comparison["value"], "undefined", "{comparison}");
    assert_eq!(
        comparison["operands"],
        json!([{"kind": "undefined"}, int_operand(3)]),
        "{comparison}"
    );
    assert_eq!(record["verdict"], "refuted");
}

/// The K Boolean connectives are strict, `andThenBool` too, though it does not evaluate the
/// operand it discards (docs/compatibility.md, "Conditionals and Boolean connectives are
/// strict"): `0 =/=Int 0 andThenBool 5 /Int 0 >Int 1` is `false` under the definedness of the
/// discarded operand, which is undefined, so the node is undefined, as the run reads it.
#[test]
fn a_boolean_connective_is_undefined_where_an_operand_is() {
    let (record, applied) = shapes().only_record("lazyr", "lazy(5, 0)");
    assert!(!applied);
    let conjunction = &record["condition"][0]["child"];
    assert_eq!(conjunction["connective"], "andThenBool", "{conjunction}");
    assert_eq!(conjunction["value"], "undefined", "{conjunction}");
    let values = conjunction["children"]
        .as_array()
        .unwrap()
        .iter()
        .map(|child| child["value"].clone())
        .collect::<Vec<_>>();
    assert_eq!(values, [json!("false"), json!("undefined")]);
    assert_eq!(record["verdict"], "refuted");
}

/// The children of a node, by their truths.
fn child_values(node: &Value) -> Vec<Value> {
    node["children"]
        .as_array()
        .unwrap_or_else(|| panic!("{node}"))
        .iter()
        .map(|child| child["value"].clone())
        .collect()
}

/// FZ-12 review 2 N4: where the undefinedness of the discarded operand comes through an
/// equation (`pd(X) = 10 /Int X >Int 3`, undefined at 0), the record still reads the strict
/// connectives over it as undefined. An application of a symbol to an undefined argument is
/// undefined, `andThenBool` too (the `_` of `false andThenBool _ => false` ranges over defined
/// values), so `false andThenBool notBool pd(0)` and the `andBool` above it are undefined: the
/// record has decided an operand undefined, and that decides its strict ancestors.
#[test]
fn a_strict_connective_over_an_operand_undefined_by_an_equation_is_undefined() {
    let (record, applied) = shapes().only_record("lazyeqr", "lazyeq(0, 0)");
    assert!(!applied);
    let conjunct = &record["condition"][0];
    let conjunction = &conjunct["child"];
    assert_eq!(conjunction["connective"], "andBool", "{conjunction}");
    let lazy = &conjunction["children"][1];
    assert_eq!(lazy["connective"], "andThenBool", "{lazy}");
    assert_eq!(
        child_values(lazy),
        [json!("false"), json!("undefined")],
        "{lazy}"
    );
    assert_eq!(lazy["value"], "undefined", "{lazy}");
    assert_eq!(
        child_values(conjunction),
        [json!("true"), json!("undefined")],
        "{conjunction}"
    );
    assert_eq!(conjunction["value"], "undefined", "{conjunction}");
    assert_eq!(conjunct["value"], "false", "{conjunct}");
    assert_eq!(record["verdict"], "refuted");
    // A defined instance next to it is decided as before.
    let (record, applied) = shapes().only_record("lazyeqr", "lazyeq(1, 0)");
    assert!(!applied);
    assert_eq!(record["condition"][0]["child"]["value"], "false");
    assert_eq!(record["verdict"], "refuted");
}

/// A Boolean atom whose operand the record found undefined is undefined by the same strictness:
/// `pd(0) ==Bool false` applies `==Bool` to an undefined argument.
#[test]
fn a_boolean_atom_over_an_undefined_operand_is_undefined() {
    let (record, applied) = shapes().only_record("eqatomr", "eqatom(0, 0)");
    assert!(!applied);
    let atom = &record["condition"][0]["child"];
    assert_eq!(atom["hook"], "BOOL.eq", "{atom}");
    assert_eq!(atom["operands"][0], json!({"kind": "undefined"}), "{atom}");
    assert_eq!(atom["value"], "undefined", "{atom}");
    assert_eq!(record["condition"][0]["value"], "false");
    assert_eq!(record["verdict"], "refuted");
    let (record, applied) = shapes().only_record("eqatomr", "eqatom(5, 0)");
    assert!(applied);
    assert_eq!(record["condition"][0]["child"]["value"], "true");
    assert_eq!(record["verdict"], "held");
}

/// A partial Boolean function with no equation for its argument decides nothing: `pb(3)` is
/// undecided, as are `notBool pb(3)` and the conjunct, and the attempt cannot decide it either.
#[test]
fn an_unevaluated_boolean_function_is_undecided() {
    let (record, _) = shapes().only_record("pbneg", "strictneg(3, 0)");
    let conjunct = &record["condition"][0];
    assert_eq!(conjunct["value"], "undecided", "{conjunct}");
    assert_eq!(conjunct["child"]["value"], "undecided", "{conjunct}");
    assert_eq!(
        conjunct["child"]["children"][0]["value"], "undecided",
        "{conjunct}"
    );
    assert_eq!(record["verdict"], "undecided");
}

/// Every node of `X >Int 0 andBool Y <Int 10` has its own truth: at `(5, 20)` the first atom is
/// true, the second false, the conjunction false; at `(5, 3)` all hold and so does the attempt.
#[test]
fn every_node_of_a_conjunction_has_its_truth() {
    let (refuted, applied) = shapes().only_record("twoc", "two(5, 20)");
    assert!(!applied);
    let conjunction = &refuted["condition"][0]["child"];
    assert_eq!(conjunction["connective"], "andBool", "{conjunction}");
    let values = |node: &Value| {
        node["children"]
            .as_array()
            .unwrap()
            .iter()
            .map(|child| child["value"].clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(values(conjunction), [json!("true"), json!("false")]);
    assert_eq!(conjunction["value"], "false");
    assert_eq!(refuted["verdict"], "refuted");
    let (held, applied) = shapes().only_record("twoc", "two(5, 3)");
    assert!(applied);
    let conjunction = &held["condition"][0]["child"];
    assert_eq!(values(conjunction), [json!("true"), json!("true")]);
    assert_eq!(conjunction["value"], "true");
    assert_eq!(held["condition"][0]["value"], "true");
    assert_eq!(held["verdict"], "held");
}

/// The records are the first `limit` distinct entries in the run's order, and a rule with more
/// distinct entries is marked truncated; equal entries are recorded once.
#[test]
fn the_limit_keeps_the_first_distinct_entries() {
    let id = division_rule();
    let program = "int n, q; n = 4; while (0 < n) { q = 12 / n; q = 12 / n; n = n - 1; }";
    let divisors = |result: &Value| {
        records(result, &id)
            .as_array()
            .unwrap()
            .iter()
            .map(|record| record["bindings"][0]["value"]["term"]["term"]["value"].clone())
            .collect::<Vec<_>>()
    };
    let truncated = |result: &Value| {
        result["coverage"]["conditions"][0]
            .get("truncated")
            .cloned()
    };
    let all = imp().run(imp().request(program, Some(ConditionCollection::new([id.as_str()]))));
    assert_eq!(divisors(&all), ["4", "3", "2", "1"]);
    assert_eq!(truncated(&all), None);
    let mut first_two = ConditionCollection::new([id.as_str()]);
    first_two.limit = 2;
    let limited = imp().run(imp().request(program, Some(first_two)));
    assert_eq!(divisors(&limited), ["4", "3"]);
    assert_eq!(truncated(&limited), Some(json!(true)));
}

/// Off by default: without `collectConditions` the coverage has no `conditions` key, and asking
/// for records of every rule changes no other field of the result, under either modality; two
/// runs on fresh backends write the same bytes.
#[test]
fn records_change_nothing_else_and_are_deterministic() {
    let cases: [(&Definition, &[&str]); 2] = [
        (
            imp(),
            &[
                "int x, y, q; x = 10; y = 0; q = x / y;",
                "int n, q; n = 4; while (0 < n) { q = 12 / n; n = n - 1; }",
                "int x, x; x = 1;",
            ],
        ),
        (
            shapes(),
            &[
                "neg(5, 0)",
                "neg(9, 2)",
                "lazy(5, 0)",
                "lazy(9, 2)",
                "lazyeq(0, 0)",
                "lazyeq(1, 0)",
                "eqatom(0, 0)",
                "strictneg(3, 0)",
                "two(5, 20)",
                "two(5, 3)",
            ],
        ),
    ];
    for (definition, programs) in cases {
        let every = definition
            .backend()
            .rule_catalog(None)
            .unwrap()
            .into_iter()
            .map(|rule| rule.id)
            .collect::<Vec<_>>();
        for program in programs {
            for modality in [
                ResultModalityOutput::StateSet,
                ResultModalityOutput::PathSet,
            ] {
                let with = |conditions: Option<ConditionCollection>| {
                    let mut request = definition.request(program, conditions);
                    request.result_modality = modality;
                    definition.backend().execute_json(request).unwrap()
                };
                let collection = || Some(ConditionCollection::new(every.clone()));
                let on = with(collection());
                assert_eq!(on, with(collection()), "{program}: two runs");
                let off = with(None);
                let mut on: Value = serde_json::from_str(&on).unwrap();
                let off: Value = serde_json::from_str(&off).unwrap();
                assert!(off["coverage"].get("conditions").is_none(), "{program}");
                assert!(
                    on["coverage"]["conditions"].is_array(),
                    "{program}: records asked for"
                );
                on["coverage"].as_object_mut().unwrap().remove("conditions");
                assert_eq!(on, off, "{program} {modality:?}");
            }
        }
    }
}

/// `collectConditions` is part of the run's coverage: without `collectCoverage` the request is
/// refused, and the wire form is read with its defaults.
#[test]
fn conditions_need_coverage_and_are_read_from_the_wire() {
    let mut refused = ExecuteRequest::new(imp().state("int x; x = 1;"));
    refused.collect_conditions = Some(ConditionCollection::new(["IMP.decl"]));
    let error = imp().backend().execute(refused).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("collectConditions requires collectCoverage"),
        "{error}"
    );
    let state = k_rust::kore::codec::to_value(&imp().state("int x; x = 1;")).unwrap();
    let request: ExecuteRequest = serde_json::from_value(json!({
        "state": state,
        "collectCoverage": true,
        "collectConditions": {"rules": ["IMP.decl"]},
    }))
    .unwrap();
    let conditions = request.collect_conditions.clone().unwrap();
    assert_eq!(conditions, ConditionCollection::new(["IMP.decl"]));
    let result = imp().run(request);
    let record = &result["coverage"]["conditions"][0]["records"][0];
    assert_eq!(
        record["bindings"].as_array().unwrap().len(),
        2,
        "X and STATE: {result}"
    );
    assert_eq!(record["verdict"], "held", "{result}");
}
