//! An execution reports every stop for lack of native stack it met (`stackStops`, absent when
//! zero), and a leaf a stack stop ended carries the structured cause `stack-exhausted`, through
//! `execute`, `execute_observed`, their JSON forms and the writer
//! (`docs/compatibility.md`, "Determinism and concurrency").

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ObservedRequest},
    kore::parser::parse_pattern,
};

/// `deep(N)` recurses `N` levels, not in tail position.
const DEEP: &str = r#"[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    symbol deep{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    sort SortS{} []
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) []
    axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(deep{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(deep{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) []
endmodule []"#;

/// The serialized results of `done(deep(30000))` at depth 0 through every entry point, on an
/// 8 MiB thread, with the simplifier's stack budget set to `budget` when one is given.
fn results(budget: Option<usize>) -> Vec<serde_json::Value> {
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let mut backend =
                Backend::new(DEEP, "MAIN", BackendOptions::default()).expect("the backend loads");
            if let Some(budget) = budget {
                backend.set_simplification_stack_budget(budget);
            }
            let request = || ExecuteRequest {
                max_depth: Some(0),
                ..ExecuteRequest::new(
                    parse_pattern(r#"done{}(deep{}(\dv{SortInt{}}("30000")))"#)
                        .expect("the state parses"),
                )
            };
            let observed = || ObservedRequest {
                request: request(),
                rules: None,
            };
            let mut written = Vec::new();
            backend
                .execute_observed_to_writer(observed(), &mut written)
                .expect("it writes");
            let texts = [
                serde_json::to_string(&backend.execute(request()).expect("it executes"))
                    .expect("it serializes"),
                serde_json::to_string(
                    &backend
                        .execute_observed(observed())
                        .expect("it executes observed"),
                )
                .expect("it serializes"),
                backend.execute_json(request()).expect("it executes"),
                backend
                    .execute_observed_json(observed())
                    .expect("it executes observed"),
                String::from_utf8(written).expect("the written result is UTF-8"),
            ];
            texts
                .iter()
                .map(|text| serde_json::from_str(text).expect("the result is JSON"))
                .collect()
        })
        .expect("the thread starts")
        .join()
        .expect("the runs do not panic")
}

#[test]
fn a_stack_stopped_leaf_has_a_structured_cause_and_the_run_counts_its_stops() {
    for result in results(Some(0)) {
        let stops = result["stackStops"].as_u64().unwrap_or(0);
        assert!(stops >= 1, "no stack stop was counted: {result}");
        let [leaf] = result["leaves"].as_array().expect("leaves").as_slice() else {
            panic!("one leaf: {result}");
        };
        assert_eq!(leaf["reason"], "simplification-error", "{leaf}");
        assert_eq!(
            leaf["cause"],
            serde_json::json!({"kind": "stack-exhausted"}),
            "{leaf}"
        );
    }
}

#[test]
fn a_run_without_stack_stops_reports_none() {
    for result in results(None) {
        assert!(result.get("stackStops").is_none(), "{result}");
        let [leaf] = result["leaves"].as_array().expect("leaves").as_slice() else {
            panic!("one leaf: {result}");
        };
        assert_eq!(leaf["reason"], "depth-bound", "{leaf}");
        assert!(leaf.get("cause").is_none(), "{leaf}");
    }
}

#[test]
fn the_backend_advertises_its_stack_stop_count() {
    let backend = Backend::new(DEEP, "MAIN", BackendOptions::default()).expect("the backend loads");
    assert!(backend.capabilities().stack_stops);
}
