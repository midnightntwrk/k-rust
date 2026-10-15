//! A load inside the scope of a cancelled request discharges the definedness of rewrite rules as
//! any other load, through the facade: the discharge is cached with the definition (a
//! `Backend` keeps every module it loads), so the request that happens to load a module must not
//! reach it (`docs/backend-port.md`, the critical-pair check and the discharge after it).
//!
//! The fixture's rule `state => done(p(0))` is discharged by simplifying the instance of `p`'s
//! ceil equation, `hk(5) == 5`.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    kore::parser::{parse_definition, parse_pattern},
};
use k_rust_backend::{definition::BackendDefinition, stop::CancellationToken};

const DISCHARGE: &str = r#"[] module MAIN 
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
    hooked-symbol hk{}(SortInt{}) : SortInt{} [function{}(), hook{}("MYHOOK.hk")]
    symbol p{}(SortInt{}) : SortInt{} [function{}()]
    sort SortS{} []
    symbol state{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol done{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
 axiom{R} \implies{R}(\and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, \dv{SortInt{}}("0")), \top{R}())), \equals{SortInt{}, R}(hk{}(X0:SortInt{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))) [] axiom{R} \implies{R}(\and{R}(\equals{SortBool{}, R}(gtInt{}(VarN:SortInt{}, \dv{SortInt{}}("0")), \dv{SortBool{}}("true")), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \top{R}())), \equals{SortInt{}, R}(hk{}(X0:SortInt{}), \and{SortInt{}}(addInt{}(hk{}(subInt{}(VarN:SortInt{}, \dv{SortInt{}}("1"))), \dv{SortInt{}}("1")), \top{SortInt{}}()))) [] axiom{R} \implies{R}(\top{R}(), \equals{R, R}(\ceil{SortInt{}, R}(p{}(X:SortInt{})), \equals{SortInt{}, R}(hk{}(\dv{SortInt{}}("5")), \dv{SortInt{}}("5")))) [] axiom{} \rewrites{SortS{}}(\and{SortS{}}(state{}(), \top{SortS{}}()), done{}(p{}(\dv{SortInt{}}("0")))) [label{}("advance")] endmodule []"#;

fn cancelled() -> CancellationToken {
    let token = CancellationToken::new();
    token.cancel();
    token
}

/// Whether the definition discharged each rewrite rule's definedness.
fn discharged(definition: &BackendDefinition) -> Vec<bool> {
    definition
        .rewrite_theory()
        .values()
        .flat_map(|groups| groups.values())
        .flatten()
        .map(|rule| rule.rule.attributes.preserves_definedness)
        .collect()
}

#[test]
fn a_definition_internalized_in_a_cancelled_scope_discharges_its_rules() {
    let syntax = parse_definition(DISCHARGE).expect("the fixture parses");
    let fresh = Backend::internalize_definition(&syntax, "MAIN").expect("the fixture loads");
    assert_eq!(discharged(&fresh), [true]);
    let under = cancelled()
        .scope(|| Backend::internalize_definition(&syntax, "MAIN"))
        .expect("the fixture loads");
    assert_eq!(discharged(&under), discharged(&fresh));
}

/// A `Backend` whose default module is another loads `MAIN` lazily, for the first request that
/// names it; that request is cancelled, and the definition it cached discharges the rule as a
/// load without a token does.
#[test]
fn a_module_first_loaded_by_a_cancelled_request_is_cached_with_its_rules_discharged() {
    let at = DISCHARGE
        .rfind("endmodule []")
        .expect("the fixture ends a module");
    let two = format!(
        "{}endmodule []\nmodule OTHER\n  sort SortX{{}} []\nendmodule []\n",
        &DISCHARGE[..at]
    );
    let state = parse_pattern("state{}()").expect("the state parses");
    let mut backend =
        Backend::new(&two, "OTHER", BackendOptions::default()).expect("the backend loads");
    let _cancelled = cancelled().scope(|| {
        backend.execute(ExecuteRequest {
            module_name: Some("MAIN".into()),
            ..ExecuteRequest::new(state.clone())
        })
    });
    let cached = backend
        .select_definition(Some("MAIN"))
        .expect("MAIN is loaded");
    let mut fresh =
        Backend::new(&two, "OTHER", BackendOptions::default()).expect("the backend loads");
    let fresh = fresh.select_definition(Some("MAIN")).expect("MAIN loads");
    assert_eq!(discharged(&fresh), [true]);
    assert_eq!(discharged(&cached), discharged(&fresh));
}
