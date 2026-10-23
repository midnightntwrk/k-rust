//! Expands every tour-minimal invocation in an ordinary (non-proc-macro)
//! process, where `proc_macro2` uses its fallback implementation. A surviving
//! `proc_macro`-only call panics here.

mod support;

use krs_syntax::surface::{AttributeMacro, FunctionMacro};
use proc_macro2::TokenStream;
use support::{Expansion, TestEnvironment, expand_tour_minimal};

/// Every expansion's kind and output, each nested invocation right after its
/// parent.
fn flatten(expansions: &[Expansion], output: &mut Vec<(&'static str, TokenStream)>) {
    for expansion in expansions {
        output.push((expansion.kind, expansion.output.clone()));
        let nested = expansion
            .nested
            .iter()
            .map(|(_, _, nested)| nested)
            .collect::<Vec<_>>();
        for nested in nested {
            flatten(std::slice::from_ref(nested), output);
        }
    }
}

fn tour_minimal_outputs() -> Vec<(&'static str, TokenStream)> {
    let (_, expansions) = expand_tour_minimal();
    let mut outputs = Vec::new();
    flatten(&expansions, &mut outputs);
    outputs
}

#[test]
fn tour_minimal_expands_in_a_fallback_process() {
    let outputs = tour_minimal_outputs();
    let kinds = outputs.iter().map(|(kind, _)| *kind).collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [
            FunctionMacro::Sorts.name(),
            AttributeMacro::Constructors.name(),
            AttributeMacro::Configuration.name(),
            AttributeMacro::Init.name(),
            FunctionMacro::K.name(),
            FunctionMacro::Rules.name(),
        ]
    );
    let outputs = outputs
        .into_iter()
        .map(|(_, output)| output)
        .collect::<Vec<_>>();
    let sorts = outputs[0].to_string();
    assert!(sorts.contains(":: k :: __krs_host_provenance (\"\" , const { const __KRS_AUTHORED"));
    assert!(sorts.contains("& :: k :: __KrsRawProvenance :: new (& [\"src/lib.rs\"]"));
    // `k::sorts! { ... }` spans 10:1 through 12:2 of the authored file.
    assert!(sorts.contains(
        ":: k :: __KrsRawAnchor :: new (0usize , false , (10u32 , 1u32) , (12u32 , 2u32) , true)"
    ));
    // The clause range ends on tokens `krs-syntax` re-quotes at the call site;
    // the environment locates them at `k::rules!`, so the nonce is rustc's
    // (native `krs emit-k` build of tour-minimal, display file `src/lib.rs`).
    assert!(
        outputs[5]
            .to_string()
            .contains("__krs_head_rule_sort_edc54d797361b2d2")
    );
    assert!(outputs.iter().all(|output| !output.is_empty()));
}

#[test]
fn every_builtin_token_island_expands_in_a_fallback_process() {
    let env = TestEnvironment::new(None);
    for (entry, input) in [
        (FunctionMacro::Id, "\"$x\""),
        (FunctionMacro::Bytes, "b\"\\x00\""),
        (FunctionMacro::Anonymous, ""),
        (FunctionMacro::OrBool, "a, b"),
    ] {
        let output = krs_expand::expand_function(entry, &env, input.parse().unwrap()).unwrap();
        assert!(output.to_string().contains("has no runtime value"));
    }
    let error =
        krs_expand::expand_function(FunctionMacro::Id, &env, "\"x\"".parse().unwrap()).unwrap_err();
    assert_eq!(error.to_string(), "invalid builtin `Id` token");
}

/// A failed `#[k::init]` leaves a stand-in for the payload function the
/// configuration names, under the method's `#[cfg]`, and nothing else; a
/// successful one emits no stand-in.
#[test]
fn a_failed_initializer_leaves_a_payload_stand_in() {
    let env = TestEnvironment::new(None);
    let failing = r#"
        #[cfg(feature = "machine")]
        pub fn init(pgm: Stmt) -> Self {
            Self { k: k::k![pgm], mem: k::anonymous!(Bytes, "_M") }
        }
    "#;
    let error = krs_expand::expand_attribute(
        AttributeMacro::Init,
        &env,
        TokenStream::new(),
        failing.parse().unwrap(),
    )
    .unwrap_err();
    let stand_in = error.stand_in().to_string();
    assert!(
        stand_in.starts_with("# [cfg (feature = \"machine\")] # [doc (hidden)] pub (crate) fn __krs_initializer_payload ()"),
        "{stand_in}"
    );
    assert!(stand_in.contains(":: core :: unreachable !"), "{stand_in}");
    assert!(!stand_in.contains("fn init"), "{stand_in}");
    let rendered = error
        .into_compile_error(proc_macro2::Span::call_site())
        .to_string();
    assert!(
        rendered.starts_with(":: core :: compile_error !"),
        "{rendered}"
    );
    assert!(rendered.ends_with(&stand_in), "{rendered}");

    let body_shape = r"
        pub fn init(pgm: Stmt) -> Self {
            let x = 1;
            Self { k: k::k![pgm] }
        }
    ";
    let error = krs_expand::expand_attribute(
        AttributeMacro::Init,
        &env,
        TokenStream::new(),
        body_shape.parse().unwrap(),
    )
    .unwrap_err();
    assert!(
        error
            .stand_in()
            .to_string()
            .starts_with("# [doc (hidden)] pub (crate) fn __krs_initializer_payload")
    );
}

#[test]
fn entry_point_names_round_trip() {
    for &entry in AttributeMacro::ALL {
        assert_eq!(AttributeMacro::from_name(entry.name()), Some(entry));
    }
    for &entry in FunctionMacro::ALL {
        assert_eq!(FunctionMacro::from_name(entry.name()), Some(entry));
    }
    assert_eq!(AttributeMacro::from_name("sorts"), None);
    assert_eq!(FunctionMacro::from_name("sort"), None);
}
