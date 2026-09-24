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
    assert!(sorts.contains(":: k :: HostSourceAnchor :: new (\"src/lib.rs\" . to_owned ()"));
    // `k::sorts! { ... }` spans 10:1 through 12:2 of the authored file.
    assert!(sorts.contains(
        ":: k :: HostSourcePosition :: new (10u32 , 1u32) . expect (\"stable proc-macro positions are one-based\") , :: k :: HostSourcePosition :: new (12u32 , 2u32)"
    ));
    assert!(sorts.contains(":: k :: AnchorPrecision :: Exact"));
    // The clause range ends on tokens `krs-syntax` re-quotes at the call site;
    // the environment locates them at `k::rules!`, so the nonce is rustc's
    // (native `krs emit-k` build of tour-minimal, display file `src/lib.rs`).
    assert!(
        outputs[5]
            .to_string()
            .contains("__krs_head_rule_sort_2cb94a8d9d940990")
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

/// Compares the fallback expansion of every tour-minimal invocation with a
/// native per-invocation capture, token for token.
///
/// `KRS_NATIVE_CAPTURE` names a JSON Lines capture whose rows carry `crate`,
/// `file`, `line`, `column`, and rustc's `output` text; the rows of
/// `krs_tour_minimal` with display file `src/lib.rs` (the `krs emit-k`
/// collector build) are compared. rustc's `Display` differs from the
/// `proc_macro2` fallback `Display`, so the native text is re-lexed through
/// `proc_macro2` before the token strings are compared.
#[test]
#[ignore = "needs a native capture; set KRS_NATIVE_CAPTURE"]
fn tour_minimal_matches_the_native_capture() {
    let path = std::env::var("KRS_NATIVE_CAPTURE").expect("KRS_NATIVE_CAPTURE names a capture");
    let capture = std::fs::read_to_string(&path).expect("the native capture is readable");
    let mut rows = capture
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("a JSON capture row"))
        .filter(|row| row["crate"] == "krs_tour_minimal" && row["file"] == "src/lib.rs")
        .collect::<Vec<_>>();
    rows.sort_by_key(|row| (row["line"].as_u64(), row["column"].as_u64()));
    let outputs = tour_minimal_outputs();
    assert_eq!(rows.len(), outputs.len(), "one native row per invocation");
    for (row, (_, output)) in rows.iter().zip(&outputs) {
        let native: TokenStream = row["output"]
            .as_str()
            .expect("a captured output")
            .parse()
            .expect("native output lexes");
        assert_eq!(
            native.to_string(),
            output.to_string(),
            "invocation at {}:{}",
            row["line"],
            row["column"]
        );
    }
}
