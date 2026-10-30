#[path = "../../../testdata/k/support.rs"]
mod support;

use kink_patch::{SemanticInput, SemanticInputError, structure_sha256};

/// Re-pin R0a (finding E-07; k-rust 67b9f5c54 "write KRUST-PROVENANCE version 8"): the semantic
/// input is KRUST-PROVENANCE version 8 at k-rust 501f18b9 (version 7 at 927b9ce6: an `anchors`
/// table and interned origin-set sources), so its digests moved: counter.k from f997509e...,
/// symmem.k from a554dced.... The structure digests (the KAST definition JSON) moved too, from
/// 4af7e670... and 87957ecd...: measured against 927b9ce6, the two JSON documents are equal except
/// for source positions of the builtin Markdown sentences (locations, sentence offsets, content
/// starts and origin ranges: the extraction's offset map is the identity, k-rust 50c5812cb,
/// bdad0af15, 760930379, finding E-09) and the two default-layout regexes of builtin kast.md
/// (k-rust df11bc569, 4df229f70); the user modules are equal. The compiled KORE is unchanged
/// (`compiled_kore_is_unchanged_by_the_provenance_move`).
///
/// Re-pin R1-PINS (kink27): both digests moved again with k-rust 0da031036, which added two
/// definedness rules to the prelude's domains.md: the semantic input and the KAST definition
/// carry the prelude's sentences and their positions. With domains.md as before 0da031036 (and
/// nothing else reverted) every old digest here comes back, so no other change reaches them; the
/// compiler change 68e362935 cannot, since both are read before compilation.
#[test]
fn literal_digests() {
    for (name, artifact, structure) in [
        (
            "counter.k",
            "62a4040f3541ac0103c4ecf81f6a5236d9af8308aabd4a098ac5465fa2d13076",
            "5f79568049266724077205cf15b6b072fdc77df041b3bc55fb82f5b495a29c96",
        ),
        (
            "symmem.k",
            "67492253f7d2e31d8a5c4b887460b640767c3574afad5f719d0b570bedd7871e",
            "3e0f4593cdab0530587e9832ec5adc1b7d7d556d44124cc7e7602149a54e906a",
        ),
    ] {
        let baseline = support::load(name);
        assert_eq!(
            SemanticInput::of(&baseline).unwrap().digest().to_string(),
            artifact,
            "{name}"
        );
        assert_eq!(
            structure_sha256(baseline.definition()).unwrap().to_string(),
            structure,
            "{name}"
        );
    }
}

/// Re-pin R0a (finding E-07): the semantic-input digests moved with the provenance format, but
/// what compilation emits did not. These are the SHA-256 digests of `definition_kore` measured at
/// k-rust 927b9ce6 (stage-1 trial, scratch-E/dump-old); 501f18b9 compiles the same bytes. The
/// definition read back from its semantic input compiles to artifacts equal to the original's
/// (formerly `read_back_compilation_is_equal`, which compiled the same three definitions).
///
/// Re-pin R1-PINS (kink27): the compiled KORE moved with k-rust 0da031036 (two `#Ceil` rules
/// of domains.md's `INT-SYMBOLIC-KORE`) and 68e362935 (each generated sort projection's
/// equation now comes with its exact domain and its conditional inverse, `<id>.selector-domain`
/// and `<id>.selector-inverse`). With domains.md as before 0da031036 and the selector contracts
/// not emitted, every old digest here comes back, so no other change reaches them.
#[test]
fn compiled_kore_is_unchanged_by_the_provenance_move_and_by_a_read_back() {
    for (name, kore) in [
        (
            "counter.k",
            "6e47a5d098ce9b14065010722cdc40d6d031a021142070bd3c7228e718f73f16",
        ),
        (
            "symmem.k",
            "ca2066a0b01fde0634ca211822ad850185f2f483f8890512158425758ca012c1",
        ),
        (
            "guardedmem.k",
            "1f1b3a5b479abc3fa1136edbcc835ec4770ab0746db510246b27286734e19a52",
        ),
    ] {
        let baseline = support::load(name);
        let artifacts = support::compile(baseline.loaded()).expect("compiles");
        assert_eq!(
            kink_patch::sha256(artifacts.definition_kore.as_bytes()).to_string(),
            kore,
            "{name}"
        );
        let (_, read) = SemanticInput::read(SemanticInput::of(&baseline).unwrap().text()).unwrap();
        assert_eq!(
            artifacts,
            support::compile(read.loaded()).unwrap(),
            "{name}"
        );
    }
}

#[test]
fn checks_canonical_form_and_changed_token_identity() {
    let baseline = support::load("counter.k");
    let pretty = k_rust::definition::json::to_provenance_string_pretty(
        baseline.definition(),
        baseline.loaded().source_table(),
    )
    .unwrap();
    assert_eq!(
        SemanticInput::read(&pretty).unwrap_err(),
        SemanticInputError::NonCanonical
    );
    let input = SemanticInput::of(&baseline).unwrap();
    let unknown_node = input
        .text()
        .replacen(r#""node":"KToken""#, r#""node":"KTokn""#, 1);
    assert_ne!(unknown_node, input.text());
    assert!(matches!(
        SemanticInput::read(&unknown_node),
        Err(SemanticInputError::Decode(_) | SemanticInputError::NonCanonical)
    ));
    let changed = input
        .text()
        .replacen(r#""token":"true""#, r#""token":"false""#, 1);
    assert_ne!(changed, input.text());
    let (changed_input, _) = SemanticInput::read(&changed).unwrap();
    assert_ne!(changed_input.digest(), input.digest());
}

#[test]
fn canonical_json_keys_are_sorted() {
    assert_eq!(
        serde_json::to_string(&serde_json::json!({"b":1,"a":2})).unwrap(),
        r#"{"a":2,"b":1}"#
    );
}
