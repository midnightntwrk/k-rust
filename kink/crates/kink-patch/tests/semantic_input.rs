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
///
/// Re-pin GAP A0 (k-rust docs/amendments.md): both digests moved again. In the prelude, the two
/// rules of domains.md's `INT-SYMBOLIC-KORE` and the two regex lines of kast.md's
/// `DEFAULT-LAYOUT` end with a `// k-rust: AM-<n>` comment, and kast.md's paragraph before
/// that module moved into amendment AM-9, so the prelude sentences after them start at other
/// offsets and the kast.md ones after the paragraph five lines earlier; no sentence changed. With
/// the two builtin files as before every old digest here comes back, and the compiled KORE below
/// is unchanged.
///
/// Re-pin GAP AM-12 (k-rust docs/amendments.md): both digests moved again. Three definedness
/// rules (of `^Int`, `^%Int` and `log2Int`, marked `// k-rust: AM-12`) follow AM-10's in the
/// prelude's `INT-SYMBOLIC-KORE`: the semantic input and the KAST definition carry the three
/// sentences, and every prelude sentence after them is three lines and their bytes later. No
/// other sentence changed, and the user modules are equal.
///
/// Re-pin GAP W8a (k-rust docs/amendments.md): both digests moved again. The five definedness
/// rules of AM-10 and AM-12 moved, unchanged, out of the prelude's `INT-SYMBOLIC-KORE` into a
/// module `INT-SYMBOLIC-KORE-AMENDMENTS` after domains.md's last line, which `INT-SYMBOLIC-KORE`
/// imports: the KAST definition carries the new module and the import, the five sentences are at
/// their new lines, and every prelude sentence after line 1394 is five lines, and their bytes,
/// earlier. No sentence changed, and the user modules are equal.
#[test]
fn literal_digests() {
    for (name, artifact, structure) in [
        (
            "counter.k",
            "32d348cc87eb71adac6198a1f598fdd20c6232b712a040570d59332960a9b5cc",
            "a2362c75a59d5846c0dec0f793d2de2f16fd4675a9419ab94e953ec8a49333ba",
        ),
        (
            "symmem.k",
            "cadb09037a76948c11e8a1bee1b6a1e4073e0ee1da05d3cb6cb86b70cb3b8393",
            "4eb58cd93acecaa668038a7d515a0cdb2c95754a1641e27e6cee545559f27378",
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
///
/// Re-pin GAP AM-12: the compiled KORE moved with the three `#Ceil` rules AM-12 adds to
/// `INT-SYMBOLIC-KORE` (three more axioms) and the source locations of the prelude sentences after
/// them; the read-back still compiles to equal artifacts.
///
/// Re-pin GAP W8a: the compiled KORE moved with the five `#Ceil` rules of AM-10 and AM-12 moving
/// to a module after domains.md's last line: the same axioms, the five at their new locations and
/// ahead of `INT-SYMBOLIC-KORE`'s own (the imported module's sentences come first), and every
/// prelude sentence after line 1394 at a location five lines earlier; no axiom and no KORE module
/// was added or changed otherwise, and the read-back still compiles to equal artifacts.
#[test]
fn compiled_kore_is_unchanged_by_the_provenance_move_and_by_a_read_back() {
    for (name, kore) in [
        (
            "counter.k",
            "0d18db45c057e6d07f8c65949d64621e91428e817f97c7e92a3a5cd0c97b27e3",
        ),
        (
            "symmem.k",
            "e17db9dfe69a209f3e40130a1462d4e1ead24ac49f168886960fce03eaf0d098",
        ),
        (
            "guardedmem.k",
            "ce5cfbd6f45f4a97306343958ec088220d8fd2a910bc2d56edcf05742c3b44f2",
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
