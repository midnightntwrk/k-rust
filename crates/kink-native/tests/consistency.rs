//! Re-pin R0c-fix-3 (`draft/tasks/repin-501f18b9`; decisions log 2026-10-17, "inconsistent
//! mutants"): kink-native's mutant consistency check (`consistency`), on k-rust's critical-pair
//! check, and the k-rust passages and source it rests on, pinned at 501f18b9.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust_backend::confluence::CheckScope;
use kink_native::consistency::{Inconsistency, UnjoinedEquations, mutant_consistency};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{ClaimSupport, Edit, Patch, TermRef};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

fn nomatch() -> NativeValidator {
    NativeValidator::bind(
        support::load_path(&root().join("testdata/k/r0c/nomatch.k"), "NOMATCH"),
        CompileOptions::default(),
    )
}

/// The claim-free mutant (and the symbols its edit can change) that replaces the only `Int`
/// token of `rule`'s condition by `to`.
fn guard_mutant(
    validator: &NativeValidator,
    rule: &str,
    to: &str,
) -> (ValidatedDefinition, Option<BTreeSet<String>>) {
    let baseline = validator.baseline();
    // `f(I) => _ requires I <op> 0`: the condition's second argument is the literal.
    let at = TermRef::new(support::rule(baseline, rule), [1, 1]);
    let expected = baseline.term(&at).expect("the guard literal").clone();
    assert!(
        matches!(expected.unannotated(), Term::Token { token, .. } if token == "0"),
        "{expected}"
    );
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        at,
        expected,
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    let support = ClaimSupport::new(baseline);
    let withdrawal = support.withdraw(baseline, &patch).unwrap();
    let side = validator
        .validate(withdrawal.patch().expect("f's total is removed"))
        .unwrap();
    (side, support.affected(baseline, &patch).unwrap())
}

/// k-rust's check pairs nothing in a definition that declares no equation head and no
/// withdrawable overloaded symbol (`compatibility.md`, "has no pair checked"), in either scope;
/// kink's checked copy adds one equation head, so the pair the edit breaks is classified.
#[test]
fn the_probe_head_makes_k_rust_check_every_pair() {
    on_a_big_stack(|| {
        let validator = nomatch();
        let (side, affected) = guard_mutant(&validator, "NOMATCH.fpos", "-5");
        assert_eq!(affected, Some(BTreeSet::from(["f".to_owned()])));
        let plain = kink_native::census::internalize(&side).unwrap();
        let claims = plain.value_claims_in_scope(CheckScope::All);
        assert_eq!(claims.counts().pairs, 0);
        assert!(claims.unjoined().is_empty());
        assert_eq!(
            mutant_consistency(&side, affected.as_ref()),
            Err(Inconsistency::Unjoined(vec![UnjoinedEquations {
                first: "NOMATCH.fpos".into(),
                second: "NOMATCH.fneg".into(),
                position: Vec::new(),
                reason: "the conditions are neither refuted nor enough to join".into(),
            }]))
        );
        // Every head (`None`, an edit whose effect is not known symbol by symbol) sees it too.
        assert!(mutant_consistency(&side, None).is_err());
    });
}

/// Only the pairs of the symbols the edit can change are read: the baseline's own equations stay
/// a trusted premise. The baseline's guards are complementary, so its pair is refuted.
#[test]
fn the_check_reads_the_heads_the_edit_can_change() {
    on_a_big_stack(|| {
        let validator = nomatch();
        let compiled = validator.compile_baseline().unwrap();
        assert_eq!(mutant_consistency(&compiled, None), Ok(()));
        let (side, _) = guard_mutant(&validator, "NOMATCH.fneg", "5");
        assert_eq!(mutant_consistency(&side, Some(&BTreeSet::new())), Ok(()));
        assert_eq!(
            mutant_consistency(&side, Some(&BTreeSet::from(["go".to_owned()]))),
            Ok(())
        );
        assert!(mutant_consistency(&side, Some(&BTreeSet::from(["f".to_owned()]))).is_err());
    });
}

/// The k-rust text the check's soundness rests on, at 501f18b9 (file relative to the k-rust
/// tree, first and last line, sha256 of the lines joined by newlines): that `M_NF` is a model
/// when evaluation terminates and the critical pairs join (947); what the check classifies and
/// how a pair is separated, refuted, joined or not joined, and the stack-stop exclusion
/// (970-975); that `value_claims_in_scope(CheckScope::All)` runs the check of every pair and
/// that a definition without an equation head has no pair checked (991-1003); and the API's own
/// documentation (`definition.rs` 2905-2920).
const PREMISE_PASSAGES: [(&str, usize, usize, &str); 4] = [
    (
        "docs/compatibility.md",
        947,
        947,
        "2bf37af71b589f828da5b8887b364c64bc688ee4f3a94db5b89b3b5e921344e3",
    ),
    (
        "docs/compatibility.md",
        970,
        975,
        "b5ee8d2e9a3e55226a715b0948e7d6e4d3af4e3da04df17f8902f0f3435e2d67",
    ),
    (
        "docs/compatibility.md",
        991,
        1003,
        "69d7ed18b800f355273e606e9d0d98f74377deaec6076a57040104fe4c587667",
    ),
    (
        "crates/k-rust-backend/src/definition.rs",
        2905,
        2920,
        "c94f4d90c7e189bb7ac1c569d678b68e67363e4d0389b2dfb3c3109de5f01cf9",
    ),
];

/// The check's driver (`confluence.rs`: the stages, `executable_equations`, the early return of
/// a definition with nothing withdrawable, the counts kink reads), by digest.
const CONFLUENCE_RS: &str = "783482c9226a04ad9c59542c89f6863582af4f70fb10b88058f9cd2d16698861";

/// A re-pin that changes the premise text or the check's driver needs the consistency check
/// (and its probe head) read again against it.
#[test]
fn the_premise_k_rust_documents_is_pinned() {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("Cargo.toml")).unwrap()).unwrap();
    let backend = root().join(
        manifest["workspace"]["dependencies"]["k-rust-backend"]["path"]
            .as_str()
            .expect("k-rust-backend is a path dependency"),
    );
    let k_rust = backend.join("../..");
    for (file, first, last, digest) in PREMISE_PASSAGES {
        let text = std::fs::read_to_string(k_rust.join(file)).unwrap();
        let lines = text.split('\n').collect::<Vec<_>>();
        let passage = lines[first - 1..last].join("\n");
        assert_eq!(
            kink_patch::sha256(passage.as_bytes()).to_string(),
            digest,
            "{file} {first}-{last}"
        );
    }
    let source = std::fs::read(backend.join("src/confluence.rs")).unwrap();
    assert_eq!(kink_patch::sha256(&source).to_string(), CONFLUENCE_RS);
}
