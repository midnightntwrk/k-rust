//! Re-pin R0c-fix-3 (`draft/tasks/repin-501f18b9`; decisions log 2026-10-17, "inconsistent
//! mutants"): kink-native's mutant consistency check (`consistency`), on k-rust's critical-pair
//! check, and the k-rust passages and source it rests on, pinned at 501f18b9. Re-pin R0c-fix-4:
//! the effect of an edit read from the compiled definitions, the source reading as a fail-closed
//! cross-check (`admit_mutant`), and the probe head shown on self and inner pairs.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust_backend::confluence::CheckScope;
use kink_native::consistency::{
    CompiledEquations, Inconsistency, MutantFailure, UnjoinedEquations, admit_mutant, check_heads,
};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::{ClaimSupport, Edit, Patch, SentenceOrigin, SourceEffect, TermRef};

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
    r0c("nomatch")
}

/// The validator of `testdata/k/r0c/<name>.k`, its main module the upper-cased name.
fn r0c(name: &str) -> NativeValidator {
    NativeValidator::bind(
        support::load_path(
            &root().join(format!("testdata/k/r0c/{name}.k")),
            &name.to_ascii_uppercase(),
        ),
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
            check_heads(&side, affected.as_ref()),
            Err(Inconsistency::Unjoined(vec![UnjoinedEquations {
                first: "NOMATCH.fpos".into(),
                second: "NOMATCH.fneg".into(),
                position: Vec::new(),
                reason: "the conditions are neither refuted nor enough to join".into(),
            }]))
        );
        // Every head (`None`, an edit whose effect is not known symbol by symbol) sees it too.
        assert!(check_heads(&side, None).is_err());
    });
}

/// Only the pairs of the symbols the edit can change are read: the baseline's own equations stay
/// a trusted premise. The baseline's guards are complementary, so its pair is refuted.
#[test]
fn the_check_reads_the_heads_the_edit_can_change() {
    on_a_big_stack(|| {
        let validator = nomatch();
        let compiled = validator.compile_baseline().unwrap();
        assert_eq!(check_heads(&compiled, None), Ok(()));
        let (side, _) = guard_mutant(&validator, "NOMATCH.fneg", "5");
        assert_eq!(check_heads(&side, Some(&BTreeSet::new())), Ok(()));
        assert_eq!(
            check_heads(&side, Some(&BTreeSet::from(["go".to_owned()]))),
            Ok(())
        );
        assert!(check_heads(&side, Some(&BTreeSet::from(["f".to_owned()]))).is_err());
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

/// The taint closure (`confluence/closure.rs`): `taintable`, which with `certified_root` decides
/// the early return the probe head turns off (an equation head is taintable), by digest (re-pin
/// R0c-fix-4, R0c-fix-3 review minor 4).
const CLOSURE_RS: &str = "d6fa4b4ccc257ab8ac99f1eaf2d1284a8ff44c57df46951fc819c343b22ca661";

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
    let closure = std::fs::read(backend.join("src/confluence/closure.rs")).unwrap();
    assert_eq!(kink_patch::sha256(&closure).to_string(), CLOSURE_RS);
}

/// Re-pin R0c-fix-4 (R0c-fix-3 review minor 4): the probe head makes k-rust classify a
/// definition's self pairs. `r0c/mapfun.k`'s `f((_K |-> V) _R) => V *Int 0` matches one map in
/// several ways and its result reads `V`; the definition declares no equation head, so without
/// the probe k-rust classifies no pair (no self pair counted, none reported), and with it the
/// self pair is reported. Inner pairs need no such test: an inner pair of two declared functions
/// needs a function symbol below the root of a left-hand side, which k-rust refuses to compile
/// (`r0c/inner.k`), and every other inner pair in a definition without an equation head or a
/// withdrawable overloaded symbol has an equation indexed at a constructor, an injection, a
/// collection or a variable, a precondition row k-rust reports before its early return. kink
/// reads such a row as refusing (`check`) when its equation is checked or the row names no
/// equation, and an `IndexedAt` row always; a constructor-headed or injection-headed row of an
/// unchecked equation does not refuse. k-rust classifies no overlap of such an equation
/// (`confluence.rs` `check_detached`), so one below the root of a checked equation's left-hand
/// side would be neither classified nor refused: a residual k-rust reading, like the unverified
/// DomainValue/And index (R0c-fix-4 deviations 2), which no K source is known to give (re-pin
/// R0-tail, R0c-fix-4 review minor 3).
#[test]
fn the_probe_head_makes_k_rust_classify_self_pairs() {
    on_a_big_stack(|| {
        let compiled = r0c("mapfun").compile_baseline().unwrap();
        let plain = kink_native::census::internalize(&compiled)
            .unwrap()
            .value_claims_in_scope(CheckScope::All);
        assert_eq!(plain.counts().pairs, 0);
        assert_eq!(plain.counts().several_matches, 0);
        assert!(plain.unjoined().is_empty(), "{:?}", plain.unjoined());
        let Err(Inconsistency::Unjoined(pairs)) = check_heads(&compiled, None) else {
            panic!("the probe head classifies the self pair")
        };
        assert!(
            pairs.iter().any(|pair| pair.first == "MAPFUN.f"
                && pair.second == "MAPFUN.f"
                && pair.reason.contains("several ways")),
            "{pairs:?}"
        );
        let refused = r0c("inner")
            .compile_baseline()
            .expect_err("a function symbol below the root");
        assert!(
            format!("{refused:?}").contains("below the root"),
            "{refused:?}"
        );
    });
}

/// Re-pin R0c-fix-4: the source reading is a fail-closed cross-check of the compiled
/// definitions. On `r0c/cfgf.k`, `fpos` (`[[ f(I) => 1 ]] <k> _ </k>`) compiles to an equation of
/// `f`; a source reading that redefines nothing (as kink-patch read such a rule at 25e229e) is
/// contradicted by the compiled equation of the touched sentence, so the effect is unread. With
/// kink-patch's reading (`f` redefined) the mutant is read and refused as inconsistent, and the
/// compiled diff alone (an empty source reading that touches no sentence) still checks `f`.
#[test]
fn a_compiled_equation_of_a_touched_sentence_must_be_redefined() {
    on_a_big_stack(|| {
        let validator = r0c("cfgf");
        let baseline = validator.baseline();
        let compiled = validator.compile_baseline().unwrap();
        let equations = CompiledEquations::of(&compiled).unwrap();
        let rule = support::rule(baseline, "CFGF.fpos");
        let at = TermRef::new(rule.clone(), [1, 1]);
        let expected = baseline.term(&at).expect("the guard literal").clone();
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            at,
            expected,
            replacement: Term::Token {
                token: "-5".into(),
                sort: Sort::new("Int"),
            },
        }])
        .unwrap();
        let support = ClaimSupport::new(baseline);
        let effect = support.effect(baseline, &patch).unwrap();
        assert_eq!(effect.redefined, Some(BTreeSet::from(["f".to_owned()])));
        let side = validator
            .validate(support.withdraw(baseline, &patch).unwrap().patch().unwrap())
            .unwrap();
        let misread = SourceEffect {
            redefined: Some(BTreeSet::new()),
            affected: Some(BTreeSet::new()),
            touched: effect.touched.clone(),
        };
        let Err(MutantFailure::UnreadEquations(unread)) = admit_mutant(&equations, &side, &misread)
        else {
            panic!("the compiled equation of fpos is unread")
        };
        assert!(
            unread.iter().any(|equation| equation.head == "Lblf"
                && equation.equation == "CFGF.fpos"
                && equation.origin == Some(SentenceOrigin::Baseline(rule.clone()))),
            "{unread:?}"
        );
        assert!(matches!(
            admit_mutant(&equations, &side, &effect),
            Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(_)))
        ));
        let compiled_only = SourceEffect {
            redefined: Some(BTreeSet::new()),
            affected: Some(BTreeSet::new()),
            touched: BTreeSet::new(),
        };
        assert!(matches!(
            admit_mutant(&equations, &side, &compiled_only),
            Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(_)))
        ));
        // The baseline against itself changes nothing and is admitted with nothing checked.
        let none = admit_mutant(&equations, &compiled, &compiled_only).unwrap();
        assert!(none.changed.is_empty(), "{none:?}");
        assert_eq!(none.checked, Some(BTreeSet::new()));
    });
}
