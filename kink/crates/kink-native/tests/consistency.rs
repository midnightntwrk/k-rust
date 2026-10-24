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
        // Re-pin probe P-1 (k-rust 58720d2e5; KINK-20/1, head d9e62128f, merge 879fce1cc; k-rust's
        // draft answers-add3 section 2.1 "Load of head-free definitions"): `CheckScope::All` now
        // classifies every pair of a definition with nothing withdrawable, so without the probe
        // head it pairs 11 (0 at 501f18b9) and reports the pair the edit breaks itself; the probe
        // head stays and gives the same verdict below.
        assert_eq!(claims.counts().pairs, 11);
        assert_eq!(claims.counts().unjoined, 1);
        assert_eq!(claims.unjoined().len(), 1);
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

/// The k-rust text the check's soundness rests on (file relative to the k-rust tree, first and
/// last line, sha256 of the lines joined by newlines). At 501f18b9: that `M_NF` is a model when
/// evaluation terminates and the critical pairs join (947); what the check classifies and how a
/// pair is separated, refuted, joined or not joined, and the stack-stop exclusion (970-975);
/// that `value_claims_in_scope(CheckScope::All)` runs the check of every pair and that a
/// definition without an equation head has no pair checked (991-1003); and the API's own
/// documentation (`definition.rs` 2905-2920).
///
/// Re-pin P-2 (k-rust 8f8ad57c5; KINK-20/1-3, heads d9e62128f and 0749cd518, merge 879fce1cc,
/// on main since 58720d2e5; k-rust's draft answers-add3 section 2.1 "Load of head-free
/// definitions" and "Fewer withdrawn claims / more refutations at load"; Sebastien's decision
/// draft/tasks/flow/decisions/human-decisions-2026-10-14.md, "2026-10-20: admit mutants whose
/// guards k-rust's KINK-20/3 refutes as disjoint", which accepts P-1's STOP 1 and names this pin
/// as its tripwire). The same passages, read again at 8f8ad57c5 (unchanged since 58720d2e5, only
/// moved by rounds 26-28's docs):
/// - 1061-1063: `M_NF` is a model, now read with the priority antecedent (an equation holds
///   only where no higher-priority group applies), which the emitted axioms leave implicit and
///   the evaluator, the join and the check all read.
/// - 1086-1092: a root pair is within one index and priority group; an overlap is separated
///   (no instance whose variables are normal forms), refuted by its conditions, now also by
///   the integer bounds of one-term comparisons with literals (`X >Int 5` beside `X <=Int 0`:
///   KINK-20/3, the cause of the cfgf admission), joined or not joined; and the evaluator's
///   instance order, passing to a lower group only when every instance is refuted.
/// - 1108-1121: the closure and relevance, `CheckScope::All` runs the check of every pair, the
///   new `ValueClaims::group_counts` paragraph, and that a head-free definition has no pair
///   checked under the load's scope while `CheckScope::All` checks its pairs all the same
///   (KINK-20/1).
/// - `definition.rs` 2901-2927: `value_claims_in_scope`, now stating that under
///   `CheckScope::All` every candidate pair is classified (`counts().skipped == 0`), which pairs
///   are formed, and that `separated`, `refuted` and `joined` are sound.
///
/// Re-pin P-1 (`draft/tasks/repin-0068938b`, k-rust 0068938b1): the four passages are
/// byte-identical to 8f8ad57c5's and only moved, compatibility.md's down 8 lines (round D's text
/// above them) and `definition.rs`'s down 32 (MLP/10's 7fec17247, FU-27, the sweep and the ks3
/// engine work); only the line numbers are re-pinned.
///
/// fz26 phase-5 integration (INT7): FZ-DATAEND's data-term paragraph (6 lines, "Anywhere
/// rules") moved the second and third compatibility.md passages down 6, byte-identical; only
/// their lines are re-pinned, by digest.
///
/// k-rust FZ-CONFLUENCE: the passage 1100-1106 changes in its line 1103, which states what
/// "refuted" reads: also a literal under `\not` only where its term is shown defined, difference
/// constraints between integer atoms with range facts, equality classes with literal
/// substitution, the cases of at most three disjunctions, and an overlap whose list or function
/// equation the unifier does not decide refuted at every solution without it. Each only refutes
/// more overlaps (or, for `\not` literals, fewer, where the old reading was unsound), so a mutant
/// is admitted only where its guards hold on no instance. The other passages are unmoved.
///
/// kink's check (probe head, `CheckScope::All`, the coverage guard) still rests only on these:
/// every verdict it reads is one of the four the text defines, and the widened refutation can
/// only admit a mutant whose guards share no integer.
const PREMISE_PASSAGES: [(&str, usize, usize, &str); 4] = [
    (
        "docs/compatibility.md",
        1069,
        1071,
        "21492a8b0fca47bf5bdea146350c650c1043731afee4cb07711db09b4d7d35c8",
    ),
    (
        "docs/compatibility.md",
        1100,
        1106,
        "00e7b87424c1ceb793e08c0d6c7ae1ab613779b4d7eea5a76752b1bc9d63e6cd",
    ),
    (
        "docs/compatibility.md",
        1122,
        1135,
        "6a3b482248576ca08648f5e2bfd7c0211ad147f43d433245a4044507b4de472c",
    ),
    (
        "crates/k-rust-backend/src/definition.rs",
        2926,
        2952,
        "231513b52fc26f915765b47abfb63789954e31ef4271986dd73f218f1ec9c8a0",
    ),
];

/// The check's driver (`confluence.rs`: the stages, `executable_equations`, the early return of
/// a definition with nothing withdrawable, the counts kink reads), by digest.
///
/// Re-pin P-2 (KINK-20/1-3, merge 879fce1cc; the 2026-10-20 decision above): 783482c9 at
/// 501f18b9 -> e84044b7 since 58720d2e5 (CheckScope::All pairs head-free definitions,
/// `GroupCounts`/`group_counts`, the integer-bound refutation); unchanged by rounds 26-28.
///
/// Re-pin P-1 (`draft/tasks/repin-0068938b`, k-rust 0068938b1): e84044b7 -> b68ae7c7. One
/// change, in `classify_inner`'s injected inner position: a subsort question that depends on a
/// sort variable (`check_subsort` answers `Err`) was read as "no overlap" (`Classified::Fine`)
/// and is now a pair not joined, `Unresolved(SortVariable)`; a decided `Ok(false)` is still fine
/// and the `drop_injected_inner` switch still drops the pair. Cause: the correctness sweep's
/// e988794ee, "Report an undecided match apart from a refutation" (CS-09-1; main fd3f80fe5,
/// merged into k-rust's round 33 at c51305fd4; result change RC-115 of k-rust
/// draft/k-in-k/answers-2026-10b.toml). It only turns a pair the check passed into one it
/// reports not joined, which kink reads as `inconsistent-mutant`: it can refuse a mutant, never
/// admit one, and closed sorts, the only ones kink's definitions have, never give the `Err`
/// (the commit message). No test's verdict moved.
///
/// Re-pin KS-08c (backend sorts become interned `Copy` handles): b68ae7c7 -> 7fb0ca97. Syntax only:
/// `Sort` patterns read `sort.node()` as `SortNode`, and sort clones become copies; no stage,
/// count or early return changes.
///
/// Re-pin FZ-CONFLUENCE (k-rust fz26/confluence): 7fb0ca97 -> b00877b8. The hook stage: each
/// executable equation at an evaluated hook is paired with the hook's written meaning, counted in
/// `CheckCounts::hook` apart from `pairs` (so the `counts().pairs` guard and pins hold), marked
/// `UnjoinedPair::hook` (which `check` reads for its first equation only) and seeding only that
/// equation into the closure; `UnmodelledHook` per-equation reports; the condition reader's
/// literal substitution and the unifier's deferral in `classify`. The stages, the early return and
/// the equation and skipped counts kink reads are unchanged.
///
/// Re-pin FZ-CONFLUENCE review fixes: b00877b8 -> 502e6d91. A hook pair is reported at load only
/// when it withdraws a claim (as the load classifies only relevant equations' hook pairs), and the
/// literal substitution moved into `conditions.rs` (`refuted_by_literals`). No stage, count or
/// early return kink reads changes.
const CONFLUENCE_RS: &str = "502e6d919e721ed174c252597fed2641436f640b4df7a2a0f97043a723b5da6a";

/// The taint closure (`confluence/closure.rs`): `taintable`, which with `certified_root` decides
/// the early return the probe head turns off (an equation head is taintable), by digest (re-pin
/// R0c-fix-4, R0c-fix-3 review minor 4). Re-pin KS-08c: d6fa4b4c -> 37bed07e, the same syntax-only
/// change of its sort patterns as `CONFLUENCE_RS`.
const CLOSURE_RS: &str = "37bed07ece2d17afb4b1098566ee484167e244ed01104fe07d98d4cbf3df5c95";

/// A re-pin that changes the premise text or the check's driver needs the consistency check
/// (and its probe head) read again against it.
#[test]
fn the_premise_k_rust_documents_is_pinned() {
    let manifest: toml::Value =
        toml::from_str(&std::fs::read_to_string(root().join("../Cargo.toml")).unwrap()).unwrap();
    // kink is a part of k-rust's workspace (merge packet M-1): the manifest is k-rust's root one.
    let backend = root().join("..").join(
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
        // Re-pin probe P-1 (k-rust 58720d2e5; KINK-20/1, head d9e62128f, merge 879fce1cc; k-rust's
        // draft answers-add3 section 2.1 "Load of head-free definitions"): without the probe head
        // `CheckScope::All` now pairs 10 (0 at 501f18b9), counts the self pair's several matches
        // and reports it; the probe head stays and gives the same verdict below.
        assert_eq!(plain.counts().pairs, 10);
        assert_eq!(plain.counts().several_matches, 1);
        assert_eq!(plain.unjoined().len(), 1, "{:?}", plain.unjoined());
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

mod kink_tier {
    use super::*;

    /// Re-pin R0c-fix-4: the source reading is a fail-closed cross-check of the compiled
    /// definitions. On `r0c/cfgf.k`, `fpos` (`[[ f(I) => 1 ]] <k> _ </k>`) compiles to an equation of
    /// `f`; a source reading that redefines nothing (as kink-patch read such a rule at 25e229e) is
    /// contradicted by the compiled equation of the touched sentence, so the effect is unread. With
    /// kink-patch's reading (`f` redefined) the mutant is read and refused as inconsistent, and the
    /// compiled diff alone (an empty source reading that touches no sentence) still checks `f`.
    #[test]
    #[ignore = "kink"]
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
            let Err(MutantFailure::UnreadEquations(unread)) =
                admit_mutant(&equations, &side, &misread)
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

    /// Only the pairs of the symbols the edit can change are read: the baseline's own equations stay
    /// a trusted premise. The baseline's guards are complementary, so its pair is refuted.
    #[test]
    #[ignore = "kink"]
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
}
