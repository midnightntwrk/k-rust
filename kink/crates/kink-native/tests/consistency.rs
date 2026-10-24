//! Re-pin R0c-fix-3 (`draft/tasks/repin-501f18b9`; decisions log 2026-10-17, "inconsistent
//! mutants"): kink-native's mutant consistency check (`consistency`), on k-rust's critical-pair
//! check, and the k-rust passages and source it rests on, pinned at 501f18b9. Re-pin R0c-fix-4:
//! the effect of an edit read from the compiled definitions, the source reading as a fail-closed
//! cross-check (`admit_mutant`), and the probe head shown on self and inner pairs.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use k_rust::kast::{Label, Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust_backend::confluence::CheckScope;
use kink_native::consistency::{
    CompiledEquations, Inconsistency, MutantFailure, UnjoinedEquations, admit_mutant, check_heads,
    loaded_definition,
};
use kink_native::data::DataFacts;
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

/// The full check of `side` on kink's route, no name assumed: what the gate reads of a side.
fn facts(side: &ValidatedDefinition) -> DataFacts {
    DataFacts::of(&loaded_definition(side).unwrap(), &[])
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
/// fz26 phase-6 integration (INT8, FZ-EMPTYSORT with FZ-CONFLUENCE and FZ-POLISH): three passages
/// change, by digest of the final merged text. compatibility.md 1100-1107 (was 1100-1106): line
/// 1103 no longer lists "separated" among an overlap's outcomes, and a new line 1104 states that
/// no overlap is set aside because a variable of it ranges over a sort with no normal form: every
/// model has an element of that sort, so such an overlap is refuted, joined or not joined like
/// any other, and a pair whose non-joined overlaps are all over such sorts is listed (naming the
/// sort) but withdraws no claim. compatibility.md 1123-1136 (was 1122-1135) moved down one line
/// and its `group_counts` sentence counts overlaps over sorts with no normal form where it
/// counted separated ones. `definition.rs` 2926-2953 (was 2926-2952) says that `refuted` and
/// `joined` are sound, no overlap being set aside for an empty sort, where it said `separated`,
/// `refuted` and `joined`. The check only gets stricter for kink: a mutant with such a pair, which
/// the check used to separate, is now refused as `inconsistent-mutant`; no mutant is newly
/// admitted. INT8 follow-up: line 1104's account of why such a pair withdraws no claim now
/// argues from the readers of the simplifier's mark (an overloaded partial function's marked
/// application is never read as a value, and what is decided from a parent over it holds under
/// its definedness) where it stated that case as a limit: 1100-1107 `a83fde62` -> `3af0cfea`.
/// No verdict of the check changes.
///
/// fz26 phase-8 FZ-EMPTYJOIN-WITNESS: all four passages change, by digest; their line ranges stay
/// but `definition.rs`'s, which grows three lines (2926-2956). "Joined" now means joined by
/// steps of the executable equations and the witness equations the full check adopts, in the
/// model `M+` that adds a fresh constant to every sort not surely inhabited (1100-1107: line 1103
/// says so, line 1104 states how witnesses are proposed, validated by a second pass on `R ∪ W`
/// and adopted). The premise (1069-1071) is now that `M+` is a model when `R ∪ W` terminates
/// innermost over the added constants (A1+, a new premise k-rust does not check, which implies
/// A1 but is not implied by it) and the pairs of `R ∪ W` join; kink's quotation of the premise
/// (`consistency.rs`, module documentation, and the README) reads `M+` and A1+ since fz26
/// KINK-WITNESS, which moves no passage. 1125 (in 1123-1136) reads
/// the claims' model with the untainted equations of `R ∪ W`, and `definition.rs` restates
/// "joined" and A1+. For kink: a pair over a sort with no normal form that joins only through an
/// adopted witness is no longer listed, so such a mutant can be admitted (admission widens), and
/// an adoption can flip between baseline and mutant, which KINK-WITNESS diffs.
///
/// fz26 phase-8 FZ-CONFLUENCE-F: 1100-1107 changes, by digest (3483b03d -> 5b52aef7). Line 1103
/// adds two ways the join closes a case it split off, each because the case has no instance at
/// which both conditions hold: a case whose two `requires`, read again under the substitution
/// that made it, are refuted (F1), and the complement of a split whose cases bind one variable to
/// each constructor of a sort whose every element in `M+` is such an application (F2: surely
/// inhabited, no proper subsort, neither hooked nor a collection, no domain values, and no symbol
/// of the sort but its constructors and unhooked partial functions; `KEQUAL.ite` counts as
/// another symbol, so a definition declaring K's `ite{S}` drops no complement); such a pair is
/// joined. "Joined" keeps its meaning (steps of `R ∪ W` valid on the instances the lifting lemma
/// ranges over, in `M+`); the check shows more pairs joined, so kink can admit more mutants: on
/// KEVM the six `#hashTxData` pairs (`serialization.md:193-196`) now join by F1. Line 1104's WASM
/// count stays four.
///
/// fz26 phase-8 FZ-EMPTYJOIN-CLAIMS: 1100-1107 and 1123-1136 change, by digest; no line moves.
/// Line 1104: a pair over a sort with no normal form withdraws claims and is named at load like
/// any other pair (it withdrew nothing and was not named, the claims being read in `M_NF`); the
/// reason naming the sort is a label. Line 1130: the warnings both scopes give alike include
/// those of such pairs. Line 1120 (outside these passages) reads the claims' models with
/// nonempty carriers. For kink: the full check lists exactly the pairs it listed, so no verdict
/// moves through the listing; an adoption of witnesses can now flip, since adoption condition 4
/// reads a closure that such pairs now seed (`CONFLUENCE_RS`).
///
/// fz26 phase-8 FZ-MAPKEY: line 1102 (how a pair is unified) gains, on the same line, that two
/// maps are unified at every key written alike on both sides, value with value and rest with
/// rest, and clash when one has no rest and fewer entries than the other: a map binds a key
/// once, and `n` explicit entries are `n` distinct keys, exactly `n` without a rest. The unifier
/// only decides more map equations, so more overlaps are separated or refuted and a mutant whose
/// map-keyed equations that separates is admitted (`MUTANT_CONSISTENCY_VERSION` is bumped at
/// integration). No line moves: 1100-1107 `3af0cfea` -> `7deefbc9`.
///
/// k-rust FZ-MEMBERSHIP: line 1103 of 1100-1107 adds membership literals to what "refuted"
/// reads (`3af0cfea` -> `933b39db`): an item required in sorts with no common lower bound, or
/// outside a sort above each of their maximal common lower bounds, by the predicates whose two
/// equations make them a sort's membership predicates, in the models that also satisfy
/// injection composition and no confusion between injections from incomparable sorts. The
/// normal-form model kink's premise builds satisfies both (`Term::injection` composes chains, and
/// injections from incomparable sorts are distinct normal forms), so a mutant newly admitted has
/// guards that hold on no normal-form instance. Only more overlaps are refuted; the other
/// passages are unmoved.
///
/// k-rust S2B-T2 (collection membership): line 1103 of 1100-1107 adds collection memberships to
/// what "refuted" reads (`933b39db` -> `3e1072d3`): a membership required true or false in a
/// list without middle, a set or map without rest, or the values or keys of a map without rest
/// is read as the equalities between the element and the members (their disjunction when
/// required true, each negated when required false), each implied wherever the membership is
/// defined, and a conjunction is refuted when it is refuted with or without them. Only more
/// overlaps are refuted; the other passages are unmoved.
///
/// fz26 int9 (FZ-MAPKEY, FZ-MEMBERSHIP, S2B-T2, FZ-EMPTYJOIN-WITNESS, FZ-EMPTYJOIN-CLAIMS and
/// FZ-CONFLUENCE-F merged): line 1102 carries FZ-MAPKEY's map sentence; line 1103 FZ-MEMBERSHIP's
/// and S2B-T2's clauses, FZ-CONFLUENCE-F's two ways a split case is closed and, at its end,
/// FZ-EMPTYJOIN-WITNESS's sentence reading "joined" in `M+`; line 1104 the witness proposal with
/// FZ-EMPTYJOIN-CLAIMS's withdrawal; 1130 FZ-EMPTYJOIN-CLAIMS's warnings; each as its branch wrote
/// it, no line moved, except that 1103's KEVM example now says the six `#hashTxData` pairs are
/// refuted by the membership literals before any join (the conditions are read before the join, so
/// on the merged check F1 no longer removes them; it would close each split case alone). Re-pinned
/// by digest of the merged texts: 1100-1107 -> `d519755a`; 1069-1071 (`a350602f`), 1123-1136
/// (`64b22da3`) and `definition.rs` 2926-2956 (`3b520509`) are as the branches pinned them.
///
/// fz26 INT9-FIX-DOCS (review CHKB-3): line 1104 now also says that the load checks again that
/// the closure of its own second pass withdraws no witness head, and otherwise keeps its own first
/// pass, with no witness (`confluence.rs`, `witness::heads_untainted`), which `CONFLUENCE_RS`
/// already pinned in the code. kink reads the full check (`CheckScope::All`), not the load, so no
/// reading of kink's moves. Re-pinned by digest: 1100-1107 -> `16798fc0`; no line moved.
///
/// kink's check (probe head, `CheckScope::All`, the coverage guard) still rests only on these:
/// every verdict it reads is one of the four the text defines, and the widened refutation can
/// only admit a mutant whose guards share no integer.
const PREMISE_PASSAGES: [(&str, usize, usize, &str); 4] = [
    (
        "docs/compatibility.md",
        1069,
        1071,
        "a350602f04b9a4d28ae88fa10bfe57340bcfe3f0f19a9260c9e926ac80f00e25",
    ),
    (
        "docs/compatibility.md",
        1100,
        1107,
        "16798fc021e1c3b22eee935971f2c7fcbfdddb5af1771ee22bdd0929d7d58bf1",
    ),
    (
        "docs/compatibility.md",
        1123,
        1136,
        "64b22da342b8e31eb42497885315d42af3fba138e6315797d46870ab2a47d202",
    ),
    (
        "crates/k-rust-backend/src/definition.rs",
        2926,
        2956,
        "3b5205091a3683ba0d694b1a136cef303abb250984fce1be15d3710769e4ffbe",
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
///
/// Re-pin FZ-CONFLUENCE review A round 2: 502e6d91 -> 7bddeac5. The hook stage passes the
/// equation's right-hand side to `hooks::meaning` (which of several equal `replace` symbols the
/// `replaceAll` lemma names), and `reported()`'s documentation cites the gate decision.
///
/// Re-pin fz26 phase-6 integration (INT8: FZ-CONFLUENCE merged with FZ-EMPTYSORT and
/// FZ-POLISH), by digest of the merged file: 7bddeac5 -> 286e86d7. FZ-EMPTYSORT: no overlap is
/// separated by an uninhabited sort (`vacuous` is gone, `CheckCounts::separated` is
/// `CheckCounts::uninhabited`, also counted for hook pairs in `HookCounts::uninhabited`); every
/// overlap of a pair is classified, and a pair whose non-joined overlaps are all over sorts with
/// no normal form is listed as `UnjoinedReason::UninhabitedSort` and seeds nothing into the
/// closure. FZ-POLISH: `Conditions::Holds` keeps `DifferentResults` where a pair's conditions
/// simplify to true, and `UnjoinedPair::conditions` records the simplified conjunction. The
/// stages, the early return, the hook stage and the equation, pair and skipped counts kink reads
/// are unchanged; a not-joined pair stays not joined (only reasons move), and a pair over an
/// empty sort that was separated is now listed, so kink can only refuse more mutants.
///
/// INT8 follow-up: 286e86d7 -> c9fa00d8. Documentation only: `Context::uninhabited_sort`'s
/// account of the simplifier's mark argues from its readers where it stated the overloaded
/// partial function as a limit.
///
/// Re-pin FZ-MEMBERSHIP (k-rust fz26/membership): c9fa00d8 -> b19c2538. The contract's list of
/// axioms read as true adds injection composition and no confusion between injections, and
/// `refuted` is stated over the models of that list; `Context` reads the definition's membership
/// predicates once (`conditions::memberships`) and passes them to the condition reader. The
/// stages, the early return and the counts kink reads are unchanged; `refuted` can only grow.
///
/// fz26 phase-8 FZ-JUNK-ORACLE: c9fa00d8 -> c74b0eb3. The classification of an overlap over a
/// sort with no normal form reads the test-only switch `separate_uninhabited`, which outside
/// test builds is the constant `false` (`switches::active`): no verdict kink reads changes.
///
/// fz26 phase-8 FZ-EMPTYJOIN-WITNESS: c74b0eb3 -> 4d58d09a. The check runs in passes
/// (`check_detached` over `check_pass`): a first pass proposes witness equations from the
/// non-joined overlaps over sorts with no normal form of the pairs the load's scope classifies;
/// when it proposes, the full check's second pass on `R ∪ W` is adopted under the conditions of
/// `witness.rs` (every proposing and witness pair joins, no pair is lost, fewer stay unjoined, no
/// witness head tainted), and the load takes that decision and runs its own second pass. The
/// stages, the early return and the guards kink reads keep their meaning: `counts().equations`
/// counts the definition's executable equations only (witnesses are `counts().witnesses`),
/// `pairs` counts witness pairs too (so `pairs >= root pairs` still holds), and `skipped` stays
/// 0 under `CheckScope::All`. A verdict kink reads can now be the adopted pass, in which a pair
/// that joins through a witness is not listed: see `PREMISE_PASSAGES`.
///
/// FZ-EMPTYJOIN-WITNESS review fixes: 4d58d09a -> 895e7fe4. The load's scope checks again, on its own
/// second pass, that no witness head is tainted, and keeps its first pass otherwise; the reader of
/// the test-only switch `gate_taints_witnesses` (constant `false` outside tests). kink reads
/// `CheckScope::All`, whose verdict changes only where settling dropped two proposals of
/// different roots as undecided: the conflict rule now compares proposals of one root alone, so
/// more witnesses can be adopted (precision; each adoption still passes the second pass).
///
/// fz26 phase-8 FZ-EMPTYJOIN-ORACLE: 4d58d09a -> 414e35af. `check_detached`, the proposal and
/// `Context::holds_empty_variable` read the test-only witness switches
/// (`adopt_unvalidated_witnesses`, `witnesses_only_at_their_pair`,
/// `witness_without_empty_variable`), which outside test builds are the constant `false`
/// (`switches::active`): no verdict kink reads changes.
///
/// fz26 phase-8 FZ-EMPTYJOIN-CLAIMS: 895e7fe4 -> ddb29c1a. A pair over a sort with no normal form
/// (`UnjoinedReason::UninhabitedSort`) seeds the closure and is reported like any other pair, in
/// both scopes and in argument position; the documentation reads the claims with nonempty
/// carriers. The stages, the early return and the counts kink reads are unchanged, and the full
/// check lists the same pairs. Its witness adoption can change: condition 4 (no witness head
/// tainted in the second pass's closure) now sees the seeds of such pairs, so a pair over an empty
/// sort that stays unjoined and reaches a witness head keeps the first pass (fewer witnesses, so
/// more pairs listed: kink can only refuse more). WASM keeps its witness.
///
/// fz26 phase-8 FZ-CONFLUENCE-F: 4d58d09a -> c94f501b. `classify` passes the join the pair's two
/// equations and the overlap's unifier (`join::PairConditions`), so that the join re-reads the
/// conditions in each case it splits off (F1, `confluence/join.rs`); the proposal pass passes the
/// same. The stages, the early return and the counts kink reads are unchanged; the join closes
/// more cases, so a verdict kink reads can list fewer pairs (see `PREMISE_PASSAGES`).
///
/// fz26 int9 (FZ-MEMBERSHIP merged with FZ-JUNK-ORACLE, FZ-EMPTYJOIN-WITNESS with its review fixes,
/// FZ-EMPTYJOIN-ORACLE, FZ-EMPTYJOIN-CLAIMS and FZ-CONFLUENCE-F): the membership table, the
/// `separate_uninhabited` reader, the witness passes, the oracle's witness switch readers, the
/// seeding of pairs over sorts with no normal form and the pair's conditions passed to the join and
/// to the witness proposal side by side (the load's own condition 4 check is kept beside
/// `witnesses_only_at_their_pair`, and `adopt_with_tainted_witness_head` drops both readings of
/// condition 4), and the contract's `refuted` and `joined` points stated together (models of the
/// axioms read as true; steps of `R ∪ W` in `M+`); re-pinned by digest of the merged file: ->
/// `60e618a0`.
const CONFLUENCE_RS: &str = "60e618a0aa3039ce0c85d09441acb6595c5d4a2d7d1b1bb2efa8208f2257da9d";

/// The taint closure (`confluence/closure.rs`): `taintable`, which with `certified_root` decides
/// the early return the probe head turns off (an equation head is taintable), by digest (re-pin
/// R0c-fix-4, R0c-fix-3 review minor 4). Re-pin KS-08c: d6fa4b4c -> 37bed07e, the same syntax-only
/// change of its sort patterns as `CONFLUENCE_RS`. fz26 phase-8 FZ-EMPTYJOIN-WITNESS: 37bed07e ->
/// 13672570: the closure's equations include the witness equations of a pass that has them, which add
/// `SortReach` edges, and the documentation reads the claims' model with `R ∪ W`; `taintable` is
/// unchanged. fz26 phase-8 FZ-EMPTYJOIN-CLAIMS: 13672570 -> f436f6fa, documentation only: the
/// claims' model starts from a model with nonempty carriers, so a pair over a sort with no normal
/// form seeds like any other.
const CLOSURE_RS: &str = "f436f6fa0939bbd9153888df29cc03849ed9659d842d97351e58946d3c3d2fb1";

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
            let baseline_facts = facts(&compiled);
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
                admit_mutant(&equations, &baseline_facts, &side, &misread)
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
                admit_mutant(&equations, &baseline_facts, &side, &effect),
                Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(_)))
            ));
            let compiled_only = SourceEffect {
                redefined: Some(BTreeSet::new()),
                affected: Some(BTreeSet::new()),
                touched: BTreeSet::new(),
            };
            assert!(matches!(
                admit_mutant(&equations, &baseline_facts, &side, &compiled_only),
                Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(_)))
            ));
            // The baseline against itself changes nothing and is admitted with nothing checked.
            let none =
                admit_mutant(&equations, &baseline_facts, &compiled, &compiled_only).unwrap();
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

    /// The claim-free mutant of `patch` on `validator`'s baseline, with kink-patch's source
    /// reading of its effect.
    fn claim_free(
        validator: &NativeValidator,
        patch: &Patch,
    ) -> (ValidatedDefinition, SourceEffect) {
        let baseline = validator.baseline();
        let support = ClaimSupport::new(baseline);
        let withdrawal = support.withdraw(baseline, patch).unwrap();
        let side = validator
            .validate(withdrawal.patch().unwrap_or(patch))
            .unwrap();
        (side, support.effect(baseline, patch).unwrap())
    }

    /// The canonical text of each witness of `facts` (its unique id).
    fn witnesses(facts: &DataFacts) -> Vec<String> {
        facts
            .witnesses()
            .iter()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect()
    }

    const IB_WITNESS: &str = "witness Lblib{}(inj{SortE{}, SortB{}}(VarWitness0:SortE{})) => \
                              inj{SortE{}, SortB{}}(VarWitness0:SortE{})";
    const IC_WITNESS: &str = "witness Lblic{}(inj{SortE{}, SortC{}}(VarWitness0:SortE{})) => \
                              inj{SortE{}, SortC{}}(VarWitness0:SortE{})";

    /// fz26 KINK-WITNESS: a head whose witnesses differ from the baseline's is changed. On
    /// `r0c/witness.k` the full check joins `s`'s and `t`'s pairs through `ib`'s witness, which
    /// `s`'s pair proposes from `da`'s `owise`, and `s2`'s through `ic`'s. Deleting `daowise` takes
    /// `ib`'s witness away; `ic`'s keeps the pass adopted, so the adopted pass does not flip.
    /// Neither the compiled diff (`da`) nor the source reading reaches `t`, whose pair is now not
    /// joined: only the witness diff (`ib`, which `t`'s equation applies) checks it, and the
    /// mutant is refused naming it. Before the diff, the mutant was admitted (fail at base).
    #[test]
    #[ignore = "kink"]
    fn a_head_whose_witnesses_differ_is_checked_where_it_is_reached() {
        on_a_big_stack(|| {
            let validator = r0c("witness");
            let baseline = validator.baseline();
            let compiled = validator.compile_baseline().unwrap();
            let equations = CompiledEquations::of(&compiled).unwrap();
            let baseline_facts = facts(&compiled);
            assert!(baseline_facts.witness_pass_adopted());
            assert_eq!(witnesses(&baseline_facts), [IB_WITNESS, IC_WITNESS]);
            assert!(baseline_facts.has_data(), "{:?}", baseline_facts.findings());

            let patch = Patch::new(vec![Edit::DeleteSentence {
                at: support::rule(baseline, "WITNESS.daowise"),
            }])
            .unwrap();
            let (side, effect) = claim_free(&validator, &patch);
            let source = effect.affected.clone().expect("a known source reading");
            assert!(
                !source.contains("t") && !source.contains("ib"),
                "{source:?}"
            );
            let mutant_facts = facts(&side);
            assert!(mutant_facts.witness_pass_adopted());
            assert_eq!(witnesses(&mutant_facts), [IC_WITNESS]);

            let Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(pairs))) =
                admit_mutant(&equations, &baseline_facts, &side, &effect)
            else {
                panic!("t's pair is checked through ib's witness and refused")
            };
            assert_eq!(
                pairs
                    .iter()
                    .map(|pair| (pair.first.as_str(), pair.second.as_str()))
                    .collect::<Vec<_>>(),
                [("WITNESS.tb", "WITNESS.te")],
                "{pairs:?}"
            );
        });
    }

    /// fz26 KINK-WITNESS (design P7-EMPTYJOIN review B2 and R2-S3): a flip of the pass the full
    /// check adopts checks every head, and the mutant is refused as inconsistent at admission,
    /// before the mutant-findings comparison. On `r0c/witflip.k` the second pass is adopted (`s`'s
    /// and `m`'s pairs join through `ib`'s witness). Editing `mid`'s right-hand side to `g(X)` (a
    /// declared partial function with no equation) makes `m`'s pair join in the first pass only,
    /// so the mutant's check keeps its first pass, where `s`'s pair is not joined: the mutant is
    /// refused naming `s`'s pair. Read back the other way (the mutant as the baseline, the
    /// baseline as its mutant), the flip checks every head (`checked` is `None`) although the
    /// source reading names only `m`, and with nothing unjoined the side is admitted.
    #[test]
    #[ignore = "kink"]
    fn a_flip_of_the_adopted_pass_checks_every_head() {
        on_a_big_stack(|| {
            let validator = r0c("witflip");
            let baseline = validator.baseline();
            let compiled = validator.compile_baseline().unwrap();
            let equations = CompiledEquations::of(&compiled).unwrap();
            let baseline_facts = facts(&compiled);
            assert!(baseline_facts.witness_pass_adopted());
            assert_eq!(witnesses(&baseline_facts), [IB_WITNESS]);
            assert!(baseline_facts.has_data(), "{:?}", baseline_facts.findings());

            // `mib`'s right-hand side is `ib(X)`: the same argument under `g`.
            let ib = baseline
                .term(&TermRef::new(
                    support::rule(baseline, "WITFLIP.mib"),
                    [0, 1],
                ))
                .unwrap()
                .clone();
            let Term::Apply { arguments, .. } = ib.unannotated() else {
                panic!("{ib}")
            };
            let at = TermRef::new(support::rule(baseline, "WITFLIP.mid"), [0, 1]);
            let expected = baseline.term(&at).unwrap().clone();
            let patch = Patch::new(vec![Edit::ReplaceTerm {
                at,
                expected,
                replacement: Term::Apply {
                    label: Label::new("g"),
                    arguments: arguments.clone(),
                },
            }])
            .unwrap();
            let (side, effect) = claim_free(&validator, &patch);
            let mutant_facts = facts(&side);
            assert!(!mutant_facts.witness_pass_adopted());
            assert!(witnesses(&mutant_facts).is_empty());

            let Err(MutantFailure::Inconsistent(Inconsistency::Unjoined(pairs))) =
                admit_mutant(&equations, &baseline_facts, &side, &effect)
            else {
                panic!("the flip is refused as inconsistent")
            };
            assert_eq!(
                pairs
                    .iter()
                    .map(|pair| (pair.first.as_str(), pair.second.as_str()))
                    .collect::<Vec<_>>(),
                [("WITFLIP.sa", "WITFLIP.sb")],
                "{pairs:?}"
            );

            let back = SourceEffect {
                redefined: None,
                affected: Some(BTreeSet::from(["m".to_owned()])),
                touched: BTreeSet::new(),
            };
            let admitted = admit_mutant(
                &CompiledEquations::of(&side).unwrap(),
                &mutant_facts,
                &compiled,
                &back,
            )
            .unwrap();
            assert_eq!(admitted.checked, None, "{admitted:?}");
            assert_eq!(
                admitted.changed,
                BTreeSet::from(["Lblib".to_owned(), "Lblm".to_owned()])
            );
        });
    }
}
