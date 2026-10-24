//! fz26 KINK-OVERLOAD-VALUE (P7-SIMPLE-KINK design, (c) overloaded list ends): a compared end may
//! hold an instance-normal application of an overload data head, where k-rust's data judgement
//! (`BackendDefinition::is_data`) holds under the definition's own facts (kink-native
//! `data::data_ends`), and every compared end of a pair is judged under the other side's
//! definition too (kink-campaign `runner::judge_across`): an end that is not data there makes that
//! side's slot unknown for the pair.
//!
//! The fixtures are in `testdata/k/overload`, outside the flow corpus that `tests/modality.rs`
//! walks:
//! - `simple.md`: TRIAL2's SIMPLE (untyped) copy without stream cells (fz26 phase 6; the stock
//!   definition with `stream="stdin"`/`"stdout"` removed from its two I/O cells), with TRIAL2's
//!   eleven programs (`FLOW-corpus.toml`, `programs/`) and 27 mutations
//!   (`MUTATIONS-corpus.toml`), copied from the trial's scratch, and small programs
//!   (`FLOW-small.toml`: FZ-OVERLIST's `simple` repro, whose `p1-var-init` is P7-SIMPLE-IN's
//!   `listform`, and probe-a's `p3`, `p5`, `p6`);
//! - `ov.k`: FZ-OVERLIST's `ov` repro, an overloaded `Ids`/`Exps` list family;
//! - `anyw.k`: the P7-KINKFLOW review's r2-anyw written as a kink mutation (fz26/kinkflow-review
//!   790a695de, `probe-kinkflow-review/flows/r2-anyw-attr`): `[anywhere]` added to the baseline
//!   rule `c(1) => d`;
//! - `addmember.k`: the DATAEND review's r2-addmember baseline, with its edit written as a kink
//!   mutation.
//!
//! The 27 mutations' verdicts are measured, not pinned here (the design's review S5).

mod flow_support;

use flow_support::copy_dir;
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_OK, results},
    results::ResultsOptions,
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// A private copy of `testdata/k/overload` for one test.
fn fixture(test: &str) -> PathBuf {
    let from = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/overload");
    let to = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-overload-value-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&to);
    copy_dir(&from, &to);
    to
}

/// `kink-flow results` of `manifest`, its status checked.
#[track_caller]
fn classes(manifest: &Path) -> Value {
    let (document, status) = results(
        manifest,
        &ResultsOptions {
            verify: false,
            cache: None,
            mutations: None,
        },
    );
    assert_eq!(status, EXIT_OK, "{document:#}");
    document
}

/// `(id, class)` of every program row.
fn rows(document: &Value) -> Vec<(String, String)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["class"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// `kink-flow run` of `mutations` under `manifest`, in corpus order.
fn search(manifest: &Path, mutations: &Path) -> Value {
    let manifest = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(mutations).unwrap();
    let (document, ok) = run(
        &manifest,
        &list,
        &RunOptions {
            only: Vec::new(),
            cache: None,
            order: ProgramOrder::Corpus,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
        },
    );
    assert!(ok, "{document:#}");
    document
}

/// The only mutation row of `document`.
fn only_row(document: &Value) -> &Value {
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    &rows[0]
}

mod kink_tier {
    use super::*;

    /// r2-anyw as a kink mutation: the baseline's end holds `c(1)` in its `<s>` cell, a free
    /// constructor of the baseline; the mutant adds `[anywhere]` to the rule `c(1) => d`, so `c`
    /// roots an equation of the mutant, its end holds `d`, and in the mutant's theory the two are
    /// one value. The baseline has no finding, and neither does the mutant, so no full check
    /// refuses it; before this ticket kink-flow killed it through the whole-term slot. Judged
    /// under the mutant's definition, the baseline's end is not data (`c` is no free constructor
    /// there), so the slots are unknown for this pair and the mutation is `unknown`. The program
    /// stays comparable on the baseline.
    #[test]
    #[ignore = "kink"]
    fn an_anywhere_attribute_on_a_baseline_constructor_is_not_a_kill() {
        let dir = fixture("anyw");
        assert_eq!(
            rows(&classes(&dir.join("FLOW-anyw.toml"))),
            [("one".to_owned(), "comparable".to_owned())]
        );
        let document = search(
            &dir.join("FLOW-anyw.toml"),
            &dir.join("MUTATIONS-anyw.toml"),
        );
        let row = only_row(&document);
        assert_eq!(row["id"], "becomes-anywhere", "{document:#}");
        assert_eq!(row["status"], "unknown", "{document:#}");
    }

    /// r2-addmember (the DATAEND review's, data_term's module example: adding
    /// `Bot ::= f(Bot) [overload(f)]` lowers the baseline's normal form `f_Nm(inj(b))` to
    /// `inj(f_Bot(b))`) cannot be written as a kink mutation: kink-flow edits rules only, and an
    /// edit that adds a production adds a sentence, so it is `invalid-mutation` with reason
    /// `structure-changed`. The judgement under both definitions would make it unknown, as it
    /// does r2-anyw; it is not reachable through kink-flow.
    #[test]
    #[ignore = "kink"]
    fn adding_an_overload_member_is_not_a_kink_mutation() {
        let dir = fixture("addmember");
        let document = search(
            &dir.join("FLOW-addmember.toml"),
            &dir.join("MUTATIONS-addmember.toml"),
        );
        let row = only_row(&document);
        assert_eq!(row["status"], "invalid-mutation", "{document:#}");
        assert_eq!(row["reason"], "structure-changed", "{document:#}");
    }

    /// An end holding an irreducible overloaded list application is compared when the
    /// application is data. Before this ticket every such end was unknown ("a baseline
    /// declaration-scoped oracle gate rejected"): FZ-OVERLIST's `ov` `int` and `mixed` (an `Exps`
    /// list holding an `Int`, which no overload equation lowers to `Ids`), and on SIMPLE every
    /// program whose store keeps an argument list or a declaration with an initializer
    /// (`p1-var-init`, P7-SIMPLE-IN's `listform`; `p2`, `p3`, `q5`, `q6`).
    #[test]
    #[ignore = "kink"]
    fn overloaded_list_ends_are_comparable() {
        let dir = fixture("small");
        let document = classes(&dir.join("FLOW-ov.toml"));
        assert_eq!(
            rows(&document),
            ["empty", "ids", "int", "mixed"]
                .map(|id| (id.to_owned(), "comparable".to_owned()))
                .to_vec(),
            "{document:#}"
        );
        let document = classes(&dir.join("FLOW-small.toml"));
        assert_eq!(
            rows(&document),
            [
                "p1-var-init",
                "p2-print-int",
                "p3-print-string",
                "p4-var",
                "p5-exp",
                "p6-two-functions",
                "q1-call-empty",
                "q2-var-two",
                "q3-param",
                "q5-call-int",
                "q6-call-exp",
                "q7-call-id",
            ]
            .map(|id| (id.to_owned(), "comparable".to_owned()))
            .to_vec(),
            "{document:#}"
        );
    }

    /// TRIAL2's eleven SIMPLE programs: before this ticket none was comparable (each store holds
    /// a list). Now nine are; `array` and `matrix` stay unknown, since `a[i]` leaves an
    /// application of `_[_]`, which roots two `[anywhere]` rules that are not overload equations,
    /// so it is no overload data head (the design's Q3).
    #[test]
    #[ignore = "kink"]
    fn the_trial2_corpus_programs_are_comparable_but_the_array_ones() {
        let dir = fixture("corpus");
        let document = classes(&dir.join("FLOW-corpus.toml"));
        let expected = [
            ("arith", "comparable"),
            ("cmp", "comparable"),
            ("loop", "comparable"),
            ("array", "unknown"),
            ("fact", "comparable"),
            ("strings", "comparable"),
            ("exc", "comparable"),
            ("threads", "comparable"),
            ("locks", "comparable"),
            ("matrix", "unknown"),
            ("higher", "comparable"),
        ];
        assert_eq!(
            rows(&document),
            expected
                .map(|(id, class)| (id.to_owned(), class.to_owned()))
                .to_vec(),
            "{document:#}"
        );
    }
}
