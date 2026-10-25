//! fz26 KINK-CAUSE-SUBTERM (KINK-OVERLOAD-VALUE review N4): a slot the pair's cross-definition
//! judgement makes unknown (kink-campaign `judge_across`) has its own cause in the run document:
//! the side whose run ended in a value of its own definition, that this end is not data under the
//! other side's definition, and the first node of it, in pre-order, that fails its own test there.
//! Before, the cause read as if the mutant's run had not ended in a value.
//!
//! The fixtures are the review's r2-anyw pair in `testdata/k/overload`, in both directions:
//! `FLOW-anyw.toml` (`anyw.k`, the rule `c(1) => d`, made `[anywhere]` by the mutation) and
//! `FLOW-anyw-rev.toml` (`anyw-anywhere.k`, whose `[anywhere]` the mutation removes).

mod flow_support;

use flow_support::copy_dir;
use kink_flow::{
    FlowManifest, MutationList,
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
        .join(format!("kink-flow-cross-cause-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&to);
    copy_dir(&from, &to);
    to
}

/// The cause of the only executed entry of the only mutation row of `kink-flow run`, after
/// checking the row is `unknown`.
fn only_cause(manifest: &Path, mutations: &Path) -> String {
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
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows.len(), 1, "{document:#}");
    assert_eq!(rows[0]["status"], "unknown", "{document:#}");
    let executed = rows[0]["executed"].as_array().unwrap();
    assert_eq!(executed.len(), 1, "{document:#}");
    assert_eq!(executed[0]["outcome"], "unknown", "{document:#}");
    executed[0]["cause"]
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| {
            panic!("{}", Value::to_string(&executed[0]));
        })
}

/// Since KRUST-ANYWHERE-HEAD `c` is a data head of the definition that applies `c(1) => d`
/// anywhere (a plain `anywhere` head declared `value-production`), so `c(1)` fails as an
/// application of a data head k-rust does not judge data (the rule matches it), not by its head.
const NOT_DATA: &str = "the first node, in pre-order, that fails its own test is an application of \
                        `c(_)_AW-SYNTAX_Foo_Int` at <s>: it is an application of a data head that \
                        k-rust does not judge data (an equation of its head may apply to it, or an \
                        argument is not data)";

mod kink_tier {
    use super::*;

    /// r2-anyw-attr: the mutant makes `c` an anywhere head, so the baseline's end `c(1)` is not
    /// data under the mutant's definition, where `c(1) => d` rewrites it. The mutant's own end `d`
    /// is.
    #[test]
    #[ignore = "kink"]
    fn a_baseline_end_not_data_under_the_mutant_names_the_baseline_side() {
        let dir = fixture("forward");
        let cause = only_cause(
            &dir.join("FLOW-anyw.toml"),
            &dir.join("MUTATIONS-anyw.toml"),
        );
        assert!(
            cause.starts_with(
                "exit-stop, whole-term: the baseline's run ended in a value of its own \
                 definition, but that end is not data under the mutant's definition, so the two \
                 ends cannot be compared; there, "
            ),
            "{cause}"
        );
        assert!(cause.contains(NOT_DATA), "{cause}");
        assert!(!cause.contains("the mutant's run:"), "{cause}");
    }

    /// The reverse pair: the baseline's rule is `[anywhere]` and the mutant drops it, so the
    /// mutant's end `c(1)` is not data under the baseline's definition. The cause names the
    /// mutant side, not a run that did not end in a value.
    #[test]
    #[ignore = "kink"]
    fn a_mutant_end_not_data_under_the_baseline_names_the_mutant_side() {
        let dir = fixture("reverse");
        let cause = only_cause(
            &dir.join("FLOW-anyw-rev.toml"),
            &dir.join("MUTATIONS-anyw-rev.toml"),
        );
        assert!(
            cause.starts_with(
                "exit-stop, whole-term: the mutant's run ended in a value of its own definition, \
                 but that end is not data under the baseline's definition, so the two ends cannot \
                 be compared; there, "
            ),
            "{cause}"
        );
        assert!(cause.contains(NOT_DATA), "{cause}");
        assert!(!cause.contains("did not end in a value"), "{cause}");
    }
}
