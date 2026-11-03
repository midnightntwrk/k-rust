//! The compared cells: a cell the specification declares `unobservable` is left out of every
//! comparison, a manifest may narrow the compared cells (`[result] cells`) but never compare an
//! unobservable one, and every document names the slots and the cells compared.
//!
//! The fixture is testdata/flow/unobservable: `unobs.k`, whose program `emit(1) ; note(2)` writes
//! the observed `<out>` and the unobservable `<scratch>`; `plain.k`, the same definition without
//! the declaration; `nested.k`, the same with both cells inside a wrapper cell `<state>`; and
//! `collection.k`, an unobservable cell inside a `*` cell. Its mutations change only `<scratch>`
//! (`note-offset`) or `<out>` (`emit-offset`). The one-sided kill under a `cells` slot runs on
//! `testdata/k/l1/onesidedcell.k`.

use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{EXIT_CORPUS, EXIT_OK, check},
    digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, outcome_context, spec_digest},
    manifest::Budget,
    mutation::MutationList,
    report::{ReportOptions, report},
    results::{ResultsOptions, results},
    search::{ProgramOrder, RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

fn flow() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/unobservable")
}

/// A private copy of the fixture, with `extra` written as `FLOW-<name>.toml` files beside it.
fn fixture(test: &str, extra: &[(&str, &str)]) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-unobservable-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    for entry in fs::read_dir(flow()).unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() {
            fs::copy(&path, dir.join(path.file_name().unwrap())).unwrap();
        }
    }
    for (name, text) in extra {
        fs::write(dir.join(format!("FLOW-{name}.toml")), text).unwrap();
    }
    dir
}

/// `FLOW.toml` with `[result] cells` set to `cells`.
fn narrowed(cells: &str) -> String {
    let manifest = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    manifest.replace(
        "[[program]]",
        &format!("[result]\ncells = {cells}\n\n[[program]]"),
    )
}

fn search(manifest: &Path) -> Value {
    let (document, _) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &RunOptions {
            order: ProgramOrder::Corpus,
            ..RunOptions::default()
        },
    );
    document
}

/// Each mutation's id and status, in list order.
fn statuses(document: &Value) -> Vec<(String, String)> {
    document["mutations"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn pairs(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(id, status)| ((*id).to_owned(), (*status).to_owned()))
        .collect()
}

fn result(slot: &str, compared: &[&str], not_compared: &[&str], unobservable: &[&str]) -> Value {
    json!({
        "slots": ["exit-stop", slot],
        "compared": compared,
        "not_compared": not_compared,
        "unobservable": unobservable,
    })
}

#[track_caller]
fn refusal(admission: &FlowAdmission) -> (String, String, String) {
    let refusal = admission.record.refusal.as_ref().expect("a refused spec");
    (
        refusal.stage.clone(),
        refusal.reason.clone(),
        refusal.detail.clone(),
    )
}

#[test]
fn a_change_only_to_an_unobservable_cell_survives_and_every_document_names_the_cells() {
    let dir = fixture("declared", &[]);
    let manifest = dir.join("FLOW.toml");
    let expected = result("cells", &["k", "out"], &["scratch"], &["scratch"]);

    let (document, status) = check(&manifest);
    assert_eq!(status, EXIT_OK, "{document:#}");
    assert_eq!(document["version"], 7);
    assert_eq!(document["result"], expected);

    let (document, ok) = results(
        &FlowManifest::read(&manifest).unwrap(),
        &ResultsOptions::default(),
    );
    assert!(ok, "{document:#}");
    assert_eq!(document["result"], expected);
    assert_eq!(document["programs"][0]["class"], "comparable");
    // The recorded final configuration is the projected one: <scratch>'s content is `\top`.
    // Under Z3 the result cache is off (`results::RESULT_CACHE_Z3`) and nothing is recorded.
    let results = dir.join(".kink-flow/results");
    if cfg!(feature = "z3") {
        assert!(!results.exists());
    } else {
        let spec = fs::read_dir(&results)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        let record = fs::read_dir(spec).unwrap().next().unwrap().unwrap().path();
        let record: Value = serde_json::from_str(&fs::read_to_string(record).unwrap()).unwrap();
        let end = record["final_configuration"][0].as_str().unwrap();
        assert!(end.contains("\\top{SortScratchCell{}}()"), "{end}");
        assert!(!end.contains("SortScratchCell{}, "), "{end}");
    }

    let document = search(&manifest);
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "survived"), ("emit-offset", "killed")])
    );
    assert_eq!(document["result"], expected);
    assert_eq!(document["survivors"], json!(["note-offset"]));
    let killed = &document["mutations"][1]["executed"][0];
    assert_eq!(
        killed["slots"]["cells"]["outcome"], "distinguish",
        "{killed:#}"
    );
    assert_eq!(
        killed["difference"]["path"],
        json!(["<generatedTop>", "<out>"]),
        "{killed:#}"
    );
    let survived = &document["mutations"][0]["executed"][0];
    assert_eq!(
        survived["slots"]["cells"]["outcome"], "agree",
        "{survived:#}"
    );

    // `report` prints the stored document, with its `result`.
    let (stored, found) = report(
        &FlowManifest::read(&manifest).unwrap(),
        &ReportOptions::default(),
    );
    assert!(found);
    assert_eq!(stored["result"], expected);

    // The outcome cache keeps the verdicts: a second run decides both from tier 1, which the z3
    // profile turns off (kink-flow `search::tier1_refusal`), so there both run live again.
    let again = search(&manifest);
    assert_eq!(statuses(&again), statuses(&document));
    assert_eq!(
        again["outcome_cache"]["mutations_from_cache"],
        if cfg!(feature = "z3") { 0 } else { 2 },
        "{again:#}"
    );
}

#[test]
fn without_the_declaration_both_mutations_are_killed_on_the_whole_term() {
    let dir = fixture("plain", &[]);
    let manifest = dir.join("FLOW-plain.toml");
    let (document, status) = check(&manifest);
    assert_eq!(status, EXIT_OK, "{document:#}");
    let expected = result("whole-term", &["k", "out", "scratch"], &[], &[]);
    assert_eq!(document["result"], expected);
    let document = search(&manifest);
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "killed"), ("emit-offset", "killed")])
    );
    assert_eq!(document["result"], expected);
    let killed = &document["mutations"][0]["executed"][0];
    assert_eq!(
        killed["slots"]["whole-term"]["outcome"], "distinguish",
        "{killed:#}"
    );
    assert_eq!(
        killed["difference"]["path"],
        json!(["<generatedTop>", "<scratch>"]),
        "{killed:#}"
    );
}

#[test]
fn a_manifest_narrows_the_compared_cells() {
    let dir = fixture("narrowed", &[("k", &narrowed("[\"k\"]"))]);
    let manifest = dir.join("FLOW-k.toml");
    let document = search(&manifest);
    assert_eq!(
        document["result"],
        result("cells", &["k"], &["out", "scratch"], &["scratch"])
    );
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "survived"), ("emit-offset", "survived")])
    );
}

#[test]
fn a_narrowing_that_compares_an_unobservable_cell_or_names_no_cell_is_refused() {
    let dir = fixture(
        "refused",
        &[
            ("scratch", &narrowed("[\"out\", \"scratch\"]")),
            ("nope", &narrowed("[\"nope\"]")),
            ("counter", &narrowed("[\"generatedCounter\"]")),
        ],
    );
    for (name, reason, cell) in [
        ("scratch", "result-cell-unobservable", "<scratch>"),
        ("nope", "result-cell-unknown", "<nope>"),
        ("counter", "result-cell-unknown", "<generatedCounter>"),
    ] {
        let manifest = dir.join(format!("FLOW-{name}.toml"));
        let (stage, found, detail) = refusal(&admit(&FlowManifest::read(&manifest).unwrap()));
        assert_eq!(
            (stage.as_str(), found.as_str()),
            ("result", reason),
            "{detail}"
        );
        assert!(detail.contains(cell), "{detail}");
        let (document, status) = check(&manifest);
        assert_eq!(status, EXIT_CORPUS);
        assert_eq!(document["result"], Value::Null);
        assert_eq!(document["spec"]["stage"], "result");
    }
}

#[test]
fn an_unobservable_cell_inside_a_collection_is_refused_unless_the_narrowing_leaves_the_collection_out()
 {
    let collection = |result: &str| {
        format!(
            "[spec]\nentry = \"collection.k\"\nmain_module = \"COLLECTION\"\n\
             syntax_module = \"COLLECTION-SYNTAX\"\n{result}\n\
             [[program]]\nid = \"one\"\ntext = \"emit(1)\"\n"
        )
    };
    let dir = fixture(
        "collection",
        &[
            ("collection", &collection("")),
            ("inside", &collection("[result]\ncells = [\"id\"]\n")),
            (
                "outside",
                &collection("[result]\ncells = [\"k\", \"out\"]\n"),
            ),
        ],
    );
    let admitted =
        |name: &str| admit(&FlowManifest::read(&dir.join(format!("FLOW-{name}.toml"))).unwrap());
    let (stage, reason, detail) = refusal(&admitted("collection"));
    assert_eq!(
        (stage.as_str(), reason.as_str()),
        ("result", "unobservable-cell-position")
    );
    assert!(
        detail.contains("<tmp>") && detail.contains("* cell <thread>"),
        "{detail}"
    );
    let (stage, reason, detail) = refusal(&admitted("inside"));
    assert_eq!(
        (stage.as_str(), reason.as_str()),
        ("result", "result-cell-position")
    );
    assert!(
        detail.contains("<id>") && detail.contains("* cell <thread>"),
        "{detail}"
    );
    // Leaving the enclosing <threads> out leaves <tmp> out with it.
    let outside = admitted("outside");
    let spec = outside.spec.as_ref().expect("admitted");
    assert_eq!(
        spec.result.value(),
        result("cells", &["k", "out"], &["threads"], &["tmp"])
    );
}

#[test]
fn the_spec_digest_changes_with_the_compared_cells_only_when_the_manifest_narrows_them() {
    let directory = flow();
    let plain = fs::read_to_string(directory.join("FLOW.toml")).unwrap();
    let digest = |text: &str| {
        let manifest = FlowManifest::decode(text, &directory).unwrap();
        spec_digest(&manifest, &[])
    };
    let base = digest(&plain);
    let narrowed_k = digest(&narrowed("[\"k\"]"));
    assert_ne!(base, narrowed_k);
    assert_eq!(
        digest(&narrowed("[\"k\", \"out\"]")),
        digest(&narrowed("[\"out\", \"k\"]"))
    );
    assert_ne!(narrowed_k, digest(&narrowed("[\"k\", \"out\"]")));
    // A manifest without `[result]` has the payload it had before the section existed.
    let manifest = FlowManifest::decode(&plain, &directory).unwrap();
    assert!(
        kink_flow::digest::spec_payload(&manifest, &[])
            .get("result_cells")
            .is_none()
    );
}

/// A manifest for `nested.k`, with `result` (a `[result]` section or nothing) before its program.
fn nested(result: &str) -> String {
    format!(
        "[spec]\nentry = \"nested.k\"\nmain_module = \"NESTED\"\nsyntax_module = \"NESTED-SYNTAX\"\n\
         {result}\n[[program]]\nid = \"both\"\ntext = \"emit(1) ; note(2)\"\n"
    )
}

#[test]
fn an_unobservable_cell_inside_a_named_or_enclosing_cell_is_left_out() {
    let dir = fixture(
        "nested",
        &[
            ("nested", &nested("")),
            ("state", &nested("[result]\ncells = [\"state\"]\n")),
            ("out", &nested("[result]\ncells = [\"out\"]\n")),
        ],
    );
    let manifest = |name: &str| dir.join(format!("FLOW-{name}.toml"));
    let admitted = |name: &str| {
        let admission = admit(&FlowManifest::read(&manifest(name)).unwrap());
        let spec = admission.spec.as_ref().expect("admitted");
        spec.result.value()
    };
    // By default the observed children of <state> are compared, not <state>, which encloses the
    // unobservable <scratch>.
    assert_eq!(
        admitted("nested"),
        result("cells", &["k", "out"], &["scratch"], &["scratch"])
    );
    // Narrowed to <out>: its sibling <scratch> and its parent's sibling <k> are left out.
    assert_eq!(
        admitted("out"),
        result("cells", &["out"], &["k", "scratch"], &["scratch"])
    );
    // Narrowed to <state>: its sibling <k> is left out, and so is the unobservable <scratch>
    // inside it, so a change only to <scratch> survives and one to <out> is killed.
    let expected = result("cells", &["state"], &["k", "scratch"], &["scratch"]);
    assert_eq!(admitted("state"), expected);
    let document = search(&manifest("state"));
    assert_eq!(document["result"], expected);
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "survived"), ("emit-offset", "killed")])
    );
    let killed = &document["mutations"][1]["executed"][0];
    assert_eq!(
        killed["difference"]["path"],
        json!(["<generatedTop>", "<state>", "<out>"]),
        "{killed:#}"
    );
}

#[test]
fn the_outcome_context_names_the_cells_left_out() {
    let dir = fixture("context", &[("k", &narrowed("[\"k\"]"))]);
    let context = |manifest: &str| {
        let admission = admit(&FlowManifest::read(&dir.join(manifest)).unwrap());
        let spec = admission.spec.as_ref().expect("admitted");
        // One build and one execution digest for both, so only the projection can differ.
        outcome_context(
            kink_patch::sha256(b"kink build"),
            ExecutionDigest {
                kind: EXECUTION_DIGEST_KIND,
                digest: kink_patch::sha256(b"specification"),
            },
            Budget::default(),
            &spec.result,
        )
    };
    let declared = context("FLOW.toml");
    let narrowed_k = context("FLOW-k.toml");
    // Both slots are `cells`; they leave out other cells, so their contexts differ.
    assert_eq!(declared["oracles"], json!(["exit-stop", "cells"]));
    assert_eq!(narrowed_k["oracles"], declared["oracles"]);
    assert_eq!(declared["not_compared"], json!(["scratch"]));
    assert_eq!(narrowed_k["not_compared"], json!(["out", "scratch"]));
    let mut without = narrowed_k.clone();
    without["not_compared"] = declared["not_compared"].clone();
    assert_eq!(without, declared);
    // A whole-term context names no uncompared cells.
    let plain = context("FLOW-plain.toml");
    assert_eq!(plain["oracles"], json!(["exit-stop", "whole-term"]));
    assert!(plain.get("not_compared").is_none(), "{plain:#}");
}

/// A corpus of `testdata/k/l1/onesidedcell.k`, its configuration declaring `<scratch>` before
/// `<k>` (so an end's first difference from an end whose `<scratch>` is `\top` is in `<scratch>`
/// unless that end is projected too), with `work_factor = 1`, one program `start(600)`,
/// and two mutations that also lengthen the late loop twentyfold (late's 2 becomes 20), so their
/// run (about 12000 states) passes the work budget (the baseline's about 1200 states plus the
/// floor of 10000) after the early branch has finished: `early-k` changes the early end's `<k>`
/// (7 becomes 8), `early-scratch` only its unobservable `<scratch>` (1 becomes 2).
fn one_sided_cell_corpus() -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-unobservable-{}", std::process::id()))
        .join("one-sided");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let definition = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/l1/onesidedcell.k"),
    )
    .unwrap();
    let configuration = "configuration <k> $PGM:Prog </k> <scratch unobservable=\"\"> 0 </scratch>";
    assert!(definition.contains(configuration));
    fs::write(
        dir.join("onesidedcell.k"),
        definition.replace(
            configuration,
            "configuration <scratch unobservable=\"\"> 0 </scratch> <k> $PGM:Prog </k>",
        ),
    )
    .unwrap();
    // No wall clock decides a run: the work budget does.
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"onesidedcell.k\"\nmain_module = \"ONESIDEDCELL\"\n\
         syntax_module = \"ONESIDEDCELL-SYNTAX\"\n\n[budget]\ntime_ms = 600000\nwork_factor = 1\n\n\
         [[program]]\nid = \"start\"\ntext = \"start(600)\"\n",
    )
    .unwrap();
    let mutation = |id: &str, find: &str, replace: &str| {
        format!(
            "[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"another early end, a longer loop\"\n\n\
             [[mutation.edit]]\nrule = \"early\"\nfind = \"{find}\"\nreplace = \"{replace}\"\n\n\
             [[mutation.edit]]\nrule = \"late\"\nfind = \"N *Int 2\"\nreplace = \"N *Int 20\"\n\n"
        )
    };
    fs::write(
        dir.join("MUTATIONS.toml"),
        mutation("early-k", "N +Int 7", "N +Int 8")
            + &mutation("early-scratch", "N +Int 1", "N +Int 2"),
    )
    .unwrap();
    dir.join("FLOW.toml")
}

#[test]
fn a_one_sided_kill_under_a_cells_slot_never_rests_on_an_unobservable_cell() {
    let document = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| search(&one_sided_cell_corpus()))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(
        document["result"],
        result("cells", &["k"], &["scratch"], &["scratch"])
    );
    let statuses = statuses(&document);
    assert_eq!(
        statuses[0],
        ("early-k".to_owned(), "killed".to_owned()),
        "{document:#}"
    );
    // The explored part's early end differs from the baseline's only in <scratch>, which the slot
    // leaves out: no one-sided kill, and the run reached its work budget.
    assert_eq!(
        statuses[1],
        ("early-scratch".to_owned(), "unknown".to_owned()),
        "{document:#}"
    );
    let killed = &document["mutations"][0]["executed"][0];
    assert_eq!(
        killed["slots"]["cells"]["outcome"], "distinguish",
        "{killed:#}"
    );
    // The evidence is the projected one-sided end: the difference is in <k>, never in <scratch>,
    // which an unprojected end would show first.
    let difference = &killed["difference"];
    assert_eq!(difference["mutant"]["complete"], false, "{difference:#}");
    assert_eq!(
        difference["path"],
        json!(["<generatedTop>", "<k>"]),
        "{difference:#}"
    );
    let text = difference["mutant"]["value"]["text"].as_str().unwrap();
    assert!(text.contains("done ( 608 )"), "{difference:#}");
}
