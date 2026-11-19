//! The compared cells: a cell the specification declares `unobservable` is left out of every
//! comparison, a manifest's projections may narrow the compared cells (`[[projection]] compare`)
//! but never compare an unobservable one, and every document names the slots and the cells
//! compared.
//!
//! The fixture is testdata/flow/unobservable: `unobs.k`, whose program `emit(1) ; note(2)` writes
//! the observed `<out>` and the unobservable `<scratch>`; `plain.k`, the same definition without
//! the declaration; `nested.k`, the same with both cells inside a wrapper cell `<state>`;
//! `collection.k`, an unobservable cell beside a compared one inside the instances of a Map
//! collection; and
//! `collectionkey.k`, the same Map with its key declared unobservable. Its mutations change only
//! `<scratch>` (`note-offset`) or `<out>` (`emit-offset`). The one-sided kill under a `cells` slot
//! runs on `testdata/k/l1/onesidedcell.k`.

use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{
        CommandFiles, EXIT_UNASKED, EXIT_YES, FlowCommand, FrontEnd, check, check_document,
        dispatch,
    },
    coverage::{CoverageOptions, coverage},
    digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, outcome_context, spec_digest},
    manifest::Budget,
    mutation::MutationList,
    report::{ReportOptions, report},
    search::{RunOptions, run},
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

/// `FLOW.toml` with one projection, `p`, comparing `cells`.
fn narrowed(cells: &str) -> String {
    let manifest = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    manifest.replace(
        "[[program]]",
        &format!("[[projection]]\nname = \"p\"\ncompare = {cells}\n\n[[program]]"),
    )
}

fn search(manifest: &Path) -> Value {
    let (document, _) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &RunOptions {
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
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["version"], 18);
    assert_eq!(document["result"], expected);
    // A flow that declares no projection names none: its `default` is what `result` names.
    assert_eq!(document.get("projections"), None, "{document:#}");

    let (document, ok) = coverage(
        &FlowManifest::read(&manifest).unwrap(),
        &CoverageOptions::default(),
    );
    assert!(ok, "{document:#}");
    assert_eq!(document["result"], expected);
    assert_eq!(document.get("projections"), None, "{document:#}");
    assert_eq!(document["programs"][0]["class"], "comparable");
    // The recorded final configuration is the projected one: <scratch>'s content is `\top`.
    let results = dir.join(".kink-flow/results");
    let spec = fs::read_dir(&results)
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let record = fs::read_dir(spec).unwrap().next().unwrap().unwrap().path();
    let record: Value = serde_json::from_str(&fs::read_to_string(record).unwrap()).unwrap();
    let end = kink_flow::results::record_final_configuration(&record).unwrap()[0];
    assert!(end.contains("\\top{SortScratchCell{}}()"), "{end}");
    assert!(!end.contains("SortScratchCell{}, "), "{end}");

    let document = search(&manifest);
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "survived"), ("emit-offset", "killed")])
    );
    assert_eq!(document["result"], expected);
    assert_eq!(document.get("projections"), None, "{document:#}");
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

    // The outcome cache keeps the verdicts: a second run decides both from tier 1.
    let again = search(&manifest);
    assert_eq!(statuses(&again), statuses(&document));
    assert_eq!(
        again["outcome_cache"]["mutations_from_cache"], 2,
        "{again:#}"
    );
}

#[test]
fn without_the_declaration_both_mutations_are_killed_on_the_whole_term() {
    let dir = fixture("plain", &[]);
    let manifest = dir.join("FLOW-plain.toml");
    let (document, status) = check(&manifest);
    assert_eq!(status, EXIT_YES, "{document:#}");
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
        assert_eq!(status, EXIT_UNASKED);
        assert_eq!(document["result"], Value::Null);
        assert_eq!(document["spec"]["stage"], "result");
    }
}

/// An unobservable cell inside a collection's instances is left out of each instance: a mutant
/// that changes only `<tmp>` survives, one that changes a thread's key or its compared `<val>` is
/// killed. Narrowed to a cell inside the instances, the slot compares that cell and the key the
/// Map holds the instance by, and leaves the instances' other cells out; narrowed to cells
/// outside, it leaves the whole collection out.
#[test]
fn an_unobservable_cell_inside_a_collection_is_left_out_of_each_instance() {
    let collection = |result: &str| {
        format!(
            "[spec]\nentry = \"collection.k\"\nmain_module = \"COLLECTION\"\n\
             syntax_module = \"COLLECTION-SYNTAX\"\n{result}\n\
             [[program]]\nid = \"one\"\ntext = \"spawn(1)\"\n"
        )
    };
    let dir = fixture(
        "collection",
        &[
            ("collection", &collection("")),
            (
                "inside",
                &collection("[[projection]]\nname = \"p\"\ncompare = [\"id\"]\n"),
            ),
            (
                "val",
                &collection("[[projection]]\nname = \"p\"\ncompare = [\"val\"]\n"),
            ),
            (
                "outside",
                &collection("[[projection]]\nname = \"p\"\ncompare = [\"k\", \"out\"]\n"),
            ),
        ],
    );
    let manifest = |name: &str| dir.join(format!("FLOW-{name}.toml"));
    let admitted = |name: &str| admit(&FlowManifest::read(&manifest(name)).unwrap());
    let result_of = |name: &str| {
        let admission = admitted(name);
        let spec = admission
            .spec
            .as_ref()
            .unwrap_or_else(|| panic!("{name}: {:?}", admission.record.refusal));
        spec.result.value()
    };
    assert_eq!(
        result_of("collection"),
        result("cells", &["k", "out", "id", "val"], &["tmp"], &["tmp"])
    );
    // Narrowed to the key, every other cell is left out, in each instance too.
    assert_eq!(
        result_of("inside"),
        result("cells", &["id"], &["k", "out", "val", "tmp"], &["tmp"])
    );
    // Narrowed to a cell of the instances, the key the Map holds each instance by is compared.
    assert_eq!(
        result_of("val"),
        result("cells", &["id", "val"], &["k", "out", "tmp"], &["tmp"])
    );
    // Leaving the enclosing <threads> out leaves <tmp> out with it.
    assert_eq!(
        result_of("outside"),
        result("cells", &["k", "out"], &["threads"], &["tmp"])
    );

    fs::write(
        dir.join("MUTATIONS.toml"),
        "[[mutation]]\nid = \"spawn-tmp\"\nmisunderstanding = \"a thread starts with tmp one \
         more than its key: only the unobservable <tmp> differs\"\n\n  [[mutation.edit]]\n  \
         rule = \"spawn\"\n  find = \"<tmp> I </tmp>\"\n  replace = \"<tmp> I +Int 1 </tmp>\"\n\n\
         [[mutation]]\nid = \"spawn-id\"\nmisunderstanding = \"a thread is keyed one more than \
         asked\"\n\n  [[mutation.edit]]\n  rule = \"spawn\"\n  find = \"<id> I </id>\"\n  \
         replace = \"<id> I +Int 1 </id>\"\n\n\
         [[mutation]]\nid = \"spawn-val\"\nmisunderstanding = \"a thread starts with val one \
         more than its key: the compared <val> differs\"\n\n  [[mutation.edit]]\n  \
         rule = \"spawn\"\n  find = \"<val> I </val>\"\n  replace = \"<val> I +Int 1 </val>\"\n",
    )
    .unwrap();
    let document = search(&manifest("collection"));
    assert_eq!(
        statuses(&document),
        pairs(&[
            ("spawn-tmp", "survived"),
            ("spawn-id", "killed"),
            ("spawn-val", "killed")
        ]),
        "{document:#}"
    );
    assert_eq!(
        document["result"],
        result("cells", &["k", "out", "id", "val"], &["tmp"], &["tmp"])
    );
    // Narrowed to the key, the slot still tells the threads apart by it, and leaves <val> out of
    // each instance.
    let document = search(&manifest("inside"));
    assert_eq!(
        statuses(&document),
        pairs(&[
            ("spawn-tmp", "survived"),
            ("spawn-id", "killed"),
            ("spawn-val", "survived")
        ]),
        "{document:#}"
    );
    // Narrowed to <val>, a change to it inside an instance kills the mutant; the key is compared
    // with it.
    let document = search(&manifest("val"));
    assert_eq!(
        statuses(&document),
        pairs(&[
            ("spawn-tmp", "survived"),
            ("spawn-id", "killed"),
            ("spawn-val", "killed")
        ]),
        "{document:#}"
    );
    let killed = &document["mutations"][2]["executed"][0];
    assert_eq!(
        killed["slots"]["cells"]["outcome"], "distinguish",
        "{killed:#}"
    );
}

/// A Map's key is never left out: an unobservable key is refused at stage `result`, whether the
/// slot leaves out the unobservable cells alone or a narrowing compares a cell of the instances,
/// whose key it then compares; a narrowing that leaves the whole collection out is admitted.
#[test]
fn an_unobservable_map_key_is_refused_unless_the_narrowing_leaves_the_collection_out() {
    let key = |result: &str| {
        format!(
            "[spec]\nentry = \"collectionkey.k\"\nmain_module = \"COLLECTIONKEY\"\n\
             syntax_module = \"COLLECTIONKEY-SYNTAX\"\n{result}\n\
             [[program]]\nid = \"one\"\ntext = \"emit(1)\"\n"
        )
    };
    let dir = fixture(
        "collectionkey",
        &[
            ("key", &key("")),
            (
                "inside",
                &key("[[projection]]\nname = \"p\"\ncompare = [\"tmp\"]\n"),
            ),
            (
                "outside",
                &key("[[projection]]\nname = \"p\"\ncompare = [\"out\"]\n"),
            ),
        ],
    );
    let admitted =
        |name: &str| admit(&FlowManifest::read(&dir.join(format!("FLOW-{name}.toml"))).unwrap());
    for name in ["key", "inside"] {
        let (stage, reason, detail) = refusal(&admitted(name));
        assert_eq!(
            (stage.as_str(), reason.as_str()),
            ("result", "map-key-left-out"),
            "{name}: {detail}"
        );
        assert!(
            detail.contains("<id> is left out, but it is the key")
                && detail.contains("Map cell <thread>"),
            "{name}: {detail}"
        );
    }
    let outside = admitted("outside");
    let spec = outside.spec.as_ref().expect("admitted");
    assert_eq!(
        spec.result.value(),
        result("cells", &["out"], &["k", "threads"], &["id"])
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
    // A manifest without `[[projection]]` has the payload it had before projections existed.
    let manifest = FlowManifest::decode(&plain, &directory).unwrap();
    assert!(
        kink_flow::digest::spec_payload(&manifest, &[])
            .get("result_cells")
            .is_none()
    );
}

/// The record keeps the union of the cells the projections compare (projections package, gate
/// G4): one projection narrowing to `<k>` has the payload member `[result] cells = ["k"]` had; a
/// second projection inside the union, or another order, does not re-key; a projection that keeps
/// every cell (no `compare`, or `accepts`) narrows nothing, so the manifest keeps the digest it
/// had without projections.
#[test]
fn the_record_keeps_the_union_of_the_projections_cells() {
    let directory = flow();
    let plain = fs::read_to_string(directory.join("FLOW.toml")).unwrap();
    let with =
        |projections: &str| plain.replace("[[program]]", &format!("{projections}[[program]]"));
    let manifest = |text: &str| FlowManifest::decode(text, &directory).unwrap();
    let digest = |text: &str| spec_digest(&manifest(text), &[]);
    let one = with("[[projection]]\nname = \"p\"\ncompare = [\"k\"]\n\n");
    assert_eq!(
        kink_flow::digest::spec_payload(&manifest(&one), &[])["result_cells"],
        json!(["k"])
    );
    let two = with(
        "[[projection]]\nname = \"p\"\ncompare = [\"out\", \"k\"]\n\n\
         [[projection]]\nname = \"q\"\ncompare = [\"k\"]\n\n",
    );
    assert_eq!(digest(&two), digest(&narrowed("[\"k\", \"out\"]")));
    assert_eq!(
        kink_flow::digest::spec_payload(&manifest(&two), &[])["result_cells"],
        json!(["k", "out"])
    );
    for every in [
        "[[projection]]\nname = \"all\"\n\n",
        "[[projection]]\nname = \"p\"\ncompare = [\"k\"]\n\n[[projection]]\nname = \"a\"\nkind = \"accepts\"\n\n",
    ] {
        let text = with(every);
        assert!(
            kink_flow::digest::spec_payload(&manifest(&text), &[])
                .get("result_cells")
                .is_none(),
            "{every}"
        );
        assert_eq!(digest(&text), digest(&plain), "{every}");
    }
}

/// kink-flow's own K front end refuses a projection compared through `views` or an `observer`
/// before it loads the specification (projections package, README D3).
#[test]
fn check_refuses_a_projection_with_views_under_the_k_front_end() {
    let plain = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    let viewed = plain.replace(
        "[[program]]",
        "[[projection]]\nname = \"v\"\nviews = { out = \"OutView\" }\n\n[[program]]",
    );
    let dir = fixture("views", &[("views", &viewed)]);
    let (document, status) = check(&dir.join("FLOW-views.toml"));
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    assert_eq!(document["spec"]["stage"], "projection", "{document:#}");
    assert_eq!(
        document["spec"]["reason"], "unsupported-front-end",
        "{document:#}"
    );
    assert_eq!(document["result"], Value::Null);
    // The refused document still names the projection, and says that no front end identified
    // the functions it compares through.
    assert_eq!(
        document["projections"],
        json!([{"name": "v", "kind": "end", "views": {"out": "OutView"}, "observation": null}]),
        "{document:#}"
    );
    // A front end that resolves them states their identity, which the document names.
    let identity = json!({"observer": {"definition": null, "definition_ir": "ab12"}});
    let manifest = FlowManifest::read(&dir.join("FLOW-views.toml"))
        .unwrap()
        .with_projection_observation("v", identity.clone());
    let document = check_document(&admit(&manifest));
    assert_eq!(
        document["projections"][0]["observation"], identity,
        "{document:#}"
    );
}

/// `verb` on `manifest` through the command line's dispatch, with the flow's mutation list for
/// `run` and no pattern list.
fn dispatched(manifest: &Path, verb: &str) -> (Value, u8) {
    let files = CommandFiles {
        mutations: (verb == "run").then(|| manifest.with_file_name("MUTATIONS.toml")),
        patterns: None,
        templates: None,
    };
    let command = FlowCommand::parse(verb, files, &[]).unwrap();
    dispatch(
        FlowManifest::read(manifest).unwrap(),
        command,
        FrontEnd::default(),
    )
    .unwrap()
}

/// Every document of a flow that declares projections names them, each with its keys as
/// written (PJ-10): `check`, `coverage`, `run`, `query` (refused here: the flow has no pattern),
/// `compare` (refused: kink-flow's front end compares no implementation) and `prune`. The
/// identity a front end states for a projection's functions is in no digest.
#[test]
fn every_document_names_the_projections_it_measured_under() {
    let declared = plain_with(
        "[[projection]]\nname = \"p\"\ncompare = [\"k\"]\n\n[[projection]]\nname = \"q\"\n\
         compare = [\"out\"]\ndomain = [\"b*\"]\n\n",
    );
    let dir = fixture("named", &[("named", &declared)]);
    let manifest = dir.join("FLOW-named.toml");
    let projections = json!([
        {"name": "p", "kind": "end", "compare": ["k"]},
        {"name": "q", "kind": "end", "compare": ["out"], "domain": ["b*"]},
    ]);
    for verb in ["check", "coverage", "run", "query", "compare", "prune"] {
        let (document, _) = dispatched(&manifest, verb);
        assert_eq!(document["projections"], projections, "{verb}: {document:#}");
    }
    // The documents of a flow without projections have none, whatever the verb.
    for verb in ["query", "compare"] {
        let (document, _) = dispatched(&dir.join("FLOW.toml"), verb);
        assert_eq!(document.get("projections"), None, "{verb}: {document:#}");
    }
    let read = FlowManifest::read(&manifest).unwrap();
    assert_eq!(
        spec_digest(&read, &[]),
        spec_digest(
            &read.clone().with_projection_observation("p", json!("x")),
            &[]
        )
    );
}

/// The unobservable fixture's `FLOW.toml` with `projections` before its program.
fn plain_with(projections: &str) -> String {
    fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace("[[program]]", &format!("{projections}[[program]]"))
}

/// A flow whose projections are all `trace` projections keeps no cell of the end: every cell the
/// specification declares is left out of the second slot, which then compares only the run's
/// stop, and the channels decide.
#[test]
fn trace_projections_alone_keep_no_cell_of_the_end() {
    let plain = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    let traced = plain.replace(
        "[[program]]",
        "[[observe.point]]\nname = \"emits\"\nafter = [\"UNOBS.emit\"]\nstutter = \"count\"\n\
         cells = [\"out\"]\n\n[[projection]]\nname = \"t\"\nkind = \"trace\"\n\
         channels = [\"emits\"]\n\n[[program]]",
    );
    let dir = fixture("traces", &[("traces", &traced)]);
    let admission = admit(&FlowManifest::read(&dir.join("FLOW-traces.toml")).unwrap());
    let spec = admission
        .spec
        .as_ref()
        .unwrap_or_else(|| panic!("{:?}", admission.record.refusal));
    assert_eq!(
        spec.result.value(),
        result("cells", &[], &["k", "out", "scratch"], &["scratch"])
    );
}

/// A manifest for `nested.k`, with `result` (a `[[projection]]` or nothing) before its program.
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
            (
                "state",
                &nested("[[projection]]\nname = \"p\"\ncompare = [\"state\"]\n"),
            ),
            (
                "out",
                &nested("[[projection]]\nname = \"p\"\ncompare = [\"out\"]\n"),
            ),
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
            None,
            None,
            None,
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

/// kink-flow's K front end checks every projection's `compare` against the configuration, also
/// where another projection keeps every cell in the record and so the record does not narrow to
/// it: such a `compare` is refused as it would be were its projection the flow's only one, and
/// one the configuration holds leaves the record as the other projection keeps it.
#[test]
fn a_projection_s_compare_is_checked_where_the_record_does_not_narrow_to_it() {
    let beside = |cells: &str| {
        plain_with(&format!(
            "[[projection]]\nname = \"all\"\n\n[[projection]]\nname = \"p\"\ncompare = {cells}\n\n"
        ))
    };
    let dir = fixture(
        "compare-checked",
        &[
            ("nope", &beside("[\"nope\"]")),
            ("scratch", &beside("[\"out\", \"scratch\"]")),
            ("out", &beside("[\"out\"]")),
        ],
    );
    let admitted =
        |name: &str| admit(&FlowManifest::read(&dir.join(format!("FLOW-{name}.toml"))).unwrap());
    for (name, reason, cell) in [
        ("nope", "result-cell-unknown", "<nope>"),
        ("scratch", "result-cell-unobservable", "<scratch>"),
    ] {
        let (stage, found, detail) = refusal(&admitted(name));
        assert_eq!(
            (stage.as_str(), found.as_str()),
            ("result", reason),
            "{name}: {detail}"
        );
        assert!(
            detail.contains(cell) && detail.contains("projection `p`"),
            "{name}: {detail}"
        );
    }
    let out = admitted("out");
    let spec = out.spec.as_ref().expect("admitted");
    assert_eq!(
        spec.result.value(),
        result("cells", &["k", "out"], &["scratch"], &["scratch"])
    );
}

/// A front end for compare whose every end view is `equal`: compare needs one, and kink-flow's
/// own front end has none.
struct Equal;

impl kink_flow::compare::Vocabulary for Equal {
    fn check(&self, _: &kink_flow::manifest::ImplementationSection) -> Result<(), String> {
        Ok(())
    }
    fn start(&self, _: &k_rust::kore::ast::Pattern) -> Result<Value, String> {
        Err("no start is asked".to_owned())
    }
    fn inputs(
        &self,
        _: &kink_flow::manifest::Program,
        _: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<Value, String> {
        Ok(json!({}))
    }
    fn read_answer(
        &self,
        _: &kink_flow::manifest::ImplementationSection,
        _: &Value,
    ) -> Result<(), String> {
        Ok(())
    }
    fn compare(
        &self,
        _: &kink_flow::compare::Question<'_>,
    ) -> Result<kink_flow::compare::Judged, String> {
        Ok(kink_flow::compare::Judged::Equal {
            omitted: Vec::new(),
            compared_cells: 1,
        })
    }
    fn observe_request(&self, _: &[String]) -> Result<Vec<Value>, String> {
        Err("no channel is asked".to_owned())
    }
    fn judge_trace(
        &self,
        _: &kink_flow::compare::TraceQuestion<'_>,
    ) -> Result<kink_flow::compare::TraceAnswer, String> {
        Err("no channel is asked".to_owned())
    }
}

/// A program outside the domain of the projection a view names is neither compared nor counted
/// under that view: its row is `not-compared` (`outside-domain`, status 0), the implementation is
/// not asked where no view applies to the program, the summary counts the view on the programs
/// of its domain only, and the lock holds the row and counts the view from the rows it holds.
#[test]
fn a_view_compares_only_the_programs_of_its_projection_s_domain() {
    let answer = |log: &str| {
        format!(
            "[\"sh\", \"-c\", \"cat >> {log}; echo >> {log}; echo '{{\\\"end\\\": \\\"final\\\", \
             \\\"cells\\\": {{}}}}'\"]"
        )
    };
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"p\"\ndomain = [\"both\"]\n\n[[program]]",
        )
        + &format!(
            "\n[[program]]\nid = \"two\"\ntext = \"emit(2)\"\n\n\
             [[implementation]]\nname = \"wide\"\ngiven = \"inputs\"\ncommand = {}\nviews = [\n  \
             {{ projection = \"p\", required = true }},\n  {{ name = \"all\", required = true }},\n]\n\n\
             [[implementation]]\nname = \"narrow\"\ngiven = \"inputs\"\ncommand = {}\nviews = [{{ projection = \"p\", \
             required = true }}]\n",
            answer("wide.log"),
            answer("narrow.log")
        );
    let dir = fixture("domain", &[("domain", &manifest)]);
    let read = FlowManifest::read(&dir.join("FLOW-domain.toml")).unwrap();
    let lock = dir.join("kink.lock");
    let options = kink_flow::compare::CompareOptions {
        lock: Some(lock.clone()),
        ..Default::default()
    };
    let document = kink_flow::compare::command(&read, &options, Some(&Equal), "compare");
    assert_eq!(document["version"], 8, "{document:#}");
    let views = |implementation: &str, program: &str| -> Vec<(String, String, Value)> {
        let row = document["rows"]
            .as_array()
            .unwrap_or_else(|| panic!("{document:#}"))
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .unwrap_or_else(|| panic!("{implementation} {program}: {document:#}"));
        row["views"]
            .as_array()
            .unwrap()
            .iter()
            .map(|view| {
                (
                    view["view"].as_str().unwrap().to_owned(),
                    format!(
                        "{}{}",
                        view["verdict"].as_str().unwrap(),
                        view["reason"]
                            .as_str()
                            .map(|reason| format!(" {reason}"))
                            .unwrap_or_default()
                    ),
                    view["status"].clone(),
                )
            })
            .collect()
    };
    let view =
        |name: &str, verdict: &str, status: Value| (name.to_owned(), verdict.to_owned(), status);
    let outside = || view("p", "not-compared outside-domain", json!(0));
    assert_eq!(
        views("wide", "both"),
        [
            view("p", "equal", Value::Null),
            view("all", "equal", Value::Null)
        ]
    );
    assert_eq!(
        views("wide", "two"),
        [outside(), view("all", "equal", Value::Null)]
    );
    assert_eq!(views("narrow", "both"), [view("p", "equal", Value::Null)]);
    assert_eq!(views("narrow", "two"), [outside()]);
    let row = |implementation: &str, program: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .unwrap()
            .clone()
    };
    let detail = &row("narrow", "two")["views"][0]["detail"];
    assert!(
        detail.as_str().unwrap().contains("projection `p` (`both`)"),
        "{detail}"
    );
    // No view of `narrow` applies to `two`: it was not asked, and its row requires nothing.
    assert_eq!(row("narrow", "two")["request_sha256"], Value::Null);
    assert_eq!(row("narrow", "two")["required"], false);
    assert_eq!(row("wide", "two")["required"], true);
    let asked = |log: &str| {
        fs::read_to_string(dir.join(log))
            .unwrap()
            .lines()
            .filter(|line| !line.is_empty())
            .map(|line| serde_json::from_str::<Value>(line).unwrap()["program"].clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(asked("wide.log"), [json!("both"), json!("two")]);
    assert_eq!(asked("narrow.log"), [json!("both")]);
    // Counted on the programs of the domain only.
    assert_eq!(
        document["summary"]["verdicts"],
        json!({"equal": 4, "different": 0, "could-not-apply": 0, "not-compared": 0}),
        "{document:#}"
    );
    let compared = document["summary"]["views"]
        .as_array()
        .unwrap()
        .iter()
        .map(|view| {
            (
                view["implementation"].as_str().unwrap(),
                view["view"].as_str().unwrap(),
                view["compared"].as_u64().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        compared,
        [("wide", "p", 1), ("wide", "all", 2), ("narrow", "p", 1)]
    );
    assert_eq!(kink_flow::compare::compare_status(&document), EXIT_YES);
    // The lock holds every row, the one outside the domain too, and counts as the summary does.
    let text = fs::read_to_string(&lock).unwrap();
    assert_eq!(
        text.matches("reason = \"outside-domain\"").count(),
        2,
        "{text}"
    );
    let rows = |header: &str| text.lines().filter(|line| *line == header).count();
    assert_eq!(
        (rows("[[compare.verdict]]"), rows("[[compare.view]]")),
        (6, 3),
        "{text}"
    );
    assert!(
        text.contains("view = \"p\"\nrequired = true\ncompared = 1\nagreeing = 1"),
        "{text}"
    );
    let again = kink_flow::compare::command(
        &read,
        &kink_flow::compare::CompareOptions {
            locked: true,
            ..options
        },
        Some(&Equal),
        "compare",
    );
    assert_eq!(again["lock"]["status"], "unchanged", "{:#}", again["lock"]);
}
