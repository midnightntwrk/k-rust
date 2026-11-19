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
    assert_eq!(document["version"], 19);
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
    one_sided_cell_corpus_with("one-sided", "")
}

/// [`one_sided_cell_corpus`] in its own directory `name`, with `projections` (manifest text)
/// before its program.
fn one_sided_cell_corpus_with(name: &str, projections: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-unobservable-{}", std::process::id()))
        .join(name);
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
         [[program]]\nid = \"start\"\ntext = \"start(600)\"\n"
            .replace("[[program]]", &format!("{projections}[[program]]")),
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

/// PJ-11: a one-sided kill is taken by a projection whose observation is the search's own and is
/// never re-judged under a projection judged flow-side. Over [`one_sided_cell_corpus`], `whole`
/// (no `compare`, so the record keeps every observable cell) takes the search's verdict, and `k`
/// compares the same cells but, the record not being narrowed to them, is judged flow-side:
/// `early-k`'s mutant run is cut by its work budget, so its ends are not every end of its run, and
/// its one-sided kill of the cells slot is `unknown` under `k` (the one exception to
/// `a_projection_over_the_runs_cells_gives_the_runners_verdict`), live and from the stores.
#[test]
fn a_one_sided_kill_is_unknown_under_a_projection_judged_flow_side() {
    let manifest = one_sided_cell_corpus_with(
        "one-sided-projected",
        "[[projection]]\nname = \"whole\"\n\n[[projection]]\nname = \"k\"\ncompare = [\"k\"]\n\n",
    );
    let document = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn({
            let manifest = manifest.clone();
            move || search(&manifest)
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(
        statuses(&document),
        pairs(&[("early-k", "killed"), ("early-scratch", "unknown")]),
        "{document:#}"
    );
    let expected = vec![
        quad("early-k", "whole", "killed", Some("start")),
        quad("early-k", "k", "unknown", None),
        quad("early-scratch", "whole", "unknown", None),
        quad("early-scratch", "k", "unknown", None),
    ];
    assert_eq!(projection_statuses(&document), expected, "{document:#}");
    let killed = &document["mutations"][0]["executed"][0];
    assert_eq!(
        killed["slots"]["cells"]["outcome"], "distinguish",
        "{killed:#}"
    );
    assert_ne!(
        killed["slots"]["exit-stop"]["outcome"], "distinguish",
        "{killed:#}"
    );
    assert_eq!(
        killed["difference"]["mutant"]["complete"], false,
        "{killed:#}"
    );
    assert_eq!(
        killed["projections"],
        json!({"whole": "killed", "k": "unknown"}),
        "{killed:#}"
    );
    // A second run reads the outcome record and the stored, incomplete, mutant ends: the same
    // statuses, and no call for the projections.
    let again = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || search(&manifest))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(projection_statuses(&again), expected, "{again:#}");
    for row in again["mutations"].as_array().unwrap() {
        assert_eq!(row["executed"][0]["cached"], true, "{row:#}");
        assert!(
            row["projection_search"]["calls"]
                .as_array()
                .is_none_or(Vec::is_empty),
            "{row:#}"
        );
    }
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
    assert_eq!(document["version"], 11, "{document:#}");
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

/// A front end for compare that reads acceptance: every end view is `equal`, the definition
/// declares a `finished` end, and a `rejected` answer's `refused` is read as written.
struct Accepting;

impl kink_flow::compare::Vocabulary for Accepting {
    fn check(
        &self,
        implementation: &kink_flow::manifest::ImplementationSection,
    ) -> Result<(), String> {
        Equal.check(implementation)
    }
    fn start(&self, state: &k_rust::kore::ast::Pattern) -> Result<Value, String> {
        Equal.start(state)
    }
    fn inputs(
        &self,
        program: &kink_flow::manifest::Program,
        files: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<Value, String> {
        Equal.inputs(program, files)
    }
    fn read_answer(
        &self,
        implementation: &kink_flow::manifest::ImplementationSection,
        cells: &Value,
    ) -> Result<(), String> {
        Equal.read_answer(implementation, cells)
    }
    fn compare(
        &self,
        question: &kink_flow::compare::Question<'_>,
    ) -> Result<kink_flow::compare::Judged, String> {
        Equal.compare(question)
    }
    fn observe_request(&self, channels: &[String]) -> Result<Vec<Value>, String> {
        Equal.observe_request(channels)
    }
    fn judge_trace(
        &self,
        question: &kink_flow::compare::TraceQuestion<'_>,
    ) -> Result<kink_flow::compare::TraceAnswer, String> {
        Equal.judge_trace(question)
    }
    fn declares_finished_end(&self) -> bool {
        true
    }
    fn read_refusal(&self, refused: &Value) -> Result<Value, String> {
        Ok(refused.clone())
    }
}

/// A program whose entry states that it is rejected before it runs (projections PJ-32) and that
/// admission rejected there is rejected on the definition's side: an implementation given the
/// inputs is asked, its acceptance and end views judged by acceptance (`equal` for a rejection,
/// whatever refused end it names, `different` for an end or a crash) and its snapshot view
/// against its file (`pending`: none is accepted); one given `start` is not asked (`not-compared`, `rejected-before-run`, status 0). An unmet statement is
/// asked of none, every view `not-compared` (`definition`, status 2). The lock holds the reason.
#[test]
fn a_program_rejected_before_it_runs_is_rejected_on_the_definition_side() {
    const BOTH: &str = "{ name = \"accepts\", kind = \"accepts\", required = true }, \
                        { name = \"end\", required = true }";
    const ACCEPTS: &str = "{ name = \"accepts\", kind = \"accepts\", required = true }";
    let answer = |log: &str, answer: &str| {
        format!(
            "[\"sh\", \"-c\", \"cat >> {log}; echo >> {log}; {answer}\"]",
            answer = answer.replace('"', "\\\"")
        )
    };
    let implementation = |name: &str, given: &str, command: &str, views: &str| {
        format!(
            "\n[[implementation]]\nname = \"{name}\"\nprotocol = \"kink-implementation/3\"\n\
             given = \"{given}\"\ncommand = {command}\nviews = [{views}]\n"
        )
    };
    let manifest = fs::read_to_string(flow().join("FLOW.toml")).unwrap()
        + "\n[[program]]\nid = \"bad\"\ntext = \"emit(\"\nexpect = { rejected = \"parse\" }\n\n\
           [[program]]\nid = \"good\"\ntext = \"emit(3)\"\nexpect = { rejected = \"parse\" }\n\n\
           [[projection]]\nname = \"msg\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n"
        + &implementation(
            "parser",
            "inputs",
            &answer(
                "parser.log",
                "echo '{\"end\": \"rejected\", \"message\": \"no\"}'",
            ),
            &format!("{BOTH}, {{ projection = \"msg\", required = false }}"),
        )
        + &implementation(
            "named",
            "inputs",
            &answer(
                "named.log",
                "echo '{\"end\": \"rejected\", \"refused\": {\"end\": \"x\"}}'",
            ),
            ACCEPTS,
        )
        + &implementation(
            "acceptor",
            "inputs",
            &answer("acceptor.log", "echo '{\"end\": \"final\", \"cells\": {}}'"),
            BOTH,
        )
        + &implementation(
            "crasher",
            "inputs",
            &answer("crasher.log", "exit 3"),
            ACCEPTS,
        )
        + &implementation(
            "starter",
            "start",
            &answer("starter.log", "echo '{\"end\": \"rejected\"}'"),
            ACCEPTS,
        );
    let dir = fixture("rejected", &[("rejected", &manifest)]);
    let read = FlowManifest::read(&dir.join("FLOW-rejected.toml")).unwrap();
    let lock = dir.join("kink.lock");
    let options = kink_flow::compare::CompareOptions {
        lock: Some(lock.clone()),
        ..Default::default()
    };
    let document = kink_flow::compare::command(&read, &options, Some(&Accepting), "compare");
    assert_eq!(document["version"], 11, "{document:#}");
    assert!(document["refusal"].is_null(), "{document:#}");
    let class = |program: &str| {
        document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == program)
            .unwrap()["class"]
            .clone()
    };
    assert_eq!(
        (class("both"), class("bad"), class("good")),
        (json!("comparable"), json!("rejected"), json!("accepted"))
    );
    let row = |implementation: &str, program: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .unwrap_or_else(|| panic!("{implementation} {program}: {document:#}"))
            .clone()
    };
    let views = |implementation: &str, program: &str| -> Vec<(String, String, Value)> {
        row(implementation, program)["views"]
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
    let difference = |implementation: &str, index: usize| {
        row(implementation, "bad")["views"][index]["difference"].clone()
    };
    let accepts = |implementation: &str| json!({"format": "kink-accepts/1", "definition": "rejects", "implementation": implementation});
    // Asked with its inputs, and judged by acceptance.
    assert_eq!(
        views("parser", "bad")[..2],
        [
            view("accepts", "equal", Value::Null),
            view("end", "equal", Value::Null)
        ]
    );
    // Its snapshot view judges the answer alone: no value is accepted for it yet.
    assert_eq!(views("parser", "bad")[2].1, "pending");
    assert!(row("parser", "bad")["request_sha256"].is_string());
    assert_eq!(
        views("acceptor", "bad"),
        [
            view("accepts", "different", Value::Null),
            view("end", "different", Value::Null)
        ]
    );
    assert_eq!(
        (difference("acceptor", 0), difference("acceptor", 1)),
        (accepts("accepts"), accepts("accepts"))
    );
    // The definition's rejection states no declared class, so `refused` is compared with
    // nothing.
    assert_eq!(
        views("named", "bad"),
        [view("accepts", "equal", Value::Null)]
    );
    assert!(row("named", "bad")["views"][0].get("refused").is_none());
    assert_eq!(
        views("crasher", "bad"),
        [view("accepts", "different", Value::Null)]
    );
    assert_eq!(difference("crasher", 0), accepts("crashed"));
    assert_eq!(row("crasher", "bad")["failure"]["kind"], "exit");
    // Given `start`: there is none, so it is not asked, and its required view decides nothing.
    assert_eq!(
        views("starter", "bad"),
        [view(
            "accepts",
            "not-compared rejected-before-run",
            json!(0)
        )]
    );
    let detail = &row("starter", "bad")["views"][0]["detail"];
    assert!(detail.as_str().unwrap().contains("no start"), "{detail}");
    assert!(row("starter", "bad")["request_sha256"].is_null());
    assert_eq!(
        kink_flow::compare::row_status(&row("starter", "bad")),
        EXIT_YES
    );
    // An unmet statement: nothing is asked of any implementation.
    for implementation in ["parser", "named", "acceptor", "crasher", "starter"] {
        assert!(row(implementation, "good")["request_sha256"].is_null());
        assert!(
            row(implementation, "good")["views"]
                .as_array()
                .unwrap()
                .iter()
                .all(|view| view["verdict"] == "not-compared"
                    && view["reason"] == "definition"
                    && view["status"] == EXIT_UNASKED),
            "{implementation}: {document:#}"
        );
    }
    let asked = |log: &str| {
        fs::read_to_string(dir.join(log))
            .unwrap_or_default()
            .lines()
            .filter(|line| !line.is_empty())
            .map(|line| serde_json::from_str::<Value>(line).unwrap()["program"].clone())
            .collect::<Vec<_>>()
    };
    for log in ["parser.log", "named.log", "acceptor.log", "crasher.log"] {
        assert_eq!(asked(log), [json!("both"), json!("bad")], "{log}");
    }
    assert!(!asked("starter.log").contains(&json!("bad")));
    assert_eq!(kink_flow::compare::compare_status(&document), EXIT_UNASKED);
    let text = fs::read_to_string(&lock).unwrap();
    assert_eq!(
        text.matches("reason = \"rejected-before-run\"").count(),
        1,
        "{text}"
    );
}

/// `FLOW-plain.toml` (every cell of `plain.k` observable) with `extra` (projections, `[run]`)
/// before its program.
fn plain_projected(extra: &str) -> String {
    fs::read_to_string(flow().join("FLOW-plain.toml"))
        .unwrap()
        .replace("[[program]]", &format!("{extra}[[program]]"))
}

/// Each row's `projections`, `(mutation, projection) -> (status, killer)`, in row and list order.
fn projection_statuses(document: &Value) -> Vec<(String, String, String, Option<String>)> {
    document["mutations"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .flat_map(|row| {
            row["projections"]
                .as_array()
                .unwrap_or_else(|| panic!("no projections in {row:#}"))
                .iter()
                .map(|entry| {
                    (
                        row["id"].as_str().unwrap().to_owned(),
                        entry["name"].as_str().unwrap().to_owned(),
                        entry["status"].as_str().unwrap().to_owned(),
                        entry["killer"].as_str().map(str::to_owned),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn quad(
    mutation: &str,
    projection: &str,
    status: &str,
    killer: Option<&str>,
) -> (String, String, String, Option<String>) {
    (
        mutation.to_owned(),
        projection.to_owned(),
        status.to_owned(),
        killer.map(str::to_owned),
    )
}

/// PJ-11: a mutation the run kills on the union of the projections' cells is judged under each
/// listed projection: `note-offset` changes `<scratch>` only, so it survives under `out` and is
/// killed under `scratch`; `emit-offset` the reverse. Each kill under a projection is a kill of
/// the run's own slots (an `end` projection can turn a kill into a survival, never the reverse). A
/// second run, which tier 1 decides from the outcome records, reads the mutant's ends from the
/// ends store and gives the same statuses.
#[test]
fn kills_are_judged_under_each_listed_projection() {
    let text = plain_projected(
        "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
         [[projection]]\nname = \"scratch\"\ncompare = [\"scratch\"]\n\n",
    );
    let dir = fixture("projections", &[("projections", &text)]);
    let manifest = dir.join("FLOW-projections.toml");
    let document = search(&manifest);
    assert_eq!(
        statuses(&document),
        pairs(&[("note-offset", "killed"), ("emit-offset", "killed")])
    );
    let expected = vec![
        quad("note-offset", "out", "survived", None),
        quad("note-offset", "scratch", "killed", Some("both")),
        quad("emit-offset", "out", "killed", Some("both")),
        quad("emit-offset", "scratch", "survived", None),
    ];
    assert_eq!(projection_statuses(&document), expected, "{document:#}");
    for row in document["mutations"].as_array().unwrap() {
        let entry = &row["executed"][0];
        assert_eq!(entry["cached"], false, "{entry:#}");
        for (name, verdict) in entry["projections"].as_object().unwrap() {
            if verdict == "killed" {
                assert!(
                    ["exit-stop", "cells"]
                        .iter()
                        .any(|slot| entry["slots"][slot]["outcome"] == "distinguish"),
                    "{name}: {entry:#}"
                );
            }
        }
    }
    let again = search(&manifest);
    assert!(
        again["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row["executed"][0]["cached"] == true),
        "{again:#}"
    );
    assert_eq!(projection_statuses(&again), expected, "{again:#}");
}

/// A projection whose observation is the run's own takes the row's verdict; one judged
/// flow-side over the same cells (`cells3` compares every cell of `plain.k` while `whole`, with
/// no `compare`, keeps the record unnarrowed) gives the runner's verdict on every program: the
/// flow-side relation is the runner's.
#[test]
fn a_projection_over_the_runs_cells_gives_the_runners_verdict() {
    let text = plain_projected(
        "[[projection]]\nname = \"whole\"\n\n\
         [[projection]]\nname = \"cells3\"\ncompare = [\"k\", \"out\", \"scratch\"]\n\n",
    );
    let dir = fixture("runners", &[("runners", &text)]);
    let document = search(&dir.join("FLOW-runners.toml"));
    for row in document["mutations"].as_array().unwrap() {
        let statuses = row["projections"].as_array().unwrap();
        for entry in statuses {
            assert_eq!(entry["status"], row["status"], "{row:#}");
            assert_eq!(entry["killer"], row["killer"], "{row:#}");
        }
        for entry in row["executed"].as_array().unwrap() {
            let verdicts = &entry["projections"];
            let runner = if entry["slots"]
                .as_object()
                .unwrap()
                .values()
                .any(|slot| slot["outcome"] == "distinguish")
            {
                "killed"
            } else {
                "agree"
            };
            assert_eq!(
                verdicts,
                &json!({"whole": runner, "cells3": runner}),
                "{entry:#}"
            );
        }
    }
}

/// `[run] projections` selects the projections `run` judges under, in its order; a projection's
/// `domain` keeps the programs outside it out of its judgement and its count (an executed entry
/// names them `outside-domain`, as `compare` does); an `accepts` projection observes nothing under
/// kink-flow's own front end, which declares no `finished` end (`unknown`, `no-finished-end`);
/// a projection under which the search's first killing program agrees has the programs of its
/// domain after it run (the search under the projections, `projection_search`), as has a
/// projection that observes what the search does (`whole`) over its domain only. The corpus is
/// `both` and `other` (`emit(3)`): the search kills both mutations at `both`, the first program
/// of the search order. A second run reads every program from the stores and makes no call.
#[test]
fn run_judges_the_listed_projections_within_their_domain() {
    let text = format!(
        "{}\n[[program]]\nid = \"other\"\ntext = \"emit(3)\"\n",
        plain_projected(
            "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
             [[projection]]\nname = \"mine\"\ncompare = [\"out\"]\ndomain = [\"both\"]\n\n\
             [[projection]]\nname = \"acc\"\nkind = \"accepts\"\n\n\
             [[projection]]\nname = \"whole\"\ndomain = [\"other\"]\n\n\
             [run]\nprojections = [\"mine\", \"acc\", \"out\", \"whole\"]\n\n",
        )
    );
    let dir = fixture("listed", &[("listed", &text)]);
    let document = search(&dir.join("FLOW-listed.toml"));
    let rows = document["mutations"].as_array().unwrap();
    let note = &rows[0];
    assert_eq!(note["id"], "note-offset");
    assert_eq!(note["status"], "killed", "{note:#}");
    assert_eq!(
        note["projections"],
        json!([
            {"name": "mine", "status": "survived", "killer": null, "reason": null},
            {"name": "acc", "status": "unknown", "killer": null, "reason": "no-finished-end"},
            {"name": "out", "status": "survived", "killer": null, "reason": null},
            {"name": "whole", "status": "survived", "killer": null, "reason": null},
        ]),
        "{note:#}"
    );
    // The row is the search's: `other` ran only for the projections, in a call of its own.
    assert_eq!(note["killer"], "both", "{note:#}");
    assert_eq!(note["executed"].as_array().unwrap().len(), 1, "{note:#}");
    assert_eq!(note["calls"].as_array().unwrap().len(), 1, "{note:#}");
    let searched = &note["projection_search"];
    assert_eq!(
        searched["calls"],
        json!([{"programs": ["other"], "status": "survived"}]),
        "{note:#}"
    );
    assert_eq!(searched["executed"][0]["program"], "other", "{note:#}");
    assert_eq!(searched["executed"][0]["cached"], false, "{note:#}");
    assert_eq!(
        searched["executed"][0]["projections"],
        json!({"mine": "outside-domain", "out": "agree", "whole": "agree"}),
        "{note:#}"
    );
    let emit = &rows[1];
    assert_eq!(emit["id"], "emit-offset");
    assert_eq!(
        emit["projections"],
        json!([
            {"name": "mine", "status": "killed", "killer": "both", "reason": null},
            {"name": "acc", "status": "unknown", "killer": null, "reason": "no-finished-end"},
            {"name": "out", "status": "killed", "killer": "both", "reason": null},
            {"name": "whole", "status": "killed", "killer": "other", "reason": null},
        ]),
        "{emit:#}"
    );
    assert_eq!(
        emit["executed"][0]["projections"],
        json!({"mine": "killed", "out": "killed", "whole": "outside-domain"})
    );
    assert_eq!(
        emit["projection_search"]["calls"],
        json!([{"programs": ["other"], "status": "killed"}]),
        "{emit:#}"
    );
    // A second run: tier 1 decides each row from `both`'s record, and the projections read
    // `other`'s record (and its ends record, where its cells slot distinguished): no call.
    let again = search(&dir.join("FLOW-listed.toml"));
    for (row, first) in again["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .zip(document["mutations"].as_array().unwrap())
    {
        assert_eq!(row["projections"], first["projections"], "{row:#}");
        assert_eq!(row["projection_search"]["calls"], json!([]), "{row:#}");
        assert_eq!(
            row["projection_search"]["executed"][0]["cached"], true,
            "{row:#}"
        );
        assert_eq!(
            row["projection_search"]["executed"][0]["projections"],
            first["projection_search"]["executed"][0]["projections"],
            "{row:#}"
        );
    }
    // Under `--full` every program runs: `other` is outside `mine`'s domain.
    let (full, _) = run(
        &FlowManifest::read(&dir.join("FLOW-listed.toml")).unwrap(),
        &MutationList::read(&dir.join("MUTATIONS.toml")).unwrap(),
        &RunOptions {
            schedule: kink_campaign::ScheduleMode::Full,
            ..RunOptions::default()
        },
    );
    let note = &full["mutations"][0];
    let other = note["executed"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["program"] == "other")
        .unwrap_or_else(|| panic!("{note:#}"));
    assert_eq!(
        other["projections"],
        json!({"mine": "outside-domain", "out": "agree", "whole": "agree"}),
        "{other:#}"
    );
    assert_eq!(note["projections"][0]["status"], "survived", "{note:#}");
    assert_eq!(note["projections"][2]["status"], "survived", "{note:#}");
    assert_eq!(note["projections"][3]["status"], "survived", "{note:#}");
    // `whole` observes what the search does, over its domain only: `both`, the row's killer, is
    // outside it, and `other` kills.
    let emit = &full["mutations"][1];
    assert_eq!(emit["killer"], "both", "{emit:#}");
    assert_eq!(
        emit["projections"][3],
        json!({"name": "whole", "status": "killed", "killer": "other", "reason": null}),
        "{emit:#}"
    );
}

/// `plain_projected(extra)` with the program `other` (`emit(3)`) after `both`.
fn with_other(extra: &str) -> String {
    format!(
        "{}\n[[program]]\nid = \"other\"\ntext = \"emit(3)\"\n",
        plain_projected(extra)
    )
}

/// The row's members a run gives whatever the stores held: status, killer, each projection's
/// status, and the programs and status of each call of the search under the projections.
fn searched(document: &Value) -> Vec<Value> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            json!({
                "status": row["status"],
                "killer": row["killer"],
                "projections": row["projections"],
                "programs": row["projection_search"]["executed"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|entry| json!([entry["program"], entry["projections"]]))
                    .collect::<Vec<_>>(),
            })
        })
        .collect()
}

/// The search under the projections goes round by round: each call ends at the next program the
/// run's slots kill, and the next call runs what a projection still needs after it. The corpus is
/// `both`, `n2` (`note(5)`) and `e3` (`emit(3)`): `note-offset` is killed at `both`, which agrees
/// under `out`; the first call over `n2` and `e3` stops at `n2` (killed on `<scratch>`, agreeing
/// under `out`), and a second runs `e3`; `emit-offset` the same way under `scratch`. Every status
/// and killer under each projection is the one `--full` gives, and a second run makes no call.
#[test]
fn the_search_under_the_projections_runs_round_by_round() {
    let text = format!(
        "{}\n[[program]]\nid = \"n2\"\ntext = \"note(5)\"\n\n[[program]]\nid = \"e3\"\ntext = \"emit(3)\"\n",
        plain_projected(
            "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
             [[projection]]\nname = \"scratch\"\ncompare = [\"scratch\"]\n\n",
        )
    );
    let dir = fixture("rounds", &[("rounds", &text)]);
    let manifest = dir.join("FLOW-rounds.toml");
    let document = search(&manifest);
    let rows = document["mutations"].as_array().unwrap();
    let calls = |row: &Value| row["projection_search"]["calls"].clone();
    assert_eq!(rows[0]["killer"], "both", "{document:#}");
    assert_eq!(
        calls(&rows[0]),
        json!([
            {"programs": ["n2", "e3"], "status": "killed"},
            {"programs": ["e3"], "status": "survived"},
        ]),
        "{document:#}"
    );
    assert_eq!(
        calls(&rows[1]),
        json!([
            {"programs": ["e3", "n2"], "status": "killed"},
            {"programs": ["n2"], "status": "survived"},
        ]),
        "{document:#}"
    );
    // Each program the projections ran is listed once, with its verdicts; a test a call
    // skipped after its kill is not listed.
    for row in rows {
        let programs = row["projection_search"]["executed"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["program"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(programs.len(), 2, "{row:#}");
        assert!(programs.contains(&"n2".to_owned()) && programs.contains(&"e3".to_owned()));
    }
    let expected = vec![
        quad("note-offset", "out", "survived", None),
        quad("note-offset", "scratch", "killed", Some("both")),
        quad("emit-offset", "out", "killed", Some("both")),
        quad("emit-offset", "scratch", "survived", None),
    ];
    assert_eq!(projection_statuses(&document), expected, "{document:#}");
    let (full, _) = run(
        &FlowManifest::read(&manifest).unwrap(),
        &MutationList::read(&dir.join("MUTATIONS.toml")).unwrap(),
        &RunOptions {
            schedule: kink_campaign::ScheduleMode::Full,
            ..RunOptions::default()
        },
    );
    assert_eq!(projection_statuses(&full), expected, "{full:#}");
    let again = search(&manifest);
    for row in again["mutations"].as_array().unwrap() {
        assert_eq!(calls(row), json!([]), "{row:#}");
    }
    assert_eq!(projection_statuses(&again), expected, "{again:#}");
}

/// A row tier 1 decides from the resolution memo's facts, whose search under the projections
/// still needs a program no record holds, is resolved live (a memo's facts carry no mutant to
/// run): the row is the one a run with empty stores gives. The first run lists only `whole`,
/// the run's own observation, so nothing runs past `both`; the second adds `out`, over the same
/// record, under which `note-offset` needs `other`.
#[test]
fn a_row_the_memo_decides_runs_what_its_projections_need() {
    let first = with_other("[[projection]]\nname = \"whole\"\n\n");
    let second = with_other(
        "[[projection]]\nname = \"whole\"\n\n[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n",
    );
    let dir = fixture("memo", &[("first", &first), ("second", &second)]);
    let before = search(&dir.join("FLOW-first.toml"));
    assert!(
        before["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row.get("projection_search").is_none()),
        "{before:#}"
    );
    assert!(dir.join(".kink-flow/memo").is_dir());
    let warm = search(&dir.join("FLOW-second.toml"));
    let cold_dir = fixture("memo-cold", &[("second", &second)]);
    let cold = search(&cold_dir.join("FLOW-second.toml"));
    assert_eq!(searched(&warm), searched(&cold), "{warm:#}");
    // The row itself is tier 1's: no call of its own.
    let row = &warm["mutations"][0];
    assert_eq!(row["executed"][0]["cached"], true, "{row:#}");
    assert_eq!(row["calls"], json!([]), "{row:#}");
    assert_eq!(
        warm["mutations"][0]["projection_search"]["calls"],
        json!([{"programs": ["other"], "status": "survived"}]),
        "{warm:#}"
    );
}

/// The mutant ends record of `program` for `mutation` under the flow's cache in `dir`, and its
/// path.
fn ends_record(dir: &Path, mutation: &str, program: &str) -> (PathBuf, Value) {
    let mut found = Vec::new();
    for context in fs::read_dir(dir.join(".kink-flow/mutant-ends")).unwrap() {
        for identity in fs::read_dir(context.unwrap().path()).unwrap() {
            for file in fs::read_dir(identity.unwrap().path()).unwrap() {
                let path = file.unwrap().path();
                let value: Value =
                    serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
                if value["mutation_id"] == mutation && value["program_id"] == program {
                    found.push((path, value));
                }
            }
        }
    }
    assert_eq!(found.len(), 1, "{mutation} on {program}: {found:?}");
    found.remove(0)
}

/// Rewrites an ends record as one of another run (`undefined_steps` negated) that every check
/// of the store admits: its digest recomputed.
fn forge_ends(path: &Path, value: &Value) {
    let texts = |key: &str| {
        value[key]
            .as_array()
            .unwrap()
            .iter()
            .map(|text| text.as_str().unwrap().to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(value["across"], json!({"baseline": null, "mutant": null}));
    let forged = kink_flow::mutant_ends::MutantEnds {
        program_id: value["program_id"].as_str().unwrap().to_owned(),
        ends: texts("ends"),
        stop_ends: value["stop_ends"]
            .as_array()
            .unwrap()
            .iter()
            .map(|index| usize::try_from(index.as_u64().unwrap()).unwrap())
            .collect(),
        one_sided_ends: texts("one_sided_ends"),
        undefined_steps: !value["undefined_steps"].as_bool().unwrap(),
        complete: value["complete"].as_bool().unwrap(),
        across: kink_flow::mutant_ends::Across::default(),
        polls: kink_flow::outcomes::RunPolls {
            count: value["polls"]["count"].as_u64().unwrap(),
            bound: value["polls"]["bound"].as_u64().unwrap(),
            cut: value["polls"]["cut"].as_bool().unwrap(),
        },
    };
    let mut value = value.clone();
    value["undefined_steps"] = json!(forged.undefined_steps);
    value["record_sha256"] = json!(
        forged
            .digest(
                value["context_sha256"].as_str().unwrap(),
                value["mutation_identity"].as_str().unwrap(),
                value["program_digest"].as_str().unwrap(),
            )
            .to_string()
    );
    fs::write(path, serde_json::to_string_pretty(&value).unwrap()).unwrap();
}

/// `run --verify` of the flow `manifest`.
fn verify(manifest: &Path) -> Value {
    let (document, _) = kink_flow::search::run_with(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &RunOptions::default(),
        kink_flow::search::RunMode::Verify,
    );
    document
}

/// `run --verify` re-derives each mutant ends record a run of a flow that declares
/// `[[projection]]` would read: a record that no longer describes the live run is a mismatch,
/// as an outcome record's is. A flow that declares none reads no ends record, so its `--verify`
/// does not look at them.
#[test]
fn verify_re_derives_the_ends_records_a_projection_reads() {
    let text = with_other(
        "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
         [[projection]]\nname = \"whole\"\ndomain = [\"other\"]\n\n",
    );
    let dir = fixture("verify-ends", &[("verified", &text)]);
    let manifest = dir.join("FLOW-verified.toml");
    search(&manifest);
    let verified = verify(&manifest);
    assert_eq!(verified["mismatches"], json!([]), "{verified:#}");
    let (path, record) = ends_record(&dir, "note-offset", "other");
    forge_ends(&path, &record);
    let forged = verify(&manifest);
    let mismatch = &forged["mismatches"][0];
    assert_eq!(
        (&mismatch["mutation"], &mismatch["program"]),
        (&json!("note-offset"), &json!("other")),
        "{forged:#}"
    );
    assert!(
        mismatch["cached"]["ends_sha256"].is_string(),
        "{mismatch:#}"
    );
    assert!(mismatch["live"]["ends_sha256"].is_string(), "{mismatch:#}");
    assert_ne!(mismatch["cached"], mismatch["live"], "{mismatch:#}");
    assert_eq!(forged["mutations"][0]["status"], "error", "{forged:#}");
    assert_eq!(
        forged["mutations"][0]["reason"], "outcome-mismatch:other",
        "{forged:#}"
    );
    // A flow without projections: the same forgery is not looked at.
    let dir = fixture("verify-ends-plain", &[]);
    let manifest = dir.join("FLOW-plain.toml");
    search(&manifest);
    let (path, record) = ends_record(&dir, "note-offset", "both");
    forge_ends(&path, &record);
    let plain = verify(&manifest);
    assert_eq!(plain["mismatches"], json!([]), "{plain:#}");
    assert_eq!(statuses(&plain), statuses(&search(&manifest)));
}

/// `run` of `manifest` on `list` (a mutation list's text, written beside it) with the lock
/// `kink.lock` beside it.
fn locked_search(manifest: &Path, list: &str, locked: bool) -> Value {
    let list_path = manifest.with_file_name("EXPECT.toml");
    fs::write(&list_path, list).unwrap();
    let (document, _) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&list_path).unwrap(),
        &RunOptions {
            lock: Some(manifest.with_file_name("kink.lock")),
            locked,
            ..RunOptions::default()
        },
    );
    document
}

/// The fixture's mutation list with `expect` stated per mutation (`note-offset`'s, then
/// `emit-offset`'s, each a TOML value or nothing).
fn expecting(note: &str, emit: &str) -> String {
    let list = fs::read_to_string(flow().join("MUTATIONS.toml")).unwrap();
    let with = |list: String, id: &str, expect: &str| {
        if expect.is_empty() {
            return list;
        }
        list.replace(
            &format!("id = \"{id}\"\n"),
            &format!("id = \"{id}\"\nexpect = {expect}\n"),
        )
    };
    with(with(list, "note-offset", note), "emit-offset", emit)
}

/// PJ-11 (U11e): `run` judges no snapshot projection (`compare`'s alone), so a flow whose every
/// projection is a snapshot lists none: its rows carry `projections = []`, and the entries a lock
/// recorded under an earlier projection are dropped, after which `--locked` is unchanged.
/// U11f: a snapshot projection keeps no cell of the result record, so such a flow's search
/// compares no cell of the end, as a flow of trace projections does, and an `expect` naming a
/// snapshot projection refuses the list, since `run` never judges under one.
#[test]
fn a_flow_of_snapshot_projections_judges_its_mutations_under_none() {
    let flow = |projections: &str| {
        format!(
            "{}\n[[program]]\nid = \"n2\"\ntext = \"note(5)\"\n",
            plain_projected(projections)
        )
    };
    let dir = fixture(
        "snapshot-only",
        &[(
            "projected",
            &flow("[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n"),
        )],
    );
    let manifest = dir.join("FLOW-projected.toml");
    let list = expecting("", "");
    let first = locked_search(&manifest, &list, false);
    assert_eq!(first["lock"]["status"], "created", "{:#}", first["lock"]);
    let lock = dir.join("kink.lock");
    assert!(
        fs::read_to_string(&lock)
            .unwrap()
            .contains("{ name = \"out\""),
        "{first:#}"
    );
    fs::write(
        &manifest,
        flow("[[projection]]\nname = \"snap\"\nrelation = \"snapshot\"\n\n"),
    )
    .unwrap();
    let admission = admit(&FlowManifest::read(&manifest).unwrap());
    let spec = admission
        .spec
        .as_ref()
        .unwrap_or_else(|| panic!("{:?}", admission.record.refusal));
    assert_eq!(
        spec.result.value(),
        result("cells", &[], &["k", "out", "scratch"], &[])
    );
    let snapshots = locked_search(&manifest, &list, false);
    for row in snapshots["mutations"].as_array().unwrap() {
        assert_eq!(row["projections"], json!([]), "{row:#}");
    }
    assert_eq!(
        statuses(&first),
        pairs(&[("note-offset", "survived"), ("emit-offset", "killed")]),
        "{first:#}"
    );
    // No cell of the end is compared: `emit-offset`, which `out` kills, survives the search.
    assert_eq!(
        statuses(&snapshots),
        pairs(&[("note-offset", "survived"), ("emit-offset", "survived")]),
        "{snapshots:#}"
    );
    let text = fs::read_to_string(&lock).unwrap();
    assert!(!text.contains("name = \"out\""), "{text}");
    assert!(!text.contains("snap"), "{text}");
    let locked = locked_search(&manifest, &list, true);
    assert_eq!(
        locked["lock"]["status"], "unchanged",
        "{:#}",
        locked["lock"]
    );
    fs::write(
        dir.join("MUTATIONS.toml"),
        expecting("{ snap = \"kill\" }", ""),
    )
    .unwrap();
    let (refused, status) = dispatched(&manifest, "run");
    assert_eq!(status, EXIT_UNASKED, "{refused:#}");
    assert_eq!(
        refused["mutation_list"]["outcome"], "refused",
        "{refused:#}"
    );
    let detail = refused["mutation_list"]["detail"].as_str().unwrap();
    assert!(
        detail.contains("mutation \"note-offset\".expect.snap")
            && detail.contains("`snap` is a snapshot projection"),
        "{detail}"
    );
}

/// PJ-11 (U11d): the lock records each mutation's status and killer under each listed
/// projection and counts the killed and the survivors under each; the document's
/// `projection_counts` counts them too. A run reads each recorded killer back and keeps it while
/// it kills under its projection (decision U2): `n2` (`note(5)`) kills `note-offset` under
/// `scratch` after `both`, so a lock naming it keeps it; one naming `e3` (`emit(3)`, which does
/// not touch `<scratch>`) gives the first killing program in the search order back. The row's
/// own killer is the row's record's.
#[test]
fn the_lock_records_a_killer_per_projection_and_counts_the_survivors() {
    let text = format!(
        "{}\n[[program]]\nid = \"n2\"\ntext = \"note(5)\"\n\n[[program]]\nid = \"e3\"\ntext = \"emit(3)\"\n",
        plain_projected(
            "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
             [[projection]]\nname = \"scratch\"\ncompare = [\"scratch\"]\n\n",
        )
    );
    let dir = fixture("lock-projections", &[("projected", &text)]);
    let manifest = dir.join("FLOW-projected.toml");
    let list = expecting("", "");
    let first = locked_search(&manifest, &list, false);
    assert_eq!(first["lock"]["status"], "created", "{:#}", first["lock"]);
    assert_eq!(
        first["projection_counts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| (
                entry["name"].clone(),
                entry["counts"]["killed"].clone(),
                entry["counts"]["survived"].clone(),
                entry["survivors"].clone()
            ))
            .collect::<Vec<_>>(),
        vec![
            (json!("out"), json!(1), json!(1), json!(["note-offset"])),
            (json!("scratch"), json!(1), json!(1), json!(["emit-offset"])),
        ],
        "{first:#}"
    );
    let lock = dir.join("kink.lock");
    let text = fs::read_to_string(&lock).unwrap();
    assert!(
        text.contains(
            "id = \"note-offset\"\nstatus = \"killed\"\nkiller = \"both\"\nprojections = [\n  \
             { name = \"out\", status = \"survived\" },\n  \
             { name = \"scratch\", status = \"killed\", killer = \"both\" },\n]\n"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "[[run.projection]]\nname = \"out\"\nkilled = 1\nsurvivors = 1\n\n\
             [[run.projection]]\nname = \"scratch\"\nkilled = 1\nsurvivors = 1\n"
        ),
        "{text}"
    );
    let locked = locked_search(&manifest, &list, true);
    assert_eq!(
        locked["lock"]["status"], "unchanged",
        "{:#}",
        locked["lock"]
    );
    let scratch_killer = |document: &Value| {
        document["mutations"][0]["projections"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["name"] == "scratch")
            .unwrap()["killer"]
            .clone()
    };
    let named = |killer: &str| {
        text.replace(
            "{ name = \"scratch\", status = \"killed\", killer = \"both\" }",
            &format!("{{ name = \"scratch\", status = \"killed\", killer = \"{killer}\" }}"),
        )
    };
    // A recorded killer that still kills under its projection is kept.
    fs::write(&lock, named("n2")).unwrap();
    let kept = locked_search(&manifest, &list, true);
    assert_eq!(scratch_killer(&kept), "n2", "{kept:#}");
    assert_eq!(kept["mutations"][0]["killer"], "both", "{kept:#}");
    assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
    // One that no longer does gives the first killing program in C back, a lock change.
    fs::write(&lock, named("e3")).unwrap();
    let moved = locked_search(&manifest, &list, true);
    assert_eq!(scratch_killer(&moved), "both", "{moved:#}");
    assert_eq!(moved["lock"]["status"], "stale", "{:#}", moved["lock"]);
    assert_eq!(
        kink_flow::lock::stale_lines(&moved)
            .iter()
            .map(|line| line.rsplit(": ").take(2).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        vec![vec!["killer e3 -> both", "under scratch"]],
        "{:#}",
        moved["lock"]
    );
}

/// PJ-11 (U11d): `expect` per projection is checked against the row's entry under each named
/// projection, as `expect` against the row's status: `note-offset` changes `<scratch>` only, so
/// it survives under `out` and is killed under `scratch` (met), while `emit-offset` claimed to
/// survive under `out` is killed there (unmet, naming the projection); the string form keeps
/// checking the row's own status. A name the flow does not declare refuses the list.
#[test]
fn an_expectation_per_projection_is_checked_under_each() {
    let text = plain_projected(
        "[[projection]]\nname = \"out\"\ncompare = [\"out\"]\n\n\
         [[projection]]\nname = \"scratch\"\ncompare = [\"scratch\"]\n\n",
    );
    let dir = fixture("expect-projections", &[("projected", &text)]);
    let manifest = dir.join("FLOW-projected.toml");
    let document = locked_search(
        &manifest,
        &expecting(
            "{ out = \"survive\", scratch = \"kill\" }",
            "{ out = \"survive\" }",
        ),
        false,
    );
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(
        rows[0]["expect"],
        json!({"out": "survive", "scratch": "kill"})
    );
    assert_eq!(
        rows[0]["expectation"],
        json!({"verdict": "met", "detail": null, "projections": [
            {"name": "out", "verdict": "met", "detail": null},
            {"name": "scratch", "verdict": "met", "detail": null},
        ]}),
        "{:#}",
        rows[0]
    );
    assert_eq!(rows[1]["expectation"]["verdict"], "unmet", "{:#}", rows[1]);
    assert_eq!(
        rows[1]["expectation"]["detail"], "under out: expected to survive, killed by both",
        "{:#}",
        rows[1]
    );
    assert_eq!(
        document["expectations"]["unmet"],
        json!(["emit-offset"]),
        "{document:#}"
    );
    assert_eq!(
        kink_flow::cli::run_status(&document),
        kink_flow::cli::EXIT_NO,
        "{document:#}"
    );
    // The string form is the row's own status, which a kill under the union decides.
    let row = locked_search(&manifest, &expecting("\"survive\"", ""), false);
    assert_eq!(row["mutations"][0]["expectation"]["verdict"], "unmet");
    // A name no projection has: the list is refused before anything runs.
    fs::write(
        dir.join("MUTATIONS.toml"),
        expecting("{ writes = \"survive\" }", ""),
    )
    .unwrap();
    let (refused, status) = dispatched(&manifest, "run");
    assert_eq!(status, EXIT_UNASKED, "{refused:#}");
    assert_eq!(
        refused["mutation_list"]["outcome"], "refused",
        "{refused:#}"
    );
    let detail = refused["mutation_list"]["detail"].as_str().unwrap();
    assert!(
        detail.contains("mutation \"note-offset\".expect.writes")
            && detail.contains("names no projection of the flow (its projections: out, scratch)"),
        "{detail}"
    );
}

/// A flow that declares no projection is judged as it was: no row or executed entry names a
/// projection, and every status and killer is the runner's.
#[test]
fn a_flow_without_projections_names_none_in_its_rows() {
    let dir = fixture("unprojected", &[]);
    let document = search(&dir.join("FLOW-plain.toml"));
    for row in document["mutations"].as_array().unwrap() {
        assert!(row.get("projections").is_none(), "{row:#}");
        for entry in row["executed"].as_array().unwrap() {
            assert!(entry.get("projections").is_none(), "{entry:#}");
        }
    }
    assert!(document.get("projection_counts").is_none(), "{document:#}");
    // Its lock section has no line of the projections', and `expect` per projection names its
    // one projection, `default`, whose status is the row's.
    let list = expecting("{ default = \"kill\" }", "\"kill\"");
    let locked = locked_search(&dir.join("FLOW-plain.toml"), &list, false);
    let text = fs::read_to_string(dir.join("kink.lock")).unwrap();
    assert!(!text.contains("projection"), "{text}");
    let rows = locked["mutations"].as_array().unwrap();
    assert_eq!(rows[0]["expectation"]["verdict"], "met", "{:#}", rows[0]);
    assert_eq!(
        rows[0]["expectation"]["projections"],
        json!([{"name": "default", "verdict": "met", "detail": null}]),
        "{:#}",
        rows[0]
    );
    assert_eq!(
        rows[1]["expectation"],
        json!({"verdict": "met", "detail": null}),
        "{:#}",
        rows[1]
    );
}

/// A view naming a snapshot projection (projections PJ-20) judges the implementation's value
/// against the file accepted for the program beside the flow, and reads no side of the
/// definition: an `accepts` snapshot the whole answer to whether it accepts (`accepted`,
/// `rejected` with its `message`), an `end` snapshot the end as stated, each a JSON document
/// compared as a value (re-ordered and re-spaced is no difference). A program with no file is
/// `pending` (status 3); the lock holds each verdict and the counts per projection, never a
/// snapshot's content or the observed value.
#[test]
fn a_snapshot_view_judges_the_answer_against_the_accepted_file() {
    let answer = |answer: &str| format!("[\"sh\", \"-c\", \"cat > /dev/null; echo '{answer}'\"]");
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"msg\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"end\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"quiet\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
             [[program]]",
        )
        + &format!(
            "\n[[program]]\nid = \"two\"\ntext = \"emit(2)\"\n\n\
             [[implementation]]\nname = \"diag\"\ngiven = \"inputs\"\nprotocol = \
             \"kink-implementation/3\"\ncommand = {}\nviews = [{{ projection = \"msg\", required = \
             true }}]\n\n\
             [[implementation]]\nname = \"ends\"\ngiven = \"inputs\"\ncommand = {}\nviews = [\n  \
             {{ projection = \"end\" }},\n  {{ name = \"all\" }},\n  {{ projection = \"quiet\" }},\n]\n",
            answer(r#"{\"end\": \"rejected\", \"message\": \"bad token\"}"#),
            answer(r#"{\"end\": \"final\", \"cells\": {\"x\": 2, \"y\": [1, 2]}}"#),
        );
    let dir = fixture("snapshot", &[("snapshot", &manifest)]);
    let snapshots = dir.join("snapshots");
    for (file, text) in [
        // Re-ordered and re-spaced: no difference.
        (
            "msg/both.json",
            "{\"message\": \"bad token\",\n\"answer\":\"rejected\"}",
        ),
        (
            "end/both.json",
            "{\"end\":\"final\",\"cells\":{\"y\":[1,2],   \"x\":2}}",
        ),
        (
            "end/two.json",
            "{\"cells\": {\"x\": 1, \"y\": [1, 2]}, \"end\": \"final\"}",
        ),
        (
            "quiet/both.json",
            "{\"answer\": \"rejected\", \"message\": \"an old diagnostic\"}",
        ),
    ] {
        let path = snapshots.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    let read = FlowManifest::read(&dir.join("FLOW-snapshot.toml")).unwrap();
    let lock = dir.join("kink.lock");
    let options = kink_flow::compare::CompareOptions {
        lock: Some(lock.clone()),
        ..Default::default()
    };
    let document = kink_flow::compare::command(&read, &options, Some(&Equal), "compare");
    assert_eq!(document["refusal"], Value::Null, "{document:#}");
    let entry = |implementation: &str, program: &str, view: &str| {
        document["rows"]
            .as_array()
            .unwrap_or_else(|| panic!("{document:#}"))
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .and_then(|row| {
                row["views"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|entry| entry["view"] == view)
                    .cloned()
            })
            .unwrap_or_else(|| panic!("{implementation} {program} {view}: {document:#}"))
    };
    let verdict = |implementation: &str, program: &str, view: &str| {
        let entry = entry(implementation, program, view);
        format!(
            "{}{}",
            entry["verdict"].as_str().unwrap(),
            entry["reason"]
                .as_str()
                .map(|reason| format!(" {reason}"))
                .unwrap_or_default()
        )
    };
    assert_eq!(verdict("diag", "both", "msg"), "equal");
    assert_eq!(verdict("diag", "two", "msg"), "pending");
    assert_eq!(entry("diag", "two", "msg")["status"], 3);
    assert_eq!(
        entry("diag", "two", "msg")["snapshot"],
        "snapshots/msg/two.json"
    );
    assert_eq!(verdict("ends", "both", "end"), "equal");
    assert_eq!(verdict("ends", "two", "end"), "different");
    let difference = &entry("ends", "two", "end")["difference"];
    assert_eq!(difference["format"], "kink-snapshot/1");
    assert_eq!(difference["snapshot"]["cells"]["x"], 1);
    assert_eq!(difference["observed"]["cells"]["x"], 2);
    let lines = difference["lines"].as_array().unwrap();
    assert!(lines.contains(&json!("-    \"x\": 1,")), "{difference:#}");
    assert!(lines.contains(&json!("+    \"x\": 2,")), "{difference:#}");
    assert_eq!(entry("ends", "two", "end")["distance"], Value::Null);
    // `quiet` observes whether the implementation accepts: a `final` answer is `accepted`.
    assert_eq!(verdict("ends", "both", "quiet"), "different");
    assert_eq!(
        entry("ends", "both", "quiet")["difference"]["observed"],
        json!({"answer": "accepted"})
    );
    assert_eq!(verdict("ends", "two", "quiet"), "pending");
    // A view that is no snapshot view is judged against the definition, in its place.
    let names = |program: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["implementation"] == "ends" && row["program"] == program)
            .unwrap()["views"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["view"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(names("two"), ["end", "all", "quiet"]);
    assert_eq!(verdict("ends", "two", "all"), "equal");
    assert_eq!(entry("ends", "two", "all").get("snapshot"), None);
    let summary = &document["summary"];
    assert_eq!(summary["verdicts"]["pending"], 2, "{summary:#}");
    assert_eq!(summary["required"]["pending"], 1, "{summary:#}");
    assert_eq!(
        summary["snapshots"],
        json!([
            {"projection": "msg", "implementation": "diag", "equal": 1, "different": 0, "pending": 1},
            {"projection": "end", "implementation": "ends", "equal": 1, "different": 1, "pending": 0},
            {"projection": "quiet", "implementation": "ends", "equal": 0, "different": 1, "pending": 1},
        ])
    );
    // `pending` is no comparison: the view counts it as neither compared nor agreeing.
    let msg = summary["views"]
        .as_array()
        .unwrap()
        .iter()
        .find(|view| view["view"] == "msg")
        .unwrap();
    assert_eq!((&msg["compared"], &msg["agreeing"]), (&json!(1), &json!(1)));
    // The required `msg` view is pending on `two`: no answer.
    assert_eq!(
        kink_flow::compare::compare_status(&document),
        kink_flow::cli::EXIT_UNANSWERED
    );
    let text = kink_flow::compare::text(&document).unwrap();
    assert!(
        text.contains(
            "ends two end (reported): different from the snapshot snapshots/end/two.json\n"
        ),
        "{text}"
    );
    assert!(text.contains("\n    +    \"x\": 2,\n"), "{text}");
    assert!(
        text.contains("diag msg (snapshot): 1 equal, 0 different, 1 pending\n"),
        "{text}"
    );
    // The lock: verdicts and counts, no snapshot content and no observed value.
    let recorded = fs::read_to_string(&lock).unwrap();
    for content in [
        "bad token",
        "an old diagnostic",
        "kink-snapshot",
        "accepted\\\"",
    ] {
        assert!(!recorded.contains(content), "{content}: {recorded}");
    }
    assert!(
        recorded.contains("view = \"msg\"\nrequired = true\nverdict = \"pending\"\n"),
        "{recorded}"
    );
    assert!(
        recorded.contains("view = \"quiet\"\nrequired = false\nverdict = \"pending\"\n"),
        "{recorded}"
    );
    assert!(
        recorded.contains(
            "[[compare.snapshot]]\nprojection = \"msg\"\nimplementation = \"diag\"\nequal = 1\n\
             different = 0\npending = 1\n"
        ),
        "{recorded}"
    );
    let rows = |header: &str| recorded.lines().filter(|line| *line == header).count();
    assert_eq!(
        (
            rows("[[compare.verdict]]"),
            rows("[[compare.view]]"),
            rows("[[compare.snapshot]]")
        ),
        (8, 4, 3),
        "{recorded}"
    );
    let locked = kink_flow::compare::CompareOptions {
        locked: true,
        ..options
    };
    let again = kink_flow::compare::command(&read, &locked, Some(&Equal), "compare");
    assert_eq!(again["lock"]["status"], "unchanged", "{:#}", again["lock"]);
    // Accepting a value for `two` moves its verdict, a lock difference; another message is
    // `different`, with a line diff of the two renderings.
    fs::write(
        snapshots.join("msg/two.json"),
        "{\"answer\": \"rejected\", \"message\": \"bad token!\"}",
    )
    .unwrap();
    let moved = kink_flow::compare::command(&read, &locked, Some(&Equal), "compare");
    assert_eq!(moved["lock"]["status"], "stale", "{:#}", moved["lock"]);
    let row = moved["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["implementation"] == "diag" && row["program"] == "two")
        .unwrap();
    assert_eq!(row["views"][0]["verdict"], "different");
    assert_eq!(
        row["views"][0]["difference"]["lines"],
        json!([
            " {",
            "   \"answer\": \"rejected\",",
            "-  \"message\": \"bad token!\"",
            "+  \"message\": \"bad token\"",
            " }",
            " "
        ])
    );
}

/// A crash is a value under an `accepts` snapshot view (`crashed` with its exit status), judged
/// as any other, so the view decides the crash's row; `could-not-apply` stays the
/// implementation's own answer (D6), whether or not a snapshot exists.
#[test]
fn a_crash_is_a_snapshot_value_and_could_not_apply_is_its_own_verdict() {
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"crashed\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"ended\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"declined\"\nrelation = \"snapshot\"\n\n[[program]]",
        )
        + "\n[[program]]\nid = \"two\"\ntext = \"emit(2)\"\n\n\
           [[implementation]]\nname = \"boom\"\ngiven = \"inputs\"\nprotocol = \
           \"kink-implementation/3\"\ncommand = [\"sh\", \"-c\", \"cat > /dev/null; exit 1\"]\n\
           views = [{ projection = \"crashed\", required = true }, { projection = \"ended\" }]\n\n\
           [[implementation]]\nname = \"later\"\ngiven = \"inputs\"\ncommand = [\"sh\", \"-c\", \
           \"cat > /dev/null; echo '{\\\"end\\\": \\\"could-not-apply\\\", \\\"reason\\\": \
           \\\"not yet\\\"}'\"]\nviews = [{ projection = \"declined\", required = true }]\n";
    let dir = fixture("snapshot-failures", &[("snapshot", &manifest)]);
    fs::create_dir_all(dir.join("snapshots/crashed")).unwrap();
    fs::write(
        dir.join("snapshots/crashed/both.json"),
        "{\"answer\": \"crashed\", \"exit_code\": 1}",
    )
    .unwrap();
    let read = FlowManifest::read(&dir.join("FLOW-snapshot.toml")).unwrap();
    let document = kink_flow::compare::command(
        &read,
        &kink_flow::compare::CompareOptions::default(),
        Some(&Equal),
        "compare",
    );
    assert_eq!(document["refusal"], Value::Null, "{document:#}");
    let row = |implementation: &str, program: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .unwrap()
            .clone()
    };
    let both = row("boom", "both");
    assert_eq!(both["failure"]["kind"], "exit", "{both:#}");
    // The crash is the accepted value; the end snapshot has no end to judge.
    assert_eq!(both["views"].as_array().unwrap().len(), 1, "{both:#}");
    assert_eq!(both["views"][0]["view"], "crashed");
    assert_eq!(both["views"][0]["verdict"], "equal");
    assert_eq!(both["failure"]["decided"], true, "{both:#}");
    let two = row("boom", "two");
    assert_eq!(two["views"][0]["verdict"], "pending", "{two:#}");
    let later = row("later", "both");
    assert_eq!(later["views"][0]["verdict"], "could-not-apply", "{later:#}");
    assert_eq!(
        later["views"][0]["snapshot"],
        "snapshots/declined/both.json"
    );
    assert_eq!(
        document["summary"]["snapshots"],
        json!([
            {"projection": "crashed", "implementation": "boom", "equal": 1, "different": 0, "pending": 1},
            {"projection": "ended", "implementation": "boom", "equal": 0, "different": 0, "pending": 0},
            {"projection": "declined", "implementation": "later", "equal": 0, "different": 0, "pending": 0},
        ])
    );
    // `could-not-apply` under a required view is 1, a pending required view 3.
    assert_eq!(
        kink_flow::compare::compare_status(&document),
        kink_flow::cli::EXIT_NO
    );
}

/// `accept` (projections PJ-20) writes the value compare judges under a snapshot projection as
/// each case's snapshot, and nothing else beside the flow: a compare before it finds `pending`
/// and `different`, one after it `equal`. A file that holds the value as a JSON value is left as
/// written; `--only` limits the cases; a case answered `could-not-apply` is not accepted (exit 3)
/// and its file is left as it is; a file of no case is reported stale and never removed; a
/// projection that is unknown, not a snapshot, or that no view names, and an unknown case, refuse
/// the command (exit 2). The command line reaches it through `FlowCommand::parse` and `dispatch`.
#[test]
fn accept_writes_the_compared_values_as_snapshots() {
    let answer = |answer: &str| format!("[\"sh\", \"-c\", \"cat > /dev/null; echo '{answer}'\"]");
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"msg\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"end\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"declined\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"orphan\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"cells\"\n\n\
             [[program]]",
        )
        + &format!(
            "\n[[program]]\nid = \"two\"\ntext = \"emit(2)\"\n\n\
             [[implementation]]\nname = \"diag\"\ngiven = \"inputs\"\nprotocol = \
             \"kink-implementation/3\"\ncommand = {}\nviews = [{{ projection = \"msg\", required = \
             true }}]\n\n\
             [[implementation]]\nname = \"ends\"\ngiven = \"inputs\"\ncommand = {}\nviews = [\n  \
             {{ projection = \"end\", required = true }},\n  {{ name = \"all\" }},\n]\n\n\
             [[implementation]]\nname = \"later\"\ngiven = \"inputs\"\ncommand = {}\nviews = \
             [{{ projection = \"declined\" }}]\n",
            answer(r#"{\"end\": \"rejected\", \"message\": \"bad token\"}"#),
            answer(r#"{\"end\": \"final\", \"cells\": {\"x\": 2, \"y\": [1, 2]}}"#),
            answer(r#"{\"end\": \"could-not-apply\", \"reason\": \"not yet\"}"#),
        );
    let dir = fixture("accept", &[("accept", &manifest)]);
    let snapshots = dir.join("snapshots");
    // Re-spaced and re-ordered: it holds the value, and `accept` leaves its text as it is.
    let respaced = "{\"message\": \"bad token\",\n\"answer\":\"rejected\"}";
    for (file, text) in [
        ("msg/both.json", respaced),
        ("msg/gone.json", "{\"answer\": \"accepted\"}\n"),
        (
            "end/both.json",
            "{\"cells\": {\"x\": 1, \"y\": [1, 2]}, \"end\": \"final\"}\n",
        ),
        ("declined/both.json", "{\"end\": \"final\"}\n"),
    ] {
        let path = snapshots.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    let path = dir.join("FLOW-accept.toml");
    let read = FlowManifest::read(&path).unwrap();
    let compare = || {
        let document = kink_flow::compare::command(
            &read,
            &kink_flow::compare::CompareOptions::default(),
            Some(&Equal),
            "compare",
        );
        assert_eq!(document["refusal"], Value::Null, "{document:#}");
        document
    };
    let verdicts = |document: &Value, implementation: &str, view: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["implementation"] == implementation)
            .map(|row| {
                let entry = row["views"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|entry| entry["view"] == view)
                    .unwrap_or_else(|| panic!("{row:#}"));
                format!(
                    "{} {}",
                    row["program"].as_str().unwrap(),
                    entry["verdict"].as_str().unwrap()
                )
            })
            .collect::<Vec<_>>()
    };
    let before = compare();
    assert_eq!(
        verdicts(&before, "diag", "msg"),
        ["both equal", "two pending"]
    );
    assert_eq!(
        verdicts(&before, "ends", "end"),
        ["both different", "two pending"]
    );
    let accept = |projection: &str, only: &[&str]| {
        let mut args = vec!["--projection".to_owned(), projection.to_owned()];
        for case in only {
            args.extend(["--only".to_owned(), (*case).to_owned()]);
        }
        let command = FlowCommand::parse("accept", CommandFiles::default(), &args).unwrap();
        let front = FrontEnd {
            implementations: Some(&Equal),
            ..FrontEnd::default()
        };
        dispatch(FlowManifest::read(&path).unwrap(), command, front).unwrap()
    };
    let outcomes = |document: &Value| {
        document["cases"]
            .as_array()
            .unwrap()
            .iter()
            .map(|case| {
                format!(
                    "{} {}",
                    case["case"].as_str().unwrap(),
                    case["outcome"].as_str().unwrap()
                )
            })
            .collect::<Vec<_>>()
    };

    let (msg, status) = accept("msg", &[]);
    assert_eq!(status, EXIT_YES, "{msg:#}");
    assert_eq!(msg["schema"], "kink-flow-accept");
    assert_eq!(msg["implementation"], "diag");
    assert_eq!(outcomes(&msg), ["both unchanged", "two created"], "{msg:#}");
    assert_eq!(msg["cases"][1]["verdict"], "pending");
    assert_eq!(msg["changed"], json!(["snapshots/msg/two.json"]));
    assert_eq!(msg["stale"], json!(["snapshots/msg/gone.json"]));
    assert_eq!(
        fs::read_to_string(snapshots.join("msg/two.json")).unwrap(),
        "{\n  \"answer\": \"rejected\",\n  \"message\": \"bad token\"\n}\n"
    );
    assert_eq!(
        fs::read_to_string(snapshots.join("msg/both.json")).unwrap(),
        respaced
    );
    assert!(
        snapshots.join("msg/gone.json").is_file(),
        "a stale file is kept"
    );

    // `--only` accepts the cases it names: `end/two.json` stays absent.
    let (only, status) = accept("end", &["both"]);
    assert_eq!(status, EXIT_YES, "{only:#}");
    assert_eq!(outcomes(&only), ["both replaced"], "{only:#}");
    assert_eq!(only["cases"][0]["verdict"], "different");
    assert!(!snapshots.join("end/two.json").exists());
    let (end, status) = accept("end", &[]);
    assert_eq!(status, EXIT_YES, "{end:#}");
    assert_eq!(outcomes(&end), ["both unchanged", "two created"], "{end:#}");
    let text = kink_flow::cli::text(&end).unwrap();
    assert_eq!(
        text,
        "created snapshots/end/two.json\n\
         accept end (ends): 1 created, 0 replaced, 1 unchanged, 0 not accepted, 0 stale\n"
    );

    let after = compare();
    assert_eq!(verdicts(&after, "diag", "msg"), ["both equal", "two equal"]);
    assert_eq!(verdicts(&after, "ends", "end"), ["both equal", "two equal"]);
    // The view judged against the definition is as it was.
    assert_eq!(
        verdicts(&after, "ends", "all"),
        verdicts(&before, "ends", "all")
    );

    // `could-not-apply` states no value: nothing is written, the accepted file stays.
    let (declined, status) = accept("declined", &[]);
    assert_eq!(status, kink_flow::cli::EXIT_UNANSWERED, "{declined:#}");
    assert_eq!(
        outcomes(&declined),
        ["both not-accepted", "two not-accepted"],
        "{declined:#}"
    );
    assert_eq!(declined["cases"][0]["verdict"], "could-not-apply");
    assert_eq!(declined["cases"][0]["detail"], "not yet");
    assert_eq!(declined["changed"], json!([]));
    assert_eq!(
        fs::read_to_string(snapshots.join("declined/both.json")).unwrap(),
        "{\"end\": \"final\"}\n"
    );
    assert!(!snapshots.join("declined/two.json").exists());
    let text = kink_flow::cli::text(&declined).unwrap();
    assert!(
        text.starts_with("not accepted both (could-not-apply): not yet\n"),
        "{text}"
    );

    for (projection, only, reason) in [
        ("nope", &[][..], "unknown-projection"),
        ("cells", &[][..], "not-a-snapshot"),
        ("orphan", &[][..], "no-producer"),
        ("msg", &["three"][..], "unknown-case"),
    ] {
        let (refused, status) = accept(projection, only);
        assert_eq!(status, EXIT_UNASKED, "{refused:#}");
        assert_eq!(refused["refusal"]["reason"], reason, "{refused:#}");
        assert_eq!(refused["cases"], json!([]));
    }
    // Nothing but snapshots was written beside the flow: no lock.
    assert!(!dir.join("kink.lock").exists());
    let mut written = Vec::new();
    let mut pending = vec![snapshots.clone()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                written.push(path.strip_prefix(&snapshots).unwrap().display().to_string());
            }
        }
    }
    written.sort();
    assert_eq!(
        written,
        [
            "declined/both.json",
            "end/both.json",
            "end/two.json",
            "msg/both.json",
            "msg/gone.json",
            "msg/two.json"
        ]
    );
}

/// A view naming a `metric` projection (projections PJ-21) measures a metric the answer states
/// (`metrics`, `kink-implementation/3`) and reads no side of the definition: a deterministic
/// metric against the baseline accepted for the program, in the projection's direction, a
/// regression beyond `max_regression` a finding of a required view; a host-dependent metric is
/// reported only, its answers never cached and its views in no lock row. The lock holds each
/// deterministic metric view's verdict and the counts per projection, never a measured value or
/// a baseline, so a count that moves within its verdict moves no row; `accept` writes the
/// baselines compare measured.
#[test]
fn a_metric_view_measures_the_answer_against_its_baseline() {
    let meter = "req=$(cat)\nwall=$(date +%s%N)\ncase \"$req\" in\n  \
                 *'\"program\":\"both\"'*) m=\"\\\"bytes\\\": $(cat both-bytes), \\\"steps\\\": 7\" ;;\n  \
                 *'\"program\":\"two\"'*) m='\"bytes\": 120' ;;\n  \
                 *'\"program\":\"three\"'*) m='\"bytes\": 90, \"steps\": 3' ;;\n  \
                 *) m='\"bytes\": 50' ;;\nesac\n\
                 echo \"{\\\"end\\\": \\\"final\\\", \\\"metrics\\\": {$m, \\\"wall_ns\\\": $wall}}\"\n";
    let plain = "cat > /dev/null\necho '{\"end\": \"final\", \"metrics\": {\"work\": 3}}'\n";
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"alloc\"\nkind = \"metric\"\nmetric = \"bytes\"\ndirection = \
             \"lower\"\nmax_regression = { absolute = 10 }\n\n\
             [[projection]]\nname = \"steps\"\nkind = \"metric\"\nmetric = \"steps\"\ndirection = \
             \"higher\"\n\n\
             [[projection]]\nname = \"wall\"\nkind = \"metric\"\nmetric = \"wall_ns\"\ndirection = \
             \"lower\"\nhost_dependent = true\ndomain = [\"both\", \"two\", \"three\"]\n\n\
             [[projection]]\nname = \"work\"\nkind = \"metric\"\nmetric = \"work\"\ndirection = \
             \"lower\"\n\n[[program]]",
        )
        + "\n[[program]]\nid = \"two\"\ntext = \"emit(2)\"\n\n\
           [[program]]\nid = \"three\"\ntext = \"emit(3)\"\n\n\
           [[program]]\nid = \"four\"\ntext = \"emit(4)\"\n\n\
           [[implementation]]\nname = \"meter\"\ngiven = \"inputs\"\nprotocol = \
           \"kink-implementation/3\"\ncommand = [\"sh\", \"meter.sh\"]\nidentity = { file = \
           \"meter.sh\" }\nviews = [\n  { projection = \"alloc\", required = true },\n  \
           { projection = \"steps\" },\n  { projection = \"wall\" },\n]\n\n\
           [[implementation]]\nname = \"plain\"\ngiven = \"inputs\"\nprotocol = \
           \"kink-implementation/3\"\ncommand = [\"sh\", \"plain.sh\"]\nidentity = { file = \
           \"plain.sh\" }\nviews = [{ projection = \"work\" }]\n";
    let dir = fixture("metric", &[("metric", &manifest)]);
    fs::write(dir.join("meter.sh"), meter).unwrap();
    fs::write(dir.join("plain.sh"), plain).unwrap();
    // The count `meter` states for `both`, read at each run, so a test moves it with no new
    // identity.
    fs::write(dir.join("both-bytes"), "105").unwrap();
    let snapshots = dir.join("snapshots");
    for (file, text) in [
        ("alloc/both.json", "{\"metric\": \"bytes\", \"value\": 100}"),
        ("alloc/two.json", "{\"value\": 100, \"metric\": \"bytes\"}"),
        (
            "alloc/three.json",
            "{\"metric\": \"bytes\", \"value\": 100}",
        ),
        ("alloc/four.json", "{\"metric\": \"bytes\", \"value\": 50}"),
        ("steps/both.json", "{\"metric\": \"steps\", \"value\": 5}"),
    ] {
        let path = snapshots.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    let path = dir.join("FLOW-metric.toml");
    let read = FlowManifest::read(&path).unwrap();
    let lock = dir.join("kink.lock");
    let cache = dir.join("cache");
    let compare = |locked: bool| {
        let options = kink_flow::compare::CompareOptions {
            lock: Some(lock.clone()),
            locked,
            cache: Some(cache.clone()),
            ..Default::default()
        };
        let document = kink_flow::compare::command(&read, &options, Some(&Equal), "compare");
        assert_eq!(document["refusal"], Value::Null, "{document:#}");
        document
    };
    let entry = |document: &Value, implementation: &str, program: &str, view: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["implementation"] == implementation && row["program"] == program)
            .and_then(|row| {
                row["views"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|entry| entry["view"] == view)
                    .cloned()
            })
            .unwrap_or_else(|| panic!("{implementation} {program} {view}: {document:#}"))
    };
    let verdicts = |document: &Value, implementation: &str, view: &str| {
        ["both", "two", "three", "four"]
            .iter()
            .map(|program| {
                let entry = entry(document, implementation, program, view);
                format!(
                    "{program} {}{}",
                    entry["verdict"].as_str().unwrap(),
                    entry["reason"]
                        .as_str()
                        .map(|reason| format!(" {reason}"))
                        .unwrap_or_default()
                )
            })
            .collect::<Vec<_>>()
    };

    let first = compare(false);
    assert_eq!(first["version"], 11);
    assert_eq!(
        verdicts(&first, "meter", "alloc"),
        [
            "both regressed",
            "two regressed",
            "three improved",
            "four stayed"
        ]
    );
    assert_eq!(
        entry(&first, "meter", "both", "alloc")["metric"],
        json!({"name": "bytes", "direction": "lower", "value": 105, "baseline": 100, "change": 5,
               "exceeded": false})
    );
    assert_eq!(entry(&first, "meter", "both", "alloc")["status"], 0);
    // Beyond `max_regression`: a finding, which the required view makes compare's status.
    assert_eq!(
        entry(&first, "meter", "two", "alloc")["metric"]["exceeded"],
        true
    );
    assert_eq!(entry(&first, "meter", "two", "alloc")["status"], 1);
    assert_eq!(
        entry(&first, "meter", "three", "alloc")["metric"]["change"],
        -10
    );
    assert_eq!(
        entry(&first, "meter", "both", "alloc")["snapshot"],
        "snapshots/alloc/both.json"
    );
    assert_eq!(kink_flow::compare::compare_status(&first), 1);
    // Ungated: higher is better, no baseline is pending, an unstated metric is not compared.
    assert_eq!(
        verdicts(&first, "meter", "steps"),
        [
            "both improved",
            "two not-compared metric-unstated",
            "three pending",
            "four not-compared metric-unstated"
        ]
    );
    assert_eq!(
        entry(&first, "meter", "both", "steps")["metric"]["exceeded"],
        Value::Null
    );
    assert_eq!(
        entry(&first, "meter", "three", "steps")["metric"]["value"],
        3
    );
    // Host-dependent: measured, reported, with no baseline; outside its domain on `four`.
    assert_eq!(
        verdicts(&first, "meter", "wall"),
        [
            "both measured",
            "two measured",
            "three measured",
            "four not-compared outside-domain"
        ]
    );
    let wall = entry(&first, "meter", "both", "wall");
    assert_eq!(wall["metric"]["host_dependent"], true);
    assert!(wall["metric"]["value"].is_u64(), "{wall:#}");
    assert!(wall.get("snapshot").is_none(), "{wall:#}");
    let row = first["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["implementation"] == "meter" && row["program"] == "both")
        .unwrap();
    assert_eq!(row["answer"]["metrics"]["bytes"], 105, "{row:#}");
    // The summary: per metric view, its counts; no metric view is in `views`.
    let metrics = first["summary"]["metrics"].as_array().unwrap();
    assert_eq!(
        metrics[0],
        json!({"projection": "alloc", "implementation": "meter", "metric": "bytes",
               "direction": "lower", "host_dependent": false, "measured": 4, "total": 365,
               "improved": 1, "regressed": 2, "stayed": 1, "pending": 0, "exceeded": 1})
    );
    assert_eq!(metrics[1]["measured"], 2);
    assert_eq!(metrics[1]["pending"], 1);
    assert_eq!(metrics[2]["host_dependent"], true);
    assert_eq!(metrics[2]["measured"], 3);
    assert_eq!(first["summary"]["views"], json!([]));
    assert_eq!(first["summary"]["required"]["regressed"], 2);
    let text = kink_flow::compare::text(&first).unwrap();
    assert!(
        text.contains(
            "meter two alloc (required): regressed: 120 (baseline 100, change +20, beyond \
             max_regression)\n"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "meter alloc (metric `bytes`, lower is better): total 365 over 4 programs measured; \
             1 improved, 2 regressed (1 beyond max_regression), 1 stayed, 0 pending\n"
        ),
        "{text}"
    );
    assert!(
        text.contains("meter wall (metric `wall_ns`, host-dependent): total "),
        "{text}"
    );
    // The lock: each deterministic metric view's verdict, the counts per projection; no value,
    // no total, no baseline, no change and no host-dependent row.
    let section = fs::read_to_string(&lock).unwrap();
    assert!(
        section.contains(
            "view = \"alloc\"\nrequired = true\nverdict = \"regressed\"\nrequest_sha256 = "
        ),
        "{section}"
    );
    assert!(
        section.contains(
            "[[compare.metric]]\nprojection = \"alloc\"\nimplementation = \"meter\"\nmetric = \
             \"bytes\"\nmeasured = 4\nimproved = 1\nregressed = 2\nstayed = 1\npending = 0\n"
        ),
        "{section}"
    );
    for absent in [
        "value =",
        "total =",
        "view = \"wall\"",
        "projection = \"wall\"",
        "baseline =",
        "wall_ns",
        "[[compare.view]]",
        "[[compare.snapshot]]",
    ] {
        assert!(!section.contains(absent), "{absent}: {section}");
    }
    // The cache: the deterministic answers are cached, the host-dependent ones never are, on
    // the program outside the host-dependent view's domain too.
    let second = compare(false);
    let cached = |document: &Value, implementation: &str| {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["implementation"] == implementation)
            .map(|row| row["cached"] == true)
            .collect::<Vec<_>>()
    };
    assert_eq!(cached(&second, "plain"), [true; 4]);
    assert_eq!(cached(&second, "meter"), [false; 4]);
    let mut answers = Vec::new();
    let mut pending = vec![cache.join("implementation-answers")];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                answers.push(fs::read_to_string(path).unwrap());
            }
        }
    }
    assert_eq!(answers.len(), 4, "{answers:?}");
    assert!(
        answers.iter().all(|answer| !answer.contains("wall_ns")),
        "{answers:?}"
    );
    // The host-dependent values of the second run are another run's: the section is the bytes
    // it was, and `--locked` confirms it.
    assert_eq!(fs::read_to_string(&lock).unwrap(), section);
    let locked = compare(true);
    assert_eq!(
        locked["lock"]["status"], "unchanged",
        "{:#}",
        locked["lock"]
    );
    // A count that moves within its verdict moves no row: `both` stays regressed within the gate.
    fs::write(dir.join("both-bytes"), "106").unwrap();
    let moved = compare(true);
    assert_eq!(
        entry(&moved, "meter", "both", "alloc")["metric"]["value"],
        106
    );
    assert_eq!(moved["lock"]["status"], "unchanged", "{:#}", moved["lock"]);

    // `accept` writes the baselines compare measured; a host-dependent metric has none.
    let accept = |projection: &str| {
        let args = vec!["--projection".to_owned(), projection.to_owned()];
        let command = FlowCommand::parse("accept", CommandFiles::default(), &args).unwrap();
        let front = FrontEnd {
            implementations: Some(&Equal),
            ..FrontEnd::default()
        };
        dispatch(FlowManifest::read(&path).unwrap(), command, front).unwrap()
    };
    let (alloc, status) = accept("alloc");
    assert_eq!(status, EXIT_YES, "{alloc:#}");
    assert_eq!(alloc["summary"]["replaced"], 3, "{alloc:#}");
    assert_eq!(alloc["summary"]["unchanged"], 1, "{alloc:#}");
    assert_eq!(
        fs::read_to_string(snapshots.join("alloc/two.json")).unwrap(),
        "{\n  \"metric\": \"bytes\",\n  \"value\": 120\n}\n"
    );
    let (steps, status) = accept("steps");
    assert_eq!(status, kink_flow::cli::EXIT_UNANSWERED, "{steps:#}");
    assert_eq!(steps["cases"][1]["reason"], "metric-unstated", "{steps:#}");
    let (wall, status) = accept("wall");
    assert_eq!(status, EXIT_UNASKED, "{wall:#}");
    assert_eq!(wall["refusal"]["reason"], "host-dependent", "{wall:#}");
    assert!(!snapshots.join("wall").exists());
    let after = compare(false);
    assert_eq!(
        verdicts(&after, "meter", "alloc"),
        ["both stayed", "two stayed", "three stayed", "four stayed"]
    );
    assert_eq!(kink_flow::compare::compare_status(&after), EXIT_YES);
}

/// A metric is stated in `metrics`, which only `kink-implementation/3` has: a view measuring one
/// under another protocol is refused before any run.
#[test]
fn a_metric_view_needs_the_third_protocol() {
    let manifest = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .replace(
            "[[program]]",
            "[[projection]]\nname = \"alloc\"\nkind = \"metric\"\nmetric = \"bytes\"\ndirection = \
             \"lower\"\n\n[[program]]",
        )
        + "\n[[implementation]]\nname = \"old\"\ngiven = \"inputs\"\nprotocol = \
           \"kink-implementation/2\"\ncommand = [\"true\"]\nviews = [{ projection = \"alloc\" }]\n";
    let dir = fixture("metric-protocol", &[("metric", &manifest)]);
    let read = FlowManifest::read(&dir.join("FLOW-metric.toml")).unwrap();
    let document = kink_flow::compare::command(
        &read,
        &kink_flow::compare::CompareOptions::default(),
        Some(&Equal),
        "compare",
    );
    assert_eq!(document["refusal"]["reason"], "declaration", "{document:#}");
    let detail = document["refusal"]["detail"].as_str().unwrap();
    assert!(
        detail.contains("views[0]: the view `alloc` measures a metric")
            && detail.contains("declare `protocol = \"kink-implementation/3\"`"),
        "{detail}"
    );
}
