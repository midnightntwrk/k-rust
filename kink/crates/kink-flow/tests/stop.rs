//! `[stop]`: where every program's run ends besides its own end, for a definition that never
//! terminates. The stop decodes strictly; it keys every cached result and outcome it changes and
//! no other; every document names it; a mutant on which its rule labels nothing is not admitted;
//! `check` warns of an edit a stop before its rule hides, and a survivor repeats it, and of a
//! deletion of its rule, which `run` does not admit; a `cases` entry gives its cases a count;
//! `query` and `fuzz` refuse a stopped corpus.
//!
//! The fixture is testdata/flow/clock: `clock.k`, a clock whose `frame` rule fires every fourth
//! step and which never ends on its own; `FLOW.toml` stops before the first `frame`, at
//! `clock(3, 3)`. Its mutations (`mutations/clock.toml`) speed up `tick` (`tick-twice`), change
//! only `frame`'s right-hand side (`frame-jump`), delete `frame` (`frame-deleted`; an edit that
//! only drops its label is refused at resolution, `label-changed`) and halt the clock before its
//! first frame (`halt-early`).

use kink_flow::{
    FlowManifest,
    cli::{CheckOptions, EXIT_UNASKED, EXIT_YES, FuzzJobRequest, FuzzRequest, check, check_with},
    coverage::{CoverageOptions, coverage},
    digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, outcome_context},
    manifest::{Budget, ManifestError},
    mutation::MutationList,
    query::QueryOptions,
    results::result_key,
    search::{RunOptions, run},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

const SPEC: &str = "[spec]\nentry = \"clock.k\"\nmain_module = \"CLOCK\"\n";

fn decode(text: &str) -> Result<FlowManifest, ManifestError> {
    FlowManifest::decode(text, Path::new("corpus"))
}

#[track_caller]
fn assert_error(text: &str, key: &str, message: &str) {
    let error = decode(text).expect_err("the manifest must be refused");
    assert_eq!(error.key, key, "{error}");
    assert!(error.message.contains(message), "{error}");
}

fn flow() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/clock")
}

/// A private copy of the fixture, with each `(name, text)` of `extra` written as
/// `FLOW-<name>.toml` beside it.
fn fixture(test: &str, extra: &[(&str, &str)]) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-stop-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("mutations")).unwrap();
    for name in ["clock.k", "FLOW.toml", "mutations/clock.toml"] {
        fs::copy(flow().join(name), dir.join(name)).unwrap();
    }
    for (name, text) in extra {
        fs::write(dir.join(format!("FLOW-{name}.toml")), text).unwrap();
    }
    dir
}

/// `FLOW.toml` with its `[stop]` table replaced by `stop`.
fn stopped(stop: &str) -> String {
    let manifest = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    manifest.replace("[stop]\nbefore = [\"CLOCK.frame\"]\n", stop)
}

fn search(manifest: &Path) -> Value {
    let (document, _) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("mutations")).unwrap(),
        &RunOptions {
            ..RunOptions::default()
        },
    );
    document
}

/// Each mutation's row by id.
fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

fn status(document: &Value, id: &str) -> (String, Value) {
    let row = row(document, id);
    (
        row["status"].as_str().unwrap().to_owned(),
        row["reason"].clone(),
    )
}

/// The warnings' reasons of the check row of mutation `id`.
fn warnings(document: &Value, id: &str) -> Vec<String> {
    row(document, id)["warnings"]
        .as_array()
        .unwrap()
        .iter()
        .map(|warning| warning["reason"].as_str().unwrap().to_owned())
        .collect()
}

#[test]
fn stop_decodes_rules_a_count_and_program_counts() {
    let manifest = decode(&format!(
        "{SPEC}[stop]\nafter = [\"CLOCK.tick\", \"CLOCK.frame\"]\ncount = 3\n\n\
         [[program]]\nid = \"a\"\ntext = \"clock(0, 0)\"\n\n\
         [[program]]\nid = \"b\"\ntext = \"clock(0, 0)\"\nstop_count = 5\n"
    ))
    .unwrap();
    let stop = manifest.stop.as_ref().unwrap();
    assert!(stop.before.is_empty());
    // Sorted: a stop is a set of rules.
    assert_eq!(stop.after, ["CLOCK.frame", "CLOCK.tick"]);
    assert_eq!(stop.count.get(), 3);
    assert_eq!(manifest.programs[0].stop_count, None);
    assert_eq!(manifest.programs[1].stop_count.map(|c| c.get()), Some(5));
    assert_eq!(
        manifest.stop_value(),
        Some(json!({
            "before": [],
            "after": ["CLOCK.frame", "CLOCK.tick"],
            "count": 3,
            "counts": {"b": 5},
        }))
    );
    assert_eq!(
        manifest.program_stop(&manifest.programs[1]),
        Some(json!({"before": [], "after": ["CLOCK.frame", "CLOCK.tick"], "count": 5}))
    );
    let campaign = manifest.campaign_stop();
    assert_eq!(campaign.of_test("a").map(|(_, n)| n.get()), Some(3));
    assert_eq!(campaign.of_test("b").map(|(_, n)| n.get()), Some(5));
    // Without [stop]: nothing, everywhere.
    let plain = decode(&format!("{SPEC}[[program]]\nid = \"a\"\ntext = \"1\"\n")).unwrap();
    assert_eq!(plain.stop, None);
    assert_eq!(plain.stop_value(), None);
    assert_eq!(plain.program_stop(&plain.programs[0]), None);
    assert!(plain.campaign_stop().is_none());
    // The default count is 1.
    let one = decode(&format!("{SPEC}[stop]\nbefore = [\"CLOCK.frame\"]\n")).unwrap();
    assert_eq!(one.stop.unwrap().count.get(), 1);
}

#[test]
fn stop_decoding_refuses_what_it_cannot_read() {
    let program = "[[program]]\nid = \"a\"\ntext = \"1\"\n";
    for (stop, key, message) in [
        (
            "[stop]\nafter = [\"X.a\"]\nstop_when = { function = \"F\", cells = [\"n\"] }\n",
            "stop.stop_when",
            "names its condition `when`",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = 3\n",
            "stop.when",
            "expected a table",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { cells = [\"n\"] }\n",
            "stop.when.function",
            "missing required key",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"\", cells = [\"n\"] }\n",
            "stop.when.function",
            "must not be empty",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\" }\n",
            "stop.when.cells",
            "missing required key",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\", cells = [] }\n",
            "stop.when.cells",
            "names no cell",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\", cells = \"n\" }\n",
            "stop.when.cells",
            "expected an array",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\", cells = [\"n\", 1] }\n",
            "stop.when.cells[1]",
            "expected a string",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\", cells = [\"n\"], observer = \"\" }\n",
            "stop.when.observer",
            "must not be empty",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\nwhen = { function = \"F\", cells = [\"n\"], view = \"V\" }\n",
            "stop.when.view",
            "unknown key",
        ),
        ("[stop]\n", "stop", "names no rule"),
        ("[stop]\nbefore = []\nafter = []\n", "stop", "names no rule"),
        (
            "[stop]\nafter = \"X.a\"\n",
            "stop.after",
            "expected an array",
        ),
        (
            "[stop]\nafter = [\"\"]\n",
            "stop.after[0]",
            "nonempty string",
        ),
        (
            "[stop]\nbefore = [\"X.a\", 3]\n",
            "stop.before[1]",
            "nonempty string",
        ),
        (
            "[stop]\nafter = [\"X.a\", \"X.a\"]\n",
            "stop.after",
            "names `X.a` twice",
        ),
        (
            "[stop]\nbefore = [\"X.a\"]\nafter = [\"X.a\"]\n",
            "stop",
            "in both before and after",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\ncount = 0\n",
            "stop.count",
            "must be positive",
        ),
        (
            "[stop]\nafter = [\"X.a\"]\ncount = \"2\"\n",
            "stop.count",
            "expected an integer",
        ),
    ] {
        assert_error(&format!("{SPEC}{stop}{program}"), key, message);
    }
    assert_error(
        &format!("stop = 1\n{SPEC}{program}"),
        "stop",
        "expected a table",
    );
    assert_error(
        &format!("{SPEC}[[program]]\nid = \"a\"\ntext = \"1\"\nstop_count = 2\n"),
        "program \"a\".stop_count",
        "declare [stop]",
    );
    assert_error(
        &format!(
            "{SPEC}[stop]\nafter = [\"X.a\"]\n[[program]]\nid = \"a\"\ntext = \"1\"\nstop_count = 0\n"
        ),
        "program \"a\".stop_count",
        "must be positive",
    );
}

/// A front end's stop condition, for the tests that bind one: it is never asked here.
struct Unasked;

impl kink_flow::StopOracle for Unasked {
    fn cells(&self) -> &[Vec<String>] {
        &[]
    }

    fn with_condition(
        &self,
        _: &mut dyn FnMut(&mut dyn k_rust::backend::StopCondition),
    ) -> Result<(), String> {
        Err("not asked in this test".to_owned())
    }
}

/// `[stop] when` decodes as written, the front end's names kept for it to resolve. A decoded
/// manifest states no condition anywhere until a front end binds one: then every document's
/// stop and the program's key name it by its identity (`when`), and the campaign's stop carries
/// it; a stop without a condition keeps the value it had before conditions existed.
#[test]
fn a_stop_condition_decodes_and_is_named_once_bound() {
    let text = format!(
        "{SPEC}[stop]\nbefore = [\"CLOCK.frame\"]\n\
         when = {{ function = \"Breakpoint\", cells = [\"pc\", \"rom\"], observer = \"views:main\" }}\n\n\
         [[program]]\nid = \"a\"\ntext = \"clock(0, 0)\"\n"
    );
    let manifest = decode(&text).unwrap();
    let when = manifest.stop.as_ref().unwrap().when.clone().unwrap();
    assert_eq!(
        when,
        kink_flow::StopWhenSection {
            function: "Breakpoint".into(),
            cells: vec!["pc".into(), "rom".into()],
            observer: Some("views:main".into()),
        }
    );
    let unbound = json!({"before": ["CLOCK.frame"], "after": [], "count": 1});
    assert_eq!(manifest.stop_value(), Some(unbound.clone()));
    assert_eq!(manifest.program_stop(&manifest.programs[0]), Some(unbound));
    assert!(manifest.campaign_stop().when().is_none());
    let identity = json!({"observer": {"definition": "views:main", "definition_ir": "d"}});
    let bound = manifest.with_stop_when(kink_flow::StopWhen::new(
        identity.clone(),
        std::sync::Arc::new(Unasked),
    ));
    assert_eq!(bound.stop_value().unwrap()["when"], identity);
    assert_eq!(
        bound.program_stop(&bound.programs[0]).unwrap()["when"],
        identity
    );
    assert_eq!(bound.campaign_stop().when().unwrap().identity(), &identity);
    // Without `when`, a bound condition is not asked and names nothing.
    let plain = decode(&format!(
        "{SPEC}[stop]\nbefore = [\"CLOCK.frame\"]\n[[program]]\nid = \"a\"\ntext = \"1\"\n"
    ))
    .unwrap()
    .with_stop_when(kink_flow::StopWhen::new(
        identity,
        std::sync::Arc::new(Unasked),
    ));
    assert!(plain.stop.as_ref().unwrap().when.is_none());
    assert_eq!(
        plain.stop_value(),
        Some(json!({"before": ["CLOCK.frame"], "after": [], "count": 1}))
    );
}

/// kink-flow's own front end reads terms of a K definition and has no observer to evaluate a
/// condition in: a corpus with `[stop] when` is refused at stage `stop`, reason
/// `unsupported-front-end`, by `check` and `results` alike, never run without its condition.
#[test]
fn the_k_front_end_refuses_a_stop_condition() {
    let dir = fixture(
        "when",
        &[(
            "when",
            &stopped(
                "[stop]\nbefore = [\"CLOCK.frame\"]\nwhen = { function = \"Third\", cells = [\"k\"] }\n",
            ),
        )],
    );
    let path = dir.join("FLOW-when.toml");
    let (document, status) = check(&path);
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    assert_eq!(
        (&document["spec"]["stage"], &document["spec"]["reason"]),
        (&json!("stop"), &json!("unsupported-front-end")),
        "{document:#}"
    );
    let detail = document["spec"]["detail"].as_str().unwrap();
    assert!(
        detail.contains("`Third`") && detail.contains("krs kink"),
        "{detail}"
    );
    let (document, ok) = coverage(
        &FlowManifest::read(&path).unwrap(),
        &CoverageOptions::default(),
    );
    assert!(!ok, "{document:#}");
    assert_eq!(
        document["spec"]["reason"], "unsupported-front-end",
        "{document:#}"
    );
}

/// A `cases` entry takes `stop_count`, how the corpus observes each of its cases, beside the
/// pattern: every matched case has the count, and without `[stop]` it is refused as a program's.
#[test]
fn a_cases_entry_gives_its_cases_a_count() {
    let dir = fixture("cases", &[]);
    for name in ["a", "b"] {
        fs::create_dir_all(dir.join("cases")).unwrap();
        fs::write(
            dir.join(format!("cases/{name}.toml")),
            "[inputs]
",
        )
        .unwrap();
    }
    let entry = "[[program]]\ncases = \"cases/*.toml\"\nstop_count = 2\n";
    let stop = "[stop]\nbefore = [\"CLOCK.frame\"]\n";
    let manifest = FlowManifest::decode(&format!("{SPEC}{stop}{entry}"), &dir).unwrap();
    let counts = manifest
        .programs
        .iter()
        .map(|program| (program.id.as_str(), program.stop_count.map(|c| c.get())))
        .collect::<Vec<_>>();
    assert_eq!(
        counts,
        [("cases/a.toml", Some(2)), ("cases/b.toml", Some(2))]
    );
    let error = FlowManifest::decode(&format!("{SPEC}{entry}"), &dir).unwrap_err();
    assert_eq!(error.key, "program \"cases/a.toml\".stop_count", "{error}");
    assert!(error.message.contains("declare [stop]"), "{error}");
    let error =
        FlowManifest::decode(&format!("{SPEC}{stop}{entry}stop_count2 = 1\n"), &dir).unwrap_err();
    assert!(
        error.message.contains("no other key but `stop_count`"),
        "{error}"
    );
}

/// A corpus without `[stop]` keys its results and outcomes as before stops existed: the result
/// key and the tier-1 context have exactly their earlier members, and a stop adds only `stop`.
#[test]
fn a_context_without_a_stop_is_the_context_before_stops() {
    let execution = ExecutionDigest {
        kind: EXECUTION_DIGEST_KIND,
        digest: kink_patch::sha256(b"specification"),
    };
    let projection = kink_flow::ResultProjection {
        state: kink_campaign::StateProjection::WholeTerm,
        compared: Some(vec!["k".into()]),
        not_compared: Vec::new(),
        unobservable: Vec::new(),
    };
    let build = kink_patch::sha256(b"kink build");
    let keys = |value: &Value| {
        value
            .as_object()
            .unwrap()
            .keys()
            .cloned()
            .collect::<Vec<_>>()
    };
    let context = outcome_context(
        build,
        execution,
        Budget::default(),
        &projection,
        None,
        None,
        None,
    );
    assert_eq!(
        keys(&context),
        [
            "budget",
            "classifier",
            "execution_digest",
            "kink",
            "kink_build",
            "oracles",
            "outcome_schema",
            "profile",
        ]
    );
    let stop = json!({"before": ["CLOCK.frame"], "after": [], "count": 1});
    let with = outcome_context(
        build,
        execution,
        Budget::default(),
        &projection,
        Some(&stop),
        None,
        None,
    );
    let mut without_stop = with.clone();
    without_stop.as_object_mut().unwrap().remove("stop");
    assert_eq!(without_stop, context);
    assert_eq!(with["stop"], stop);
    let program = kink_patch::sha256(b"program");
    let key = result_key(
        execution,
        program,
        Budget::default(),
        Some(build),
        None,
        None,
        None,
    );
    assert_eq!(
        keys(&key),
        [
            "budget",
            "execution",
            "kink",
            "kink_build",
            "program",
            "schema_version"
        ]
    );
    let stopped = result_key(
        execution,
        program,
        Budget::default(),
        Some(build),
        Some(stop.clone()),
        None,
        None,
    );
    let mut without_stop = stopped.clone();
    without_stop.as_object_mut().unwrap().remove("stop");
    assert_eq!(without_stop, key);
    // Another count is another key and another context.
    let three = json!({"before": ["CLOCK.frame"], "after": [], "count": 3});
    assert_ne!(
        result_key(
            execution,
            program,
            Budget::default(),
            Some(build),
            Some(three.clone()),
            None,
            None
        ),
        stopped
    );
    assert_ne!(
        outcome_context(
            build,
            execution,
            Budget::default(),
            &projection,
            Some(&three),
            None,
            None,
        ),
        with
    );
}

/// The clock's run ends at its stop: the program is comparable, its one end is the state before
/// the first frame, reached at a stop, and every document names the stop.
#[test]
fn a_run_of_the_clock_ends_at_its_stop() {
    let dir = fixture("results", &[]);
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (document, ok) = coverage(&manifest, &CoverageOptions::default());
    assert!(ok, "{document:#}");
    assert_eq!(document["schema"], "kink-flow-coverage");
    assert_eq!(document["version"], 9);
    let stop = json!({"before": ["CLOCK.frame"], "after": [], "count": 1});
    assert_eq!(document["stop"], stop);
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable", "{program:#}");
    assert_eq!(
        program["ends"],
        json!([{
            "head": {"rendering": "k", "text": "clock ( 3 , 3 )", "truncated": false},
            "class": "normal",
            "halt": "stop",
        }]),
        "{program:#}"
    );
    let (check, status) = check(&dir.join("FLOW.toml"));
    assert_eq!(status, EXIT_YES, "{check:#}");
    assert_eq!(check["stop"], stop);
}

/// Each mutation is judged relative to the stop: a faster tick is killed, an edit of only the
/// stopped-before rule's right-hand side survives and says why, a mutant that loses the stop's
/// rule is not admitted, and a mutant that ends on its own before the stop is killed by its end.
#[test]
fn mutations_of_the_clock_are_judged_relative_to_the_stop() {
    let dir = fixture("run", &[]);
    let document = search(&dir.join("FLOW.toml"));
    assert_eq!(document["version"], 35);
    assert_eq!(
        document["stop"],
        json!({"before": ["CLOCK.frame"], "after": [], "count": 1})
    );
    assert_eq!(
        status(&document, "clock/tick-twice").0,
        "killed",
        "{document:#}"
    );
    assert_eq!(
        status(&document, "clock/halt-early").0,
        "killed",
        "{document:#}"
    );
    assert_eq!(
        status(&document, "clock/frame-deleted"),
        ("not-admitted".to_owned(), json!("stop-unresolved")),
        "{document:#}"
    );
    let survivor = row(&document, "clock/frame-jump");
    assert_eq!(survivor["status"], "survived", "{survivor:#}");
    let hidden = survivor["stop_hides_edit"][0].as_str().unwrap();
    assert!(
        hidden.contains("CLOCK.frame") && hidden.contains("\"zero\""),
        "{hidden}"
    );
    assert!(
        row(&document, "clock/tick-twice")
            .get("stop_hides_edit")
            .is_none()
    );
    // `check` warns of the same edit before any mutant runs.
    let (check, _) = check_with(
        &dir.join("FLOW.toml"),
        &CheckOptions {
            mutations: Some(dir.join("mutations")),
            cache: None,
        },
    );
    assert_eq!(check["version"], 13);
    assert!(
        warnings(&check, "clock/frame-jump").contains(&"stop-hides-edit".to_owned()),
        "{check:#}"
    );
    assert!(!warnings(&check, "clock/tick-twice").contains(&"stop-hides-edit".to_owned()));
    // A deletion of the stop's rule hides nothing: the mutant loses the rule, and `check` says
    // that `run` will not admit it.
    let deleted = warnings(&check, "clock/frame-deleted");
    assert!(
        deleted.contains(&"stop-rule-deleted".to_owned()),
        "{check:#}"
    );
    assert!(
        !deleted.contains(&"stop-hides-edit".to_owned()),
        "{check:#}"
    );
}

/// With a count above 1 the run takes the stopped-before rule's earlier steps, so an edit of its
/// right-hand side is killed and no warning is given; a program's own count overrides the
/// corpus's, and the documents name it.
#[test]
fn a_count_above_one_takes_the_stop_rules_earlier_steps() {
    let dir = fixture(
        "count",
        &[(
            "own",
            &stopped("[stop]\nbefore = [\"CLOCK.frame\"]\n").replace(
                "text = \"clock(0, 0)\"",
                "text = \"clock(0, 0)\"\nstop_count = 2",
            ),
        )],
    );
    let manifest = dir.join("FLOW-own.toml");
    let (results_document, _) = coverage(
        &FlowManifest::read(&manifest).unwrap(),
        &CoverageOptions::default(),
    );
    assert_eq!(
        results_document["stop"],
        json!({"before": ["CLOCK.frame"], "after": [], "count": 1, "counts": {"zero": 2}})
    );
    // Through the first frame (clock(3, 3) to clock(4, 0)) to the state before the second.
    assert_eq!(
        results_document["programs"][0]["ends"][0]["head"]["text"], "clock ( 7 , 3 )",
        "{results_document:#}"
    );
    let document = search(&manifest);
    assert_eq!(
        status(&document, "clock/frame-jump").0,
        "killed",
        "{document:#}"
    );
    let (check, _) = check_with(
        &manifest,
        &CheckOptions {
            mutations: Some(dir.join("mutations")),
            cache: None,
        },
    );
    assert!(!warnings(&check, "clock/frame-jump").contains(&"stop-hides-edit".to_owned()));
}

/// A stop that names no rewrite rule of the specification states no observation of it: the
/// specification is refused at stage `stop`, naming the name.
#[test]
fn a_stop_naming_no_rewrite_rule_refuses_the_specification() {
    let dir = fixture(
        "unresolved",
        &[
            ("later", &stopped("[stop]\nafter = [\"CLOCK.later\"]\n")),
            (
                "nothing",
                &stopped("[stop]\nbefore = [\"CLOCK.nothing\"]\n"),
            ),
            ("bare", &stopped("[stop]\nbefore = [\"frame\"]\n")),
        ],
    );
    for (name, named) in [
        ("later", "after `CLOCK.later`"),
        ("nothing", "before `CLOCK.nothing`"),
        ("bare", "before `frame`"),
    ] {
        let (document, status) = check(&dir.join(format!("FLOW-{name}.toml")));
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["spec"]["stage"], "stop", "{document:#}");
        assert_eq!(
            document["spec"]["reason"], "stop-unresolved",
            "{document:#}"
        );
        let detail = document["spec"]["detail"].as_str().unwrap();
        assert!(detail.contains(named), "{detail}");
    }
    // `results` refuses it alike, and its document names the stop as `check`'s does.
    let manifest = FlowManifest::read(&dir.join("FLOW-nothing.toml")).unwrap();
    let (document, ok) = coverage(&manifest, &CoverageOptions::default());
    assert!(!ok, "{document:#}");
    assert_eq!(document["spec"]["stage"], "stop", "{document:#}");
    assert_eq!(
        document["stop"],
        json!({"before": ["CLOCK.nothing"], "after": [], "count": 1}),
        "{document:#}"
    );
}

/// `query` and `fuzz` search runs that end at no stop, so they refuse a stopped corpus.
#[test]
fn query_and_fuzz_refuse_a_stopped_corpus() {
    let dir = fixture("verbs", &[]);
    let manifest = dir.join("FLOW.toml");
    let (query, status) = kink_flow::cli::query(
        &manifest,
        &dir.join("PATTERNS.toml"),
        &QueryOptions::default(),
    );
    assert_eq!(status, EXIT_UNASKED, "{query:#}");
    assert_eq!(query["schema"], kink_flow::query::QUERY_SCHEMA);
    assert_eq!(
        (&query["spec"]["stage"], &query["spec"]["reason"]),
        (&json!("stop"), &json!("unsupported-verb")),
        "{query:#}"
    );
    let (fuzz, status) = kink_flow::cli::fuzz(
        &manifest,
        &dir.join("TEMPLATES.toml"),
        &FuzzRequest {
            template: "t".into(),
            job: FuzzJobRequest::Rule {
                rule: "CLOCK.tick".into(),
                fired: false,
            },
            options: kink_flow::fuzz::FuzzOptions::default(),
        },
    );
    assert_eq!(status, EXIT_UNASKED, "{fuzz:#}");
    assert_eq!(
        (&fuzz["spec"]["stage"], &fuzz["spec"]["reason"]),
        (&json!("stop"), &json!("unsupported-verb")),
        "{fuzz:#}"
    );
}

/// The outcome cache's tests.
mod kink_tier {
    use super::*;

    /// A cached outcome answers only for the stop it was decided under: a second run with the same
    /// stop reads the cache, and a run with another count misses it.
    #[test]
    #[ignore = "kink"]
    fn a_cached_outcome_misses_when_the_count_changes() {
        let dir = fixture(
            "cache",
            &[(
                "three",
                &stopped("[stop]\nbefore = [\"CLOCK.frame\"]\ncount = 3\n"),
            )],
        );
        let cold = search(&dir.join("FLOW.toml"));
        let warm = search(&dir.join("FLOW.toml"));
        assert_eq!(
            warm["outcome_cache"]["context_sha256"],
            cold["outcome_cache"]["context_sha256"]
        );
        assert_eq!(
            row(&warm, "clock/tick-twice")["killer_source"],
            "outcome-cache"
        );
        let three = search(&dir.join("FLOW-three.toml"));
        assert_ne!(
            three["outcome_cache"]["context_sha256"],
            cold["outcome_cache"]["context_sha256"]
        );
        assert_eq!(status(&three, "clock/tick-twice").0, "killed", "{three:#}");
        assert_ne!(
            row(&three, "clock/tick-twice")["killer_source"],
            "outcome-cache"
        );
    }
}
