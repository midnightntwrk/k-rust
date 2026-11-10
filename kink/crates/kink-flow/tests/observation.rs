//! `[observe]`: observation channels every run is compared by besides its end, so that a program
//! that never ends is a case, compared over the prefix its budget explores. The declaration
//! decodes strictly and the K front end refuses what names a function of an observer; it keys
//! every cached result and outcome it changes and no other; every document names it; a run's
//! kill on a channel names its position and both elements, the baseline's re-derived by a capture
//! run; a survivor that agrees only up to a horizon says so; `run --verify` re-derives every
//! cached observation outcome; `query` and `fuzz`'s single-definition jobs ignore the
//! observations, saying why, and `fuzz` refuses a kill job, which judges ends, on a corpus with
//! them.
//!
//! The fixture is testdata/flow/console: `console.k` (testdata/k/console.k), a free-running
//! console whose `tick` advances the count `<n>` and whose `emit` appends `show(n)` to the `<out>`
//! log every third step; no run of `run` ends on its own, so the depth bound of 24 cuts it after
//! 16 ticks and 8 emits, and the program is a prefix program. `FLOW.toml` observes the count
//! before each tick (`clock`, collapse) and the log (`out`, read at each tick and at the end);
//! `show(6)`, the log's third item, is no value, so the log's horizon is 2. Its mutations
//! (`mutations/console.toml`) speed up `tick` (`tick-twice`), make every second step emit
//! (`emit-every-second`), change `stall`, which no run of `run` takes within its budget
//! (`stall-longer`),
//! delete `tick` (`tick-deleted`) and halt the console before its fourth tick (`halt-early`).

use kink_campaign::{
    BaselineRecord, ChannelEnd, ChannelRecord, Element, ObservationVerdict, Opened, Opening,
    OracleOutcome, Position,
};
use kink_flow::{
    FlowManifest,
    cli::{
        CheckOptions, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, FuzzJobRequest, FuzzRequest, check,
        check_with,
    },
    coverage::{CoverageOptions, coverage},
    digest::{EXECUTION_DIGEST_KIND, ExecutionDigest, outcome_context},
    manifest::{Budget, ManifestError},
    mutation::MutationList,
    query::QueryOptions,
    results::{BaselineRunner, result_key},
    search::{RunMode, RunOptions, run_with},
};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

const SPEC: &str = "[spec]\nentry = \"console.k\"\nmain_module = \"CONSOLE\"\n";
const PROGRAM: &str = "[[program]]\nid = \"a\"\ntext = \"run\"\n";

fn decode(text: &str) -> Result<FlowManifest, ManifestError> {
    FlowManifest::decode(text, Path::new("corpus"))
}

fn flow() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/console")
}

/// A private copy of the fixture, with each `(name, text)` of `extra` written as
/// `FLOW-<name>.toml` beside it.
fn fixture(test: &str, extra: &[(&str, &str)]) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-observation-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("mutations")).unwrap();
    for name in ["console.k", "FLOW.toml", "mutations/console.toml"] {
        fs::copy(flow().join(name), dir.join(name)).unwrap();
    }
    for (name, text) in extra {
        fs::write(dir.join(format!("FLOW-{name}.toml")), text).unwrap();
    }
    dir
}

/// `FLOW.toml` with `from` replaced by `to`.
fn edited(from: &str, to: &str) -> String {
    let manifest = fs::read_to_string(flow().join("FLOW.toml")).unwrap();
    assert!(manifest.contains(from), "{from}");
    manifest.replace(from, to)
}

fn search(manifest: &Path, mode: RunMode) -> (Value, bool) {
    run_with(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("mutations")).unwrap(),
        &RunOptions::default(),
        mode,
    )
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

/// The one executed entry of the row of mutation `id`.
fn entry<'d>(document: &'d Value, id: &str) -> &'d Value {
    let executed = row(document, id)["executed"].as_array().unwrap();
    assert_eq!(executed.len(), 1, "{executed:#?}");
    &executed[0]
}

fn status(document: &Value, id: &str) -> (String, Value) {
    let row = row(document, id);
    (
        row["status"].as_str().unwrap().to_owned(),
        row["reason"].clone(),
    )
}

/// A printed value as the evidence gives it: K text, not cut.
fn printed(text: &str) -> Value {
    json!({"rendering": "k", "text": text, "truncated": false})
}

/// The declaration's tables decode into point classes and logs, their rules sorted, and every
/// key that names a function of an observer is kept for a front end that evaluates one.
#[test]
fn observe_decodes_classes_and_logs() {
    let manifest = decode(&format!(
        "{SPEC}[observe]\nobserver = \"pkg:views\"\n\n\
         [[observe.point]]\nname = \"clock\"\nbefore = [\"B.y\", \"B.x\"]\nafter = [\"A.z\"]\n\
         stutter = \"count\"\ncells = [\"n\", \"phase\"]\nviews = {{ n = \"View\" }}\n\
         components = [{{ name = \"c\" }}]\nwhen = {{ function = \"F\", cells = [\"n\"] }}\n\n\
         [[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"clock\"]\nelement = \"Tier\"\n\n\
         {PROGRAM}"
    ))
    .unwrap();
    let observe = manifest.observe.as_ref().unwrap();
    let point = &observe.points[0];
    assert_eq!(point.before, ["B.x", "B.y"]);
    assert_eq!(point.after, ["A.z"]);
    assert_eq!(point.stutter, kink_campaign::Stutter::Count);
    assert_eq!(point.cells, ["n", "phase"]);
    assert_eq!(
        observe.front_end_keys(),
        [
            "observe.observer",
            "observe.point[0].components",
            "observe.point[0].views",
            "observe.point[0].when",
            "observe.log[0].element",
        ]
    );
    // A declaration with a front end's key states no observation kink-flow compares by.
    assert_eq!(manifest.observe_value(), None);
    let plain = decode(&format!(
        "{SPEC}[[observe.point]]\nname = \"clock\"\nbefore = [\"CONSOLE.tick\"]\n\
         stutter = \"collapse\"\ncells = [\"n\"]\n\n\
         [[observe.log]]\nname = \"out\"\ncell = \"out\"\n\n{PROGRAM}"
    ))
    .unwrap();
    assert_eq!(
        plain.observe_value(),
        Some(json!({
            "points": [{"name": "clock", "before": ["CONSOLE.tick"], "after": [], "cells": ["n"],
                        "stutter": "collapse"}],
            "logs": [{"name": "out", "cell": "out", "at": []}],
        }))
    );
    assert_eq!(decode(&format!("{SPEC}{PROGRAM}")).unwrap().observe, None);
}

/// Decoding refuses an unknown key, a declaration with no channel, a class with no rule, a rule
/// on both sides, a missing or unknown stuttering mode, a repeated or empty name, two channels of
/// one name, a log read at a class the declaration does not have, and a front end's key of the
/// wrong shape.
#[test]
fn observe_decoding_refuses_what_it_cannot_read() {
    let point = "[[observe.point]]\nname = \"c\"\nbefore = [\"X.a\"]\nstutter = \"count\"\n";
    for (observe, key, message) in [
        (
            "[observe]\nwhatever = 1\n",
            "observe.whatever",
            "unknown key",
        ),
        ("[observe]\n", "observe", "declares no channel"),
        (
            "[observe]\npoint = 1\n",
            "observe.point",
            "expected [[observe.point]]",
        ),
        (
            &format!("{point}views2 = 1\n"),
            "observe.point[0].views2",
            "unknown key",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nstutter = \"count\"\n",
            "observe.point[0]",
            "names no rule",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nbefore = [\"X.a\"]\nafter = [\"X.a\"]\n\
             stutter = \"count\"\n",
            "observe.point[0]",
            "in both before and after",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nbefore = [\"X.a\"]\n",
            "observe.point[0].stutter",
            "has no default",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nbefore = [\"X.a\"]\nstutter = \"every\"\n",
            "observe.point[0].stutter",
            "expected \"collapse\" or \"count\"",
        ),
        (
            "[[observe.point]]\nbefore = [\"X.a\"]\nstutter = \"count\"\n",
            "observe.point[0].name",
            "missing required key",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nbefore = [\"X.a\", \"X.a\"]\nstutter = \"count\"\n",
            "observe.point[0].before",
            "names `X.a` twice",
        ),
        (
            "[[observe.point]]\nname = \"c\"\nbefore = [\"\"]\nstutter = \"count\"\n",
            "observe.point[0].before[0]",
            "expected a nonempty string",
        ),
        (
            &format!("{point}cells = [\"n\", \"n\"]\n"),
            "observe.point[0].cells",
            "names `n` twice",
        ),
        (
            &format!("{point}\n[[observe.log]]\nname = \"c\"\ncell = \"out\"\n"),
            "observe",
            "names the channel `c` twice",
        ),
        (
            &format!("{point}\n[[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"d\"]\n"),
            "observe.log[0].at",
            "names `d`, which is no [[observe.point]]",
        ),
        (
            "[[observe.log]]\nname = \"out\"\n",
            "observe.log[0].cell",
            "missing required key",
        ),
        (
            &format!("{point}views = {{ n = 1 }}\n"),
            "observe.point[0].views",
            "a table of nonempty strings",
        ),
        (
            &format!("{point}components = [1]\n"),
            "observe.point[0].components",
            "an array of tables",
        ),
        (
            &format!("{point}when = \"F\"\n"),
            "observe.point[0].when",
            "expected a table",
        ),
        (
            "[observe]\nobserver = \"\"\n\n[[observe.log]]\nname = \"out\"\ncell = \"out\"\n",
            "observe.observer",
            "a nonempty string",
        ),
        (
            "[[observe.log]]\nname = \"out\"\ncell = \"out\"\nelement = 3\n",
            "observe.log[0].element",
            "a nonempty string",
        ),
    ] {
        let error = decode(&format!("{SPEC}{observe}\n{PROGRAM}"))
            .expect_err("the manifest must be refused");
        assert_eq!(error.key, key, "{observe}: {error}");
        assert!(error.message.contains(message), "{observe}: {error}");
    }
}

/// The K front end refuses what it cannot state at stage `observe`: a function of an observer
/// (`unsupported-front-end`), a rule no rewrite rule is labelled with (`point-unresolved`; an
/// equation's label names no step), and a cell the configuration does not have or a log cell that
/// holds no `List` (`cell-refused`). `coverage` refuses it alike, naming the declaration.
#[test]
fn the_k_front_end_refuses_what_it_cannot_observe() {
    let dir = fixture(
        "refused",
        &[
            (
                "views",
                &edited(
                    "cells = [\"n\"]\n",
                    "cells = [\"n\"]\nviews = { n = \"View\" }\n",
                ),
            ),
            (
                "equation",
                &edited("before = [\"CONSOLE.tick\"]", "before = [\"CONSOLE.show\"]"),
            ),
            (
                "nothing",
                &edited(
                    "before = [\"CONSOLE.tick\"]",
                    "before = [\"CONSOLE.nothing\"]",
                ),
            ),
            ("cell", &edited("cells = [\"n\"]", "cells = [\"count\"]")),
            ("list", &edited("cell = \"out\"", "cell = \"n\"")),
        ],
    );
    for (name, reason, named) in [
        ("views", "unsupported-front-end", "observe.point[0].views"),
        ("equation", "point-unresolved", "`CONSOLE.show`"),
        ("nothing", "point-unresolved", "`CONSOLE.nothing`"),
        ("cell", "cell-refused", "`count`"),
        ("list", "cell-refused", "does not hold a List"),
    ] {
        let (document, status) = check(&dir.join(format!("FLOW-{name}.toml")));
        assert_eq!(status, EXIT_UNASKED, "{name}: {document:#}");
        assert_eq!(document["spec"]["stage"], "observe", "{name}: {document:#}");
        assert_eq!(document["spec"]["reason"], reason, "{name}: {document:#}");
        let detail = document["spec"]["detail"].as_str().unwrap();
        assert!(detail.contains(named), "{name}: {detail}");
    }
    let manifest = FlowManifest::read(&dir.join("FLOW-nothing.toml")).unwrap();
    let (document, ok) = coverage(&manifest, &CoverageOptions::default());
    assert!(!ok, "{document:#}");
    assert_eq!(document["spec"]["stage"], "observe", "{document:#}");
    assert_eq!(
        document["observe"]["points"][0]["before"],
        json!(["CONSOLE.nothing"]),
        "{document:#}"
    );
}

/// The declaration keys exactly what it changes: a result key and a tier-1 context without one
/// have exactly the members they had, and one adds only `observe`.
#[test]
fn a_key_and_a_context_without_observe_are_the_ones_before_observations() {
    let build = kink_patch::sha256(b"kink build");
    let execution = ExecutionDigest {
        kind: EXECUTION_DIGEST_KIND,
        digest: kink_patch::sha256(b"specification"),
    };
    let projection = kink_flow::ResultProjection {
        state: kink_campaign::StateProjection::WholeTerm,
        compared: None,
        not_compared: Vec::new(),
        unobservable: Vec::new(),
    };
    let program = kink_patch::sha256(b"program");
    let observe = json!({"points": [], "logs": [{"name": "out", "cell": "out", "at": []}]});
    let key = result_key(
        execution,
        program,
        Budget::default(),
        Some(build),
        None,
        None,
        None,
    );
    let keys = |value: &Value| {
        value
            .as_object()
            .unwrap()
            .keys()
            .cloned()
            .collect::<Vec<_>>()
    };
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
    let observed = result_key(
        execution,
        program,
        Budget::default(),
        Some(build),
        None,
        None,
        Some(observe.clone()),
    );
    let mut without = observed.clone();
    without.as_object_mut().unwrap().remove("observe");
    assert_eq!(without, key);
    assert_eq!(observed["observe"], observe);
    let context = |observe: Option<&Value>| {
        outcome_context(
            build,
            execution,
            Budget::default(),
            &projection,
            None,
            None,
            observe,
        )
    };
    assert!(context(None).get("observe").is_none());
    let mut without = context(Some(&observe));
    assert_eq!(without["observe"], observe);
    without.as_object_mut().unwrap().remove("observe");
    assert_eq!(without, context(None));
}

/// The console's run is cut by its depth bound: under `[observe]` the program is
/// `comparable-prefix`, its row names the channels its baseline recorded and their horizons, its
/// record misses once the declaration changes, and an end expectation on it is inconclusive.
#[test]
fn a_prefix_program_is_recorded_under_its_declaration() {
    let dir = fixture(
        "results",
        &[(
            "count",
            &edited("stutter = \"collapse\"", "stutter = \"count\""),
        )],
    );
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (cold, ok) = coverage(&manifest, &CoverageOptions::default());
    assert!(ok, "{cold:#}");
    assert_eq!(cold["version"], 23);
    assert_eq!(cold["observe"], manifest.observe_value().unwrap());
    let program = &cold["programs"][0];
    assert_eq!(program["class"], "comparable-prefix", "{program:#}");
    assert_eq!(program["cached"], false, "{program:#}");
    // The clock opens where the depth bound cut the path, the log at `show(6)`, which is no value.
    assert_eq!(
        program["observations"]["horizon"],
        json!({"clock": {"elements": 16, "opening": "bound"},
               "out": {"elements": 2, "opening": "undecided-element"}})
    );
    let channels = program["observations"]["channels"].as_array().unwrap();
    assert_eq!(channels[0]["elements"], 16);
    assert_eq!(channels[0]["closed"], Value::Null);
    assert_eq!(channels[0]["open"]["index"], 16);
    assert_eq!(channels[0]["open"]["opening"], "bound");
    assert_eq!(channels[1]["open"]["opening"], "undecided-element");
    assert_eq!(channels[1]["elements"], 2);
    let (warm, ok) = coverage(&manifest, &CoverageOptions::default());
    assert!(ok, "{warm:#}");
    assert_eq!(warm["programs"][0]["cached"], true, "{warm:#}");
    assert_eq!(warm["programs"][0]["observations"], program["observations"]);
    // Another stuttering mode is another declaration: the record misses, and under `count` the
    // clock has an element per tick, as many as under `collapse` here since every tick moves it.
    let count = FlowManifest::read(&dir.join("FLOW-count.toml")).unwrap();
    let (counted, ok) = coverage(&count, &CoverageOptions::default());
    assert!(ok, "{counted:#}");
    assert_eq!(counted["programs"][0]["cached"], false, "{counted:#}");
    assert_eq!(counted["programs"][0]["class"], "comparable-prefix");
    // `check` names the declaration, and its exit status reads a prefix program as answered.
    let (check, status) = check(&dir.join("FLOW.toml"));
    assert_eq!(status, EXIT_YES, "{check:#}");
    assert_eq!(check["version"], 15);
    assert_eq!(check["observe"], manifest.observe_value().unwrap());
}

/// Each mutation is judged by the channels: a faster tick is killed at the clock's element 1 and
/// a mutant that emits every second step at the log's element 1, each with its position and both
/// elements, the baseline's from a capture run; a mutant whose difference lies past the log's
/// horizon survives and says so; a mutant without the clock's rule is not admitted, and `check`
/// warns of the deletion; a mutant that halts early is killed by its END.
#[test]
fn mutations_of_the_console_are_judged_by_its_channels() {
    let dir = fixture("run", &[]);
    let manifest = dir.join("FLOW.toml");
    let (document, _) = search(&manifest, RunMode::Search);
    assert_eq!(document["version"], 41);
    assert_eq!(
        document["observe"],
        FlowManifest::read(&manifest)
            .unwrap()
            .observe_value()
            .unwrap()
    );
    assert_eq!(document["programs"][0]["class"], "comparable-prefix");

    assert_eq!(
        status(&document, "console/tick-twice"),
        ("killed".to_owned(), Value::Null)
    );
    let killed = entry(&document, "console/tick-twice");
    assert_eq!(killed["outcome"], "distinguish", "{killed:#}");
    assert_eq!(
        killed["slots"]["observations"],
        json!({"outcome": "distinguish",
               "position": {"channel": "clock", "index": 1, "at_end": false},
               "sides": {"baseline": {"cells": {"n": printed("1")}},
                         "mutant": {"cells": {"n": printed("2")}}}}),
        "{killed:#}"
    );
    // A prefix program's end slots compare nothing within its horizon.
    assert_eq!(killed["slots"]["exit-stop"]["outcome"], "agree");
    assert_eq!(
        killed["difference"],
        json!({
            "format": "kink-k/1",
            "position": {"channel": "clock", "index": 1, "at_end": false},
            "baseline": {"element": {"cells": {"n": printed("1")}}},
            "mutant": {"element": {"cells": {"n": printed("2")}}},
        }),
        "{killed:#}"
    );

    assert_eq!(status(&document, "console/emit-every-second").0, "killed");
    assert_eq!(
        entry(&document, "console/emit-every-second")["difference"],
        json!({
            "format": "kink-k/1",
            "position": {"channel": "out", "index": 1, "at_end": false},
            "baseline": {"element": {"item": printed("4")}},
            "mutant": {"element": {"item": printed("3")}},
        })
    );

    let survivor = row(&document, "console/stall-longer");
    assert_eq!(survivor["status"], "survived", "{survivor:#}");
    let horizon = json!({"clock": {"elements": 16, "opening": "bound"},
                         "out": {"elements": 2, "opening": "undecided-element"}});
    assert_eq!(
        survivor["horizon"],
        json!([{"program": "run", "horizon": horizon}]),
        "{survivor:#}"
    );
    // The clock's horizon is a bound's, so a larger budget observes more of it.
    let action = survivor["action"].as_str().unwrap();
    assert!(
        action.contains("horizon") && action.starts_with("raise the bound"),
        "{survivor:#}"
    );
    assert_eq!(
        entry(&document, "console/stall-longer")["slots"]["observations"],
        json!({"outcome": "agree", "horizon": horizon})
    );

    assert_eq!(
        status(&document, "console/tick-deleted"),
        ("not-admitted".to_owned(), json!("point-unresolved"))
    );
    assert!(
        row(&document, "console/tick-deleted")["action"]
            .as_str()
            .unwrap()
            .contains("point class"),
    );

    assert_eq!(status(&document, "console/halt-early").0, "killed");
    let ended = entry(&document, "console/halt-early");
    assert_eq!(ended["difference"]["position"]["at_end"], true, "{ended:#}");
    assert_eq!(ended["difference"]["mutant"]["element"], "end", "{ended:#}");

    // The verdicts rendering says which survivor rests on a horizon.
    let verdicts = kink_flow::verdicts::verdicts(&document).unwrap();
    assert!(verdicts.contains("\nversion = 27\n"), "{verdicts}");
    assert!(
        verdicts.contains(
            "\nhorizon = [\n  { program = \"run\", channel = \"clock\", elements = 16, \
             opening = \"bound\" },\n  { program = \"run\", channel = \"out\", elements = 2, \
             opening = \"undecided-element\" },\n]\n"
        ),
        "{verdicts}"
    );

    let (check, status) = check_with(
        &manifest,
        &CheckOptions {
            mutations: Some(dir.join("mutations")),
            ..CheckOptions::default()
        },
    );
    assert_eq!(status, EXIT_YES, "{check:#}");
    let deleted = check["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == "console/tick-deleted")
        .unwrap();
    assert!(
        deleted["warnings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|warning| warning["reason"] == "point-rule-deleted"),
        "{deleted:#}"
    );
}

/// The console started from a count of -1003 (in a private copy of `console.k`) reaches -1000
/// after three ticks and idles there: the baseline's path returns to an earlier state with nothing
/// new observed, so both channels are closed by the cycle, complete after three clock elements
/// and one log item, and the program states no horizon. A mutant that emits every second step
/// ticks at the same counts and idles alike: it agrees on everything and survives with no
/// horizon. A mutant whose `idle` waits for a count of 3 ticks on, and its clock's element 3 is a
/// difference against the baseline's silence, the baseline's side of which is `cycle`.
#[test]
fn a_baseline_closed_by_a_cycle_states_no_horizon() {
    let dir = fixture("cycle", &[]);
    let console = fs::read_to_string(dir.join("console.k")).unwrap();
    let from = "<n> 0 </n>";
    assert!(console.contains(from));
    fs::write(
        dir.join("console.k"),
        console.replace(from, "<n> -1003 </n>"),
    )
    .unwrap();
    fs::write(
        dir.join("mutations/console.toml"),
        r#"[[mutation]]
id = "emit-every-second"
misunderstanding = "an emit resets the phase to 1, so every second step emits"

  [[mutation.edit]]
  rule = "emit"
  find = "<phase> 2 => 0 </phase>"
  replace = "<phase> 2 => 1 </phase>"

[[mutation]]
id = "idle-at-three"
misunderstanding = "the console idles once the count is 3"

  [[mutation.edit]]
  rule = "idle"
  find = "N ==Int -1000"
  replace = "N ==Int 3"
"#,
    )
    .unwrap();
    let (document, _) = search(&dir.join("FLOW.toml"), RunMode::Search);
    let program = &document["programs"][0];
    assert_eq!(program["class"], "comparable-prefix", "{program:#}");
    assert_eq!(program["observations"]["horizon"], json!({}), "{program:#}");
    let channels = program["observations"]["channels"].as_array().unwrap();
    assert_eq!(
        channels
            .iter()
            .map(|channel| (channel["elements"].clone(), channel["closed"].clone()))
            .collect::<Vec<_>>(),
        [(json!(3), json!("cycle")), (json!(1), json!("cycle"))],
        "{program:#}"
    );
    assert!(channels.iter().all(|channel| channel["open"].is_null()));

    let survivor = row(&document, "console/emit-every-second");
    assert_eq!(survivor["status"], "survived", "{survivor:#}");
    assert!(
        survivor.get("horizon").is_none_or(Value::is_null),
        "{survivor:#}"
    );
    assert_eq!(
        entry(&document, "console/emit-every-second")["slots"]["observations"],
        json!({"outcome": "agree"})
    );

    assert_eq!(status(&document, "console/idle-at-three").0, "killed");
    assert_eq!(
        entry(&document, "console/idle-at-three")["difference"],
        json!({
            "format": "kink-k/1",
            "position": {"channel": "clock", "index": 3, "at_end": false},
            "baseline": {"element": "cycle"},
            "mutant": {"element": {"cells": {"n": printed("-1000")}}},
        })
    );
}

/// `run --verify` re-derives every cached observation outcome: a second run decides from tier 1
/// with each record's position and horizon, and a verifying run finds no record that differs from
/// its live run.
#[test]
fn run_verify_rederives_observation_outcomes() {
    let dir = fixture("verify", &[]);
    let manifest = dir.join("FLOW.toml");
    let (cold, _) = search(&manifest, RunMode::Search);
    let (warm, _) = search(&manifest, RunMode::Search);
    assert_eq!(
        row(&warm, "console/tick-twice")["killer_source"],
        "outcome-cache",
        "{warm:#}"
    );
    for id in [
        "console/tick-twice",
        "console/stall-longer",
        "console/halt-early",
    ] {
        let (cached, live) = (entry(&warm, id), entry(&cold, id));
        assert_eq!(cached["cached"], true, "{id}: {cached:#}");
        assert_eq!(cached["slots"], live["slots"], "{id}");
        assert_eq!(cached["difference"], live["difference"], "{id}");
    }
    assert_eq!(
        row(&warm, "console/stall-longer")["horizon"],
        row(&cold, "console/stall-longer")["horizon"]
    );
    let (verified, ok) = search(&manifest, RunMode::Verify);
    assert!(ok, "{verified:#}");
    assert_eq!(verified["mismatches"], json!([]), "{verified:#}");
}

/// A difference is reported only when both sides' values re-derive it: the capture run of the
/// baseline reads the element whose digest the record keeps, a record whose digest bytes the
/// capture run's element does not have is an error, and so is a mutant element equal to the
/// baseline's or undecided against its content.
#[test]
fn a_capture_run_rederives_the_baselines_element() {
    let dir = fixture("capture", &[]);
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let (_, admitted) = kink_flow::admit_spec(&manifest);
    let (spec, mut inputs) = admitted.expect("the console is admitted");
    let mut session = inputs.session(&spec);
    let program = &manifest.programs[0];
    let case = session.read(program).unwrap();
    let mut test = session.test_case(program, &case).unwrap();
    test.oracles = spec.result.oracles();
    let runner = BaselineRunner::new(&spec, &manifest).unwrap();
    let result = runner.run(test.clone());
    // The record the baseline's run kept, read back from its row.
    let record = &result.baseline.as_ref().unwrap()["observations"];
    let digest = |hex: &Value| {
        let hex = hex.as_str().unwrap();
        let mut bytes = [0; 8];
        for (index, byte) in bytes.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&hex[2 * index..2 * index + 2], 16).unwrap();
        }
        Some(bytes)
    };
    let channel = |index: usize| ChannelRecord {
        name: record["channels"][index]["name"]
            .as_str()
            .unwrap()
            .to_owned(),
        elements: record["channels"][index]["elements"]
            .as_array()
            .unwrap()
            .iter()
            .map(digest)
            .collect(),
        end: ChannelEnd::Open(Opened::new(Opening::Bound, "the path was cut by a bound")),
    };
    let mut baseline = BaselineRecord {
        channels: vec![channel(0), channel(1)],
        prefix: true,
        crashed: false,
        refusal: None,
        paths: None,
    };
    let int = |value: i64| {
        k_rust::kore::parser::parse_pattern(&format!("\\dv{{SortInt{{}}}}(\"{value}\")")).unwrap()
    };
    let verdict = |mutant: i64| ObservationVerdict {
        outcome: OracleOutcome::Distinguish,
        position: Some(Position {
            channel: "clock".to_owned(),
            index: 1,
            at_end: false,
            outside: None,
        }),
        horizon: BTreeMap::new(),
        cause: None,
        element: Some(Element::Content(vec![int(mutant)])),
        cycle: None,
    };
    let derived = runner
        .observed_difference(&test, &baseline, &verdict(2))
        .unwrap();
    assert_eq!(derived.baseline, Element::Content(vec![int(1)]));
    assert_eq!(derived.mutant, Element::Content(vec![int(2)]));
    let equal = runner
        .observed_difference(&test, &baseline, &verdict(1))
        .unwrap_err();
    assert!(equal.contains("are equal"), "{equal}");
    // A recorded content differs in every model from a content or a closure, never from an
    // element whose value is not known.
    let undecided = runner
        .observed_difference(
            &test,
            &baseline,
            &ObservationVerdict {
                element: Some(Element::Undecided),
                ..verdict(2)
            },
        )
        .unwrap_err();
    assert!(undecided.contains("only from a closure"), "{undecided}");
    baseline.channels[0].elements[1] = Some([0; 8]);
    let mismatch = runner
        .observed_difference(&test, &baseline, &verdict(2))
        .unwrap_err();
    assert!(
        mismatch.contains("does not have the recorded digest"),
        "{mismatch}"
    );
}

/// Under `count` an event whose content is not decided is still an element: the log cell before
/// each tick holds `show(6)`, no value, from the seventh tick on, so the baseline's element 6 is
/// undecided, and a mutant that halts once the count passes 5 ends its channel there. END against
/// an element, decided or not, is a decided difference; the capture run re-derives the baseline's
/// undecided element, and the mutant is killed with that evidence.
#[test]
fn an_end_against_an_undecided_element_kills_under_count() {
    let dir = fixture("count-end", &[]);
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"console.k\"\nmain_module = \"CONSOLE\"\n\
         syntax_module = \"CONSOLE-SYNTAX\"\n\n[budget]\nmax_depth = 24\n\n\
         [[observe.point]]\nname = \"trace\"\nbefore = [\"CONSOLE.tick\"]\n\
         stutter = \"count\"\ncells = [\"out\"]\n\n\
         [[program]]\nid = \"run\"\ntext = \"run\"\n",
    )
    .unwrap();
    fs::write(
        dir.join("mutations/console.toml"),
        "[[mutation]]\nid = \"halt-after-five\"\n\
         misunderstanding = \"the console halts once the count passes 5\"\n\n\
         [[mutation.edit]]\nrule = \"halt\"\nfind = \"N >Int 1000000\"\n\
         replace = \"N >Int 5\"\n",
    )
    .unwrap();
    let (document, _) = search(&dir.join("FLOW.toml"), RunMode::Search);
    assert_eq!(document["programs"][0]["class"], "comparable-prefix");
    assert_eq!(
        status(&document, "console/halt-after-five"),
        ("killed".to_owned(), Value::Null),
        "{document:#}"
    );
    let killed = entry(&document, "console/halt-after-five");
    assert_eq!(
        killed["difference"],
        json!({
            "format": "kink-k/1",
            "position": {"channel": "trace", "index": 6, "at_end": true},
            "baseline": {"element": "undecided"},
            "mutant": {"element": "end"},
        }),
        "{killed:#}"
    );
}

/// A horizon says why its channel opened, and the survivor's action follows it: observing the
/// log cell before each tick (collapsed) and the log, both of which open at `show(6)` (no value)
/// before the depth bound cuts the path, a mutant that agrees up to them survives with the
/// opening `undecided-element`, and its action does not ask for a larger budget, which would
/// reach the same element.
#[test]
fn a_horizon_not_cut_by_a_bound_asks_for_another_program() {
    let dir = fixture("opened", &[]);
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"console.k\"\nmain_module = \"CONSOLE\"\n\
         syntax_module = \"CONSOLE-SYNTAX\"\n\n[budget]\nmax_depth = 24\n\n\
         [[observe.point]]\nname = \"clock\"\nbefore = [\"CONSOLE.tick\"]\n\
         stutter = \"collapse\"\ncells = [\"out\"]\n\n\
         [[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"clock\"]\n\n\
         [[program]]\nid = \"run\"\ntext = \"run\"\n",
    )
    .unwrap();
    let mutations = fs::read_to_string(dir.join("mutations/console.toml")).unwrap();
    let stall = &mutations[mutations
        .find("[[mutation]]\nid = \"stall-longer\"")
        .unwrap()..];
    let stall = &stall[..stall[1..]
        .find("[[mutation]]")
        .map_or(stall.len(), |end| end + 1)];
    fs::write(dir.join("mutations/console.toml"), stall).unwrap();
    let (document, _) = search(&dir.join("FLOW.toml"), RunMode::Search);
    let survivor = row(&document, "console/stall-longer");
    assert_eq!(survivor["status"], "survived", "{survivor:#}");
    let horizon = &survivor["horizon"][0]["horizon"];
    assert_eq!(
        *horizon,
        json!({"clock": {"elements": 3, "opening": "undecided-element"},
               "out": {"elements": 2, "opening": "undecided-element"}}),
        "{survivor:#}"
    );
    let action = survivor["action"].as_str().unwrap();
    assert!(
        action.starts_with("write another program") && !action.contains("raise the bound"),
        "{action}"
    );
}

/// A prefix program none of whose channels kept an element within its budget observed nothing:
/// observing only `stall`, which no run of `run` takes, the program is `unknown`, its cause says
/// why each channel opened, and `coverage` exits as for any program it cannot compare.
#[test]
fn a_prefix_program_that_observed_nothing_is_unknown() {
    let dir = fixture("nothing", &[]);
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"console.k\"\nmain_module = \"CONSOLE\"\n\
         syntax_module = \"CONSOLE-SYNTAX\"\n\n[budget]\nmax_depth = 24\n\n\
         [[observe.point]]\nname = \"stalls\"\nbefore = [\"CONSOLE.stall\"]\n\
         stutter = \"collapse\"\ncells = [\"n\"]\n\n\
         [[program]]\nid = \"run\"\ntext = \"run\"\n",
    )
    .unwrap();
    let (document, status) =
        kink_flow::cli::coverage(&dir.join("FLOW.toml"), &CoverageOptions::default());
    assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
    let program = &document["programs"][0];
    assert_eq!(program["class"], "unknown", "{program:#}");
    let cause = program["cause"].as_str().unwrap();
    assert!(
        cause.starts_with("observed-nothing:")
            && cause.contains("`stalls` opened before its first element (bound"),
        "{cause}"
    );
}

/// `kink-flow fuzz` on the fixture in `dir` with the template `t` (`run`, no hole) and the
/// pattern `two` (`<n> 2 </n>`) beside it, confirming, on a thread with the command's stack.
fn fuzz(dir: &Path, job: FuzzJobRequest) -> (Value, u8) {
    let dir = dir.to_path_buf();
    fs::write(
        dir.join("TEMPLATES.toml"),
        "[[template]]\nid = \"t\"\ntext = \"run\"\n",
    )
    .unwrap();
    fs::write(
        dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"two\"\npattern = \"<n> 2 </n>\"\n",
    )
    .unwrap();
    std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(move || {
            kink_flow::cli::fuzz(
                &dir.join("FLOW.toml"),
                &dir.join("TEMPLATES.toml"),
                &FuzzRequest {
                    template: "t".into(),
                    job,
                    options: kink_flow::fuzz::FuzzOptions {
                        budget: k_rust_fuzz::Budget::Cases(3),
                        confirm: true,
                        ..kink_flow::fuzz::FuzzOptions::default()
                    },
                },
            )
        })
        .unwrap()
        .join()
        .unwrap()
}

/// A kill job's campaign compares the two definitions' ends, and a kill of a corpus with
/// observations is a decided difference of a channel, so `fuzz` refuses it, naming the kill
/// judgement; the document names the declaration.
#[test]
fn fuzz_refuses_a_kill_job_on_a_corpus_with_observations() {
    let dir = fixture("fuzz-kill", &[]);
    let (fuzz, status) = fuzz(
        &dir,
        FuzzJobRequest::Kill {
            mutation: "tick-twice".into(),
            mutations: dir.join("mutations/console.toml"),
        },
    );
    assert_eq!(status, EXIT_UNASKED, "{fuzz:#}");
    assert_eq!(
        (&fuzz["spec"]["stage"], &fuzz["spec"]["reason"]),
        (&json!("observe"), &json!("unsupported-verb")),
        "{fuzz:#}"
    );
    let detail = fuzz["spec"]["detail"].as_str().unwrap();
    assert!(detail.starts_with("kill judgement"), "{detail}");
    assert!(fuzz["observe"]["points"].is_array(), "{fuzz:#}");
}

/// A pattern job asks what the baseline's run reaches, which no channel changes, so `fuzz` runs
/// it on a corpus with observations, saying why it ignores them, and `query` confirms its hit.
#[test]
fn fuzz_ignores_the_observations_of_a_single_definition_job() {
    let dir = fixture("fuzz-pattern", &[]);
    let (fuzz, status) = fuzz(
        &dir,
        FuzzJobRequest::Pattern {
            id: "two".into(),
            patterns: dir.join("PATTERNS.toml"),
        },
    );
    assert_eq!(status, EXIT_YES, "{fuzz:#}");
    let ignored = fuzz["job"]["observe"]["ignored"].as_str().unwrap();
    assert!(
        ignored.contains("observation channels compare"),
        "{ignored}"
    );
    let confirmation = &fuzz["attempts"][0]["confirmation"];
    assert_eq!(confirmation["answer"], "hit", "{confirmation:#}");
    assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
}

/// A rule job asks what the baseline's run fires, which no channel changes; what the channels
/// change is which programs `coverage` counts, and it counts the console's `run`, whose every
/// run the depth bound cuts, as comparable-prefix. So a rule job's confirmation, `coverage`'s
/// own predicate, confirms that program as a witness of `tick`'s firing. The campaign does not
/// find it: k-rust-fuzz reads a rule goal at a leaf, and a path a bound cut is no hit there.
#[test]
fn a_rule_witness_coverage_counts_by_its_channels_is_confirmed() {
    let dir = fixture("fuzz-rule", &[]);
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let confirmation = std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(move || {
            kink_flow::fuzz::confirm_program(
                &manifest,
                &kink_flow::fuzz::FuzzOptions::default(),
                kink_flow::fuzz::FuzzJob::Rule {
                    rule: "CONSOLE.tick",
                    fired: true,
                },
                &manifest.programs[0],
            )
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(confirmation["confirmed"], true, "{confirmation:#}");
    assert_eq!(confirmation["status"], "fired", "{confirmation:#}");
    assert_eq!(
        confirmation["class"], "comparable-prefix",
        "{confirmation:#}"
    );
    let (fuzz, status) = fuzz(
        &dir,
        FuzzJobRequest::Rule {
            rule: "CONSOLE.tick".into(),
            fired: true,
        },
    );
    assert_eq!(status, EXIT_UNANSWERED, "{fuzz:#}");
    let ignored = fuzz["job"]["observe"]["ignored"].as_str().unwrap();
    assert!(ignored.contains("which programs"), "{ignored}");
}

/// `query` admits a corpus with observations and ignores them, saying why: a pattern query asks
/// which states one definition's run reaches, and an observation changes none of them. Its
/// answers are those of the same corpus without `[observe]`: `<n> 2 </n>` is reached, and
/// `<n> 1000 </n>` is `unknown`, since the depth bound cuts every run.
#[test]
fn query_ignores_the_observations() {
    let plain = fs::read_to_string(flow().join("FLOW.toml"))
        .unwrap()
        .split("[[observe.point]]")
        .next()
        .unwrap()
        .to_owned()
        + PROGRAM.replace("\"a\"", "\"run\"").as_str();
    let dir = fixture("query", &[("plain", &plain)]);
    fs::write(
        dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"two\"\npattern = \"<n> 2 </n>\"\n\n\
         [[pattern]]\nid = \"far\"\npattern = \"<n> 1000 </n>\"\n",
    )
    .unwrap();
    let ask = |manifest: &str| {
        let (manifest, patterns) = (dir.join(manifest), dir.join("PATTERNS.toml"));
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || kink_flow::cli::query(&manifest, &patterns, &QueryOptions::default()))
            .unwrap()
            .join()
            .unwrap()
    };
    let (observed, status) = ask("FLOW.toml");
    assert_eq!(status, EXIT_UNANSWERED, "{observed:#}");
    assert_eq!(observed["version"], 8, "{observed:#}");
    assert_eq!(
        observed["observe"]["ignored"],
        kink_flow::query::OBSERVE_IGNORED,
        "{observed:#}"
    );
    assert!(
        observed["observe"]["declaration"].is_object(),
        "{observed:#}"
    );
    let (plain, _) = ask("FLOW-plain.toml");
    assert_eq!(plain.get("observe"), None, "{plain:#}");
    let answers = |document: &Value| {
        document["rows"]
            .as_array()
            .unwrap_or_else(|| panic!("{document:#}"))
            .iter()
            .map(|row| {
                (
                    row["pattern"].clone(),
                    row["route"].clone(),
                    row["answer"].clone(),
                    row["cause"].clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(answers(&observed), answers(&plain));
    assert_eq!(
        answers(&observed)
            .iter()
            .map(|(_, route, answer, _)| (route.clone(), answer.clone()))
            .collect::<Vec<_>>(),
        [
            (json!("search"), json!("hit")),
            (json!("search"), json!("unknown"))
        ]
    );
}

/// A counter that ends: `down(N)` steps to `down(0)`, counting its steps in `<n>`.
const DOWN: &str = "module DOWN-SYNTAX\n  imports INT-SYNTAX\n  \
                    syntax Pgm ::= down(Int) [symbol(down)]\nendmodule\n\
                    module DOWN\n  imports DOWN-SYNTAX\n  imports INT\n  imports BOOL\n  \
                    configuration <k> $PGM:Pgm </k> <n> 0 </n>\n  \
                    rule [step]: <k> down(N) => down(N -Int 1) </k> <n> M => M +Int 1 </n> \
                    requires N >Int 0\nendmodule\n";

/// `query` ignores `[observe]` on a program that ends as well: `down(3)` counts to 3 and never to
/// 4, a `no` on the search route; with `[stop]` after the second step beside it, the stopped run
/// reaches 2 and not 3, a `no` past the stop, and the document names both the stop and the
/// ignored observation.
#[test]
fn query_with_observations_answers_no() {
    let dir = fixture("query-no", &[]);
    fs::write(dir.join("down.k"), DOWN).unwrap();
    let spec =
        "[spec]\nentry = \"down.k\"\nmain_module = \"DOWN\"\nsyntax_module = \"DOWN-SYNTAX\"\n\n";
    let observe = "[[observe.point]]\nname = \"count\"\nbefore = [\"DOWN.step\"]\n\
                   stutter = \"collapse\"\ncells = [\"n\"]\n\n";
    let program = "[[program]]\nid = \"three\"\ntext = \"down(3)\"\n";
    let stop = "[stop]\nafter = [\"DOWN.step\"]\ncount = 2\n\n";
    fs::write(
        dir.join("FLOW-down.toml"),
        format!("{spec}{observe}{program}"),
    )
    .unwrap();
    fs::write(
        dir.join("FLOW-stopped.toml"),
        format!("{spec}{stop}{observe}{program}"),
    )
    .unwrap();
    fs::write(
        dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"two\"\npattern = \"<n> 2 </n>\"\n\n\
         [[pattern]]\nid = \"three\"\npattern = \"<n> 3 </n>\"\n\n\
         [[pattern]]\nid = \"four\"\npattern = \"<n> 4 </n>\"\n",
    )
    .unwrap();
    let ask = |manifest: &str| {
        let (manifest, patterns) = (dir.join(manifest), dir.join("PATTERNS.toml"));
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || kink_flow::cli::query(&manifest, &patterns, &QueryOptions::default()))
            .unwrap()
            .join()
            .unwrap()
    };
    let answers = |document: &Value| {
        ["two", "three", "four"].map(|pattern| {
            let row = document["rows"]
                .as_array()
                .unwrap_or_else(|| panic!("{document:#}"))
                .iter()
                .find(|row| row["pattern"] == pattern)
                .unwrap();
            (
                row["route"].as_str().unwrap().to_owned(),
                row["answer"].as_str().unwrap().to_owned(),
            )
        })
    };
    let pair = |route: &str, answer: &str| (route.to_owned(), answer.to_owned());

    let (down, status) = ask("FLOW-down.toml");
    assert_eq!(status, EXIT_YES, "{down:#}");
    assert_eq!(
        down["observe"]["ignored"],
        kink_flow::query::OBSERVE_IGNORED
    );
    assert_eq!(down.get("stop"), None, "{down:#}");
    assert_eq!(
        answers(&down),
        [
            pair("search", "hit"),
            pair("search", "hit"),
            pair("search", "no")
        ]
    );

    let (stopped, status) = ask("FLOW-stopped.toml");
    assert_eq!(status, EXIT_YES, "{stopped:#}");
    assert_eq!(
        stopped["observe"]["ignored"],
        kink_flow::query::OBSERVE_IGNORED
    );
    assert_eq!(
        stopped["stop"],
        json!({"before": [], "after": ["DOWN.step"], "count": 2}),
        "{stopped:#}"
    );
    assert_eq!(
        answers(&stopped),
        [
            pair("stopped-run", "hit"),
            pair("stopped-run", "no"),
            pair("stopped-run", "no")
        ]
    );
}

/// Functions a front end set ([`kink_flow::FlowManifest::with_observe_functions`]); none is
/// evaluated by admission.
struct Unasked;

impl kink_flow::ObservationFunctions for Unasked {
    fn cells(&self) -> &[Vec<String>] {
        &[]
    }

    fn filtered(&self, _: usize) -> bool {
        false
    }

    fn with_evaluator(
        &self,
        _: &mut dyn FnMut(&mut dyn kink_flow::ObservationEvaluator),
    ) -> Result<(), String> {
        Err("admission evaluates nothing".to_owned())
    }
}

/// A key that names a function of an observer is the front end's: decoded as kink-flow decodes
/// it, the corpus is still refused (`unsupported-front-end`) and its runs compare no channel,
/// since kink-flow's K front end evaluates no function; with a front end's functions set, the
/// same corpus is admitted and its declaration names the functions' identity.
#[test]
fn a_front_ends_functions_admit_its_keys_and_kink_flow_alone_still_refuses_them() {
    let dir = fixture(
        "front-end",
        &[(
            "views",
            &edited(
                "cells = [\"n\"]\n",
                "cells = [\"n\"]\nviews = { n = \"View\" }\n",
            ),
        )],
    );
    let manifest = FlowManifest::read(&dir.join("FLOW-views.toml")).unwrap();
    assert!(manifest.campaign_observe().is_none());
    assert_eq!(manifest.observe_value(), None);
    let (record, admitted) = kink_flow::admit::admit_spec(&manifest);
    assert!(admitted.is_none());
    let refusal = record.refusal.unwrap();
    assert_eq!(
        (refusal.stage.as_str(), refusal.reason.as_str()),
        ("observe", "unsupported-front-end")
    );
    let identity = json!({"front end": "views"});
    let bound = manifest.with_observe_functions(kink_flow::ObserveFunctions::new(
        identity.clone(),
        std::sync::Arc::new(Unasked),
    ));
    assert_eq!(bound.observe_value().unwrap()["functions"], identity);
    let (record, admitted) = kink_flow::admit::admit_spec(&bound);
    assert!(admitted.is_some(), "{:?}", record.refusal);
}

/// A program whose run has several paths is compared by its channels' prefix sets
/// (kink-campaign `observation`, "Several paths"): `testdata/k/choice.k` from 0 appends 1 or 2 to
/// its log, each path finishing at `done`, and its end slot compares only `<k>`, which every end
/// shares. A mutation whose third path appends 3 is killed at the log's index 0, the mutant's
/// prefix outside the baseline's set; its slot names the side outside, and its evidence, which no
/// capture run re-derives, is `kink-k-sets/1` with the mutant's element. A mutation that drops
/// the behaviour 2 is killed with the baseline's prefix outside, the mutant's element absent.
#[test]
fn a_difference_of_prefix_sets_names_the_side_outside() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-observation-{}", std::process::id()))
        .join("choice");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("mutations")).unwrap();
    fs::copy(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/choice.k"),
        dir.join("choice.k"),
    )
    .unwrap();
    fs::write(
        dir.join("FLOW.toml"),
        "[spec]\nentry = \"choice.k\"\nmain_module = \"CHOICE\"\n\
         syntax_module = \"CHOICE-SYNTAX\"\n\n[budget]\nmax_depth = 8\n\n\
         [result]\ncells = [\"k\"]\n\n\
         [[observe.point]]\nname = \"finished\"\nafter = [\"CHOICE.finish\"]\n\
         stutter = \"collapse\"\ncells = []\n\n\
         [[observe.log]]\nname = \"out\"\ncell = \"out\"\nat = [\"finished\"]\n\n\
         [[program]]\nid = \"run\"\ntext = \"run\"\n",
    )
    .unwrap();
    fs::write(
        dir.join("mutations/choice.toml"),
        "[[mutation]]\nid = \"a-third\"\nmisunderstanding = \"a run may also append 3\"\n\n\
         [[mutation.edit]]\nrule = \"extra\"\nfind = \"N ==Int -1\"\nreplace = \"N ==Int 0\"\n\n\
         [[mutation]]\nid = \"no-two\"\nmisunderstanding = \"a run never appends 2\"\n\n\
         [[mutation.edit]]\nrule = \"right\"\nfind = \"N ==Int 0\"\nreplace = \"N ==Int 5\"\n",
    )
    .unwrap();
    let (document, _) = search(&dir.join("FLOW.toml"), RunMode::Search);
    assert_eq!(
        status(&document, "choice/a-third"),
        ("killed".to_owned(), Value::Null),
        "{document:#}"
    );
    let third = entry(&document, "choice/a-third");
    assert_eq!(
        third["slots"]["observations"]["position"],
        json!({"channel": "out", "index": 0, "at_end": false, "outside": "mutant"}),
        "{third:#}"
    );
    assert_eq!(
        third["difference"],
        json!({
            "format": "kink-k-sets/1",
            "position": {"channel": "out", "index": 0, "at_end": false, "outside": "mutant"},
            "mutant": {"element": {"item": printed("3")}},
        }),
        "{third:#}"
    );
    assert_eq!(status(&document, "choice/no-two").0, "killed");
    let dropped = entry(&document, "choice/no-two");
    assert_eq!(
        dropped["difference"],
        json!({
            "format": "kink-k-sets/1",
            "position": {"channel": "out", "index": 0, "at_end": false, "outside": "baseline"},
            "mutant": {"element": "absent"},
        }),
        "{dropped:#}"
    );
    // The program's row gives the prefix sets' facts: two paths (again's merges into left's,
    // with one history), a real record, and every channel explored to its end.
    let program = &document["programs"][0];
    assert_eq!(
        program["observations"],
        json!({
            "paths": 2,
            "real": true,
            "channels": [
                {"name": "finished", "complete_to": null},
                {"name": "out", "complete_to": null},
            ],
            "horizon": {},
        }),
        "{program:#}"
    );
}
