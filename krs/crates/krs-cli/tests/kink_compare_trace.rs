//! `krs kink compare` under `kink-implementation/2`: an implementation's record of the corpus's
//! `[observe]` channels compared with the definition's, element by element, up to the horizon
//! the definition's run was cut at.
//!
//! The fixture counts down as `kink_compare.rs`'s does (`tick` while `n > 0`, `done` at `n = 0`),
//! and counts up forever from a negative `n` (`spin`: `acc` gains 1 and `n` stays), so a case of
//! `n = -1` never ends: the corpus's `max_depth = 6` cuts it after six steps. The corpus stops
//! before the third `tick`. `seen` is a map no rule rewrites, `{1: n, 2: 0}` of the start's `n`.
//!
//! The channels, each read before a step of its rules:
//!
//! - `ticks` (`count`): `n` and `acc` before each `tick` and each `spin`;
//! - `downs` (`count`): the same before each `tick` alone, so it holds nothing on a run that
//!   only spins;
//! - `sign` (`collapse`): `n` before each `tick` and each `spin`, equal consecutive contents
//!   dropped;
//! - `maps` (`count`): `seen` before each `tick` and each `spin`.
//!
//! The cases: `a` (`n = 2`, ends on its own after two elements of `ticks`), `b` (`n = 5`, ends
//! at the stop after two), `z` (`n = 0`, no element), `s` (`n = -1`, never ends: six elements,
//! then the bound).
//!
//! The implementations are one shell script, `fake2.sh MODE CHANNEL [ARGUMENT [LOG]]`
//! (`-` for a mode without an argument), which
//! runs the same machine and states the one channel `CHANNEL`. It emits an element where the
//! definition does, counts its own steps as each element's `depth`, closes its channel where it
//! ends (on its own or at the stop) and answers `horizon`, its channel open, once it has stated
//! the positions asked. Its modes:
//!
//! - `agree`: as above;
//! - `differ K`: element `K` has 100 more in `acc`;
//! - `short M`: it stops after `M` elements, its channel open there;
//! - `ends-early M`: it ends after `M` elements, its channel closed there;
//! - `runs-on`: it never ends: where the machine has ended it states the last state again;
//! - `unknown K`: element `K` is unknown (`undecided`);
//! - `fine`: every element is stated twice (a finer granularity, for `sign`);
//! - `bad-type` (a string for `n`), `bad-rule` (an element names a rule), `no-channel` (no
//!   channel at all): records that are none of the declaration.
//!
//! On `maps` an element is `seen` as an array of pairs with its values as `$int` forms, another
//! spelling of the value than the canonical object. A `/1` implementation in the same flow is
//! `kink_compare.rs`'s `fake.sh`, answering as the definition ends.

#![cfg(feature = "kink")]

use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const PACKAGE: &str = "krs-cli-kink-compare-trace";

const LIBRARY: &str = r##"use k::builtin::{Int, KSequence, Map, map};
use k::KItem;

k::sorts! {
    Op: KItem;
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    #[k::syntax("#count")]
    Count,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub n: Int,
    #[k::cell]
    pub acc: Int,
    #[k::cell]
    pub seen: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(n: Int) -> Self {
        Self {
            k: k::k![Step::Count],
            n,
            acc: 0,
            seen: map![1 -> n, 2 -> 0],
        }
    }
}

k::rules! {
    for Machine;

    #[k::requires(n > 0)]
    tick: {
        k: [Step::Count, ..],
        n,
        acc,
    } => {
        n: n - 1,
        acc: acc + n,
    };

    #[k::requires(n < 0)]
    spin: {
        k: [Step::Count, ..],
        n,
        acc,
    } => {
        acc: acc + 1,
    };

    #[k::requires(n == 0)]
    done: {
        k: [Step::Count, ..],
        n,
    } => {
        k: [..],
    };
}
"##;

/// The `/2` implementation (module documentation).
const FAKE2: &str = r#"#!/bin/sh
mode=$1
channel=$2
argument=$3
request=$(cat)
if [ -n "$4" ]; then printf '%s\n' "$request" >> "$4"; fi
n=$(printf '%s' "$request" | sed -n 's/.*"inputs":{"n":\(-\{0,1\}[0-9]*\)}.*/\1/p')
count=$(printf '%s' "$request" | sed -n 's/.*"stop":{"count":\([0-9]*\)}.*/\1/p')
positions=$(printf '%s' "$request" | sed -n 's/.*"positions":\([0-9]*\).*/\1/p')
start=$n
acc=0
ticks=0
steps=0
stated=0
kept=0
last=
elements=
end=
closed=null
open=null
emit() {
  case $channel in
    sign) value="{\"n\":$n}";;
    maps) value="{\"seen\":[[{\"\$int\":\"1\"},{\"\$int\":\"$start\"}],[2,0]]}";;
    *) shown=$acc
       if [ "$mode" = differ ] && [ "$stated" -eq "$argument" ]; then shown=$((acc + 100)); fi
       value="{\"n\":$n,\"acc\":$shown}"
       if [ "$mode" = bad-type ]; then value="{\"n\":\"many\",\"acc\":$shown}"; fi;;
  esac
  rule=null
  if [ "$mode" = bad-rule ]; then rule='"tick"'; fi
  held="\"value\":$value"
  if [ "$mode" = unknown ] && [ "$stated" -eq "$argument" ]; then held='"undecided":"the fake does not know"'; fi
  if [ -n "$elements" ]; then elements="$elements,"; fi
  elements="$elements{\"index\":$stated,\"depth\":$steps,\"rule\":$rule,\"side\":null,$held}"
  stated=$((stated + 1))
  if [ "$value" != "$last" ]; then kept=$((kept + 1)); last=$value; fi
}
# The positions stated so far, as the channel's stuttering mode counts them.
reached() {
  if [ "$channel" = sign ]; then echo "$kept"; else echo "$stated"; fi
}
while [ -z "$end" ]; do
  if [ "$mode" = short ] && [ "$stated" -ge "$argument" ]; then
    end=horizon; open="{\"index\":$stated,\"reason\":\"the fake stops here\"}"; break
  fi
  if [ "$mode" = ends-early ] && [ "$stated" -ge "$argument" ]; then end=final; closed='"end"'; break; fi
  if [ "$(reached)" -ge "$positions" ]; then
    end=horizon; open="{\"index\":$stated,\"reason\":\"the requested positions\"}"; break
  fi
  if [ "$n" -gt 0 ] && [ -n "$count" ] && [ "$ticks" -eq $((count - 1)) ]; then
    if [ "$mode" = runs-on ]; then emit; continue; fi
    end=stopped; closed='"end"'; break
  fi
  if [ "$n" -eq 0 ]; then
    if [ "$mode" = runs-on ]; then emit; continue; fi
    end=final; closed='"end"'; break
  fi
  if [ "$n" -gt 0 ]; then
    emit
    if [ "$mode" = fine ]; then emit; fi
    acc=$((acc + n)); n=$((n - 1)); ticks=$((ticks + 1))
  else
    if [ "$channel" != downs ]; then
      emit
      if [ "$mode" = fine ]; then emit; fi
    fi
    acc=$((acc + 1))
  fi
  steps=$((steps + 1))
done
channels="{\"name\":\"$channel\",\"kind\":\"point\",\"elements\":[$elements],\"closed\":$closed,\"open\":$open}"
if [ "$mode" = no-channel ]; then channels=; fi
observations="{\"schema\":\"krs-observations/1\",\"channels\":[$channels]}"
if [ "$end" = horizon ]; then
  printf '{"end":"horizon","observations":%s}\n' "$observations"
else
  printf '{"end":"%s","cells":{"n":%s,"acc":%s},"observations":%s}\n' "$end" "$n" "$acc" "$observations"
fi
"#;

/// `kink_compare.rs`'s `/1` implementation, answering as the definition ends, each request
/// appended to its second argument.
const FAKE1: &str = r#"#!/bin/sh
request=$(cat)
if [ -n "$2" ]; then printf '%s\n' "$request" >> "$2"; fi
n=$(printf '%s' "$request" | sed -n 's/.*"inputs":{"n":\(-\{0,1\}[0-9]*\)}.*/\1/p')
count=$(printf '%s' "$request" | sed -n 's/.*"stop":{"count":\([0-9]*\)}.*/\1/p')
acc=0
ticks=0
end=final
while [ "$n" -gt 0 ]; do
  if [ -n "$count" ] && [ "$ticks" -eq $((count - 1)) ]; then end=stopped; break; fi
  acc=$((acc + n)); n=$((n - 1)); ticks=$((ticks + 1))
done
printf '{"end":"%s","cells":{"n":%s,"acc":%s}}\n' "$end" "$n" "$acc"
"#;

/// One `/2` `[[implementation]]` `name` running `fake2.sh ARGUMENTS`, with one required trace
/// view over `channel`, named after it, and `more` (other keys of the declaration, each on a
/// line).
fn traced(name: &str, arguments: &[&str], channel: &str, more: &str) -> String {
    let command = ["sh", "fake2.sh"]
        .iter()
        .chain(arguments)
        .map(|word| format!("\"{word}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "[[implementation]]\nname = \"{name}\"\nprotocol = \"kink-implementation/2\"\ncommand = \
         [{command}]\ngiven = \"inputs\"\nomits = [\"k\", \"seen\"]\n{more}views = [{{ name = \
         \"{channel}\", channels = [\"{channel}\"], required = true }}]\n\n"
    )
}

/// The main corpus's implementations.
fn main_implementations() -> String {
    let mut text = String::new();
    // A required end view beside the required trace view, its requests recorded.
    text.push_str(
        "[[implementation]]\nname = \"agree\"\nprotocol = \"kink-implementation/2\"\ncommand = \
         [\"sh\", \"fake2.sh\", \"agree\", \"ticks\", \"-\", \"agree.log\"]\ngiven = \
         \"inputs\"\nomits = [\"k\", \"seen\"]\nviews = [{ name = \"whole\", required = true }, { \
         name = \"ticks\", channels = [\"ticks\"], required = true }]\n\n",
    );
    for (name, arguments, channel) in [
        ("differ", &["differ", "ticks", "1"][..], "ticks"),
        ("short", &["short", "ticks", "1"], "ticks"),
        ("ends-early", &["ends-early", "ticks", "1"], "ticks"),
        ("runs-on", &["runs-on", "ticks"], "ticks"),
        ("unknown", &["unknown", "ticks", "1"], "ticks"),
        ("bad-type", &["bad-type", "ticks"], "ticks"),
        ("bad-rule", &["bad-rule", "ticks"], "ticks"),
        ("no-channel", &["no-channel", "ticks"], "ticks"),
        ("fine", &["fine", "sign"], "sign"),
        ("maps", &["agree", "maps"], "maps"),
        ("downs", &["agree", "downs"], "downs"),
    ] {
        text.push_str(&traced(name, arguments, channel, ""));
    }
    // A `/1` implementation in the same flow, its requests recorded.
    text.push_str(
        "[[implementation]]\nname = \"v1\"\ncommand = [\"sh\", \"fake1.sh\", \"equal\", \
         \"v1.log\"]\ngiven = \"inputs\"\nomits = [\"k\", \"seen\"]\nviews = [{ name = \"whole\", \
         required = true }]\n\n",
    );
    text
}

/// The package with its corpora, and the fixture target `krs` builds in.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

const CASES: [(&str, i64); 4] = [("a", 2), ("b", 5), ("s", -1), ("z", 0)];

impl Package {
    fn new() -> Self {
        Self::with_library(LIBRARY)
    }

    /// The package whose definition is `library`.
    fn with_library(library: &str) -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let package = Self {
            directory,
            target: shared_fixture_target(),
        };
        package.write("src/lib.rs", library);
        package.write(
            "Cargo.toml",
            &format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"TRACE\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        );
        package
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.directory.path().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, relative: &str) -> String {
        fs::read_to_string(self.directory.path().join(relative))
            .unwrap_or_else(|error| panic!("{relative}: {error}"))
    }

    /// A corpus at `corpus` with `implementations` and one case document per `(name, n)`. The
    /// clock never decides a run of the definition; the depth bound cuts one after six steps.
    fn corpus(&self, corpus: &str, implementations: &str, cases: &[(&str, i64)]) {
        self.write(
            &format!("{corpus}/FLOW.toml"),
            &format!(
                "[spec]\nkrs = {{ package = \"{PACKAGE}\", definition = \"main\" }}\n\n[budget]\ntime_ms = 600000\nmax_depth = 6\n\n\
                 [stop]\nbefore = [\"crate::tick\"]\ncount = 3\n\n\
                 [[observe.point]]\nname = \"ticks\"\nbefore = [\"crate::tick\", \"crate::spin\"]\nstutter = \"count\"\ncells = [\"n\", \"acc\"]\n\n\
                 [[observe.point]]\nname = \"downs\"\nbefore = [\"crate::tick\"]\nstutter = \"count\"\ncells = [\"n\", \"acc\"]\n\n\
                 [[observe.point]]\nname = \"sign\"\nbefore = [\"crate::tick\", \"crate::spin\"]\nstutter = \"collapse\"\ncells = [\"n\"]\n\n\
                 [[observe.point]]\nname = \"maps\"\nbefore = [\"crate::tick\", \"crate::spin\"]\nstutter = \"count\"\ncells = [\"seen\"]\n\n\
                 [[program]]\ncases = \"cases/*/case.toml\"\n\n{implementations}"
            ),
        );
        self.write(&format!("{corpus}/fake2.sh"), FAKE2);
        self.write(&format!("{corpus}/fake1.sh"), FAKE1);
        for (name, n) in cases {
            self.write(
                &format!("{corpus}/cases/{name}/case.toml"),
                &format!("[inputs]\nn = {n}\n"),
            );
        }
    }

    /// `krs kink compare ARGUMENTS` on the corpus `corpus`.
    fn compare(&self, corpus: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", "compare"])
            .args(arguments)
            .args(["--package", PACKAGE, "--definition", "main"]);
        if corpus != "kink" {
            process.args(["--corpus", corpus]);
        }
        process.output().unwrap()
    }
}

fn json_of(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[track_caller]
fn assert_status(output: &Output, code: i32) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The program of the case `name`.
fn program(name: &str) -> String {
    format!("cases/{name}/case.toml")
}

/// The row of `implementation` on the case `case`.
fn row<'d>(document: &'d Value, implementation: &str, case: &str) -> &'d Value {
    let program = program(case);
    document["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("{document:#}"))
        .iter()
        .find(|row| row["implementation"] == implementation && row["program"] == program)
        .unwrap_or_else(|| panic!("no row of {implementation} on {program}: {document:#}"))
}

/// The verdict of `view` in `row`.
fn verdict<'r>(row: &'r Value, view: &str) -> &'r Value {
    row["views"]
        .as_array()
        .unwrap_or_else(|| panic!("{row:#}"))
        .iter()
        .find(|entry| entry["view"] == view)
        .unwrap_or_else(|| panic!("no view {view}: {row:#}"))
}

/// The verdict of the one trace view of `implementation` (named `channel`) on `case`.
fn traced_verdict<'d>(
    document: &'d Value,
    implementation: &str,
    case: &str,
    channel: &str,
) -> &'d Value {
    let row = row(document, implementation, case);
    assert_eq!(row["failure"], Value::Null, "{row:#}");
    verdict(row, channel)
}

/// The `--only` arguments that select `names`.
fn only<'a>(names: &[&'a str]) -> Vec<&'a str> {
    names.iter().flat_map(|name| ["--only", name]).collect()
}

/// The requests the log `name` of `corpus` holds, one per run of its implementation.
fn requests(package: &Package, corpus: &str, name: &str) -> Vec<String> {
    fs::read_to_string(package.directory.path().join(corpus).join(name))
        .map(|log| log.lines().map(str::to_owned).collect())
        .unwrap_or_default()
}

/// The request `log` holds for the case `case`.
fn request_of(log: &[String], case: &str) -> Value {
    log.iter()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .find(|request| request["program"] == program(case))
        .unwrap_or_else(|| panic!("no request for {case}: {log:#?}"))
}

/// An implementation that states every position the definition does: `equal` exactly where both
/// sides close, `agree-up-to` the definition's horizon where its run is cut, never `equal`
/// there; and what the request asks.
fn assert_agreement(package: &Package, document: &Value) {
    // Both sides close: after two elements on `a` and `b` (the stop-before arrival of the third
    // `tick` on `b` is no element), after none on `z`.
    for case in ["a", "b", "z"] {
        let ticks = traced_verdict(document, "agree", case, "ticks");
        assert_eq!(ticks["verdict"], "equal", "{ticks:#}");
        assert_eq!(ticks["horizon"], Value::Null, "{ticks:#}");
        assert_eq!(ticks["correspondence"], "implementation-claim");
        let whole = verdict(row(document, "agree", case), "whole");
        assert_eq!(whole["verdict"], "equal", "{whole:#}");
        assert!(whole.get("correspondence").is_none(), "{whole:#}");
    }
    assert_eq!(row(document, "agree", "a")["answer"]["end"], "final");
    assert_eq!(row(document, "agree", "b")["answer"]["end"], "stopped");

    // The run that never ends: six elements agree, then the definition's run is cut.
    let spin = row(document, "agree", "s");
    assert_eq!(spin["answer"]["end"], "horizon", "{spin:#}");
    let ticks = verdict(spin, "ticks");
    assert_eq!(ticks["verdict"], "agree-up-to", "{ticks:#}");
    assert_eq!(
        ticks["horizon"],
        json!({"ticks": {"elements": 6, "limited_by": "definition", "definition": "bound",
                         "implementation": "the requested positions"}}),
        "{ticks:#}"
    );
    assert_eq!(ticks["status"], 0, "{ticks:#}");
    // Its end view has no end to compare; the required trace view carries the requirement.
    let whole = verdict(spin, "whole");
    assert_eq!(whole["verdict"], "not-compared", "{whole:#}");
    assert_eq!(whole["reason"], "no-end", "{whole:#}");
    assert_eq!(whole["status"], 0, "{whole:#}");

    // The request: the channel in the declaration's vocabulary, and the positions to state.
    let log = requests(package, "kink", "agree.log");
    let request = request_of(&log, "s");
    assert_eq!(request["protocol"], "kink-implementation/2");
    assert_eq!(
        request["observe"],
        json!({"channels": [{
            "name": "ticks", "kind": "point", "stutter": "count", "filtered": false,
            "components": [{"name": "n", "type": "Int"}, {"name": "acc", "type": "Int"}],
            // The rules as the manifest holds them: the names as written, sorted.
            "points": {"before": ["crate::spin", "crate::tick"], "after": []},
            "positions": 6,
        }]}),
        "{request:#}"
    );
    // A closed channel asks for one position more than its elements: the closure's. `b` ends
    // at the stop, before its third `tick`: that arrival is no step taken, so it is no element,
    // and the channel holds the two elements read before the two steps taken.
    for (case, positions) in [("a", 3), ("b", 3), ("z", 1)] {
        assert_eq!(
            request_of(&log, case)["observe"]["channels"][0]["positions"],
            positions,
            "{case}"
        );
    }
}

/// The first difference of a trace view: the place, and each side there.
fn assert_differences(document: &Value) {
    // A differing value: the definition's element with its rule, its side and its steps.
    let differ = traced_verdict(document, "differ", "a", "ticks");
    assert_eq!(differ["verdict"], "different", "{differ:#}");
    assert_eq!(
        differ["difference"],
        json!({
            "format": "kink-trace/1", "channel": "ticks", "kind": "value", "index": 1,
            "path": "acc",
            "definition": {"element": {"n": 1, "acc": 2}, "rule": "crate::tick",
                           "side": "before", "steps": 1},
            "implementation": {"element": {"n": 1, "acc": 102}, "count": 1},
            "correspondence": "implementation-claim",
        }),
        "{differ:#}"
    );
    let spin = &traced_verdict(document, "differ", "s", "ticks")["difference"];
    assert_eq!(spin["definition"]["rule"], "crate::spin", "{spin:#}");
    assert_eq!(spin["definition"]["steps"], 1, "{spin:#}");
    // No element, nothing to differ at.
    assert_eq!(
        traced_verdict(document, "differ", "z", "ticks")["verdict"],
        "equal"
    );

    // The implementation ends where the definition goes on.
    let early = traced_verdict(document, "ends-early", "a", "ticks");
    assert_eq!(early["verdict"], "different", "{early:#}");
    assert_eq!(early["difference"]["kind"], "closure", "{early:#}");
    assert_eq!(early["difference"]["index"], 1, "{early:#}");
    assert_eq!(
        early["difference"]["implementation"],
        json!({"closed": "end", "count": null}),
        "{early:#}"
    );
    assert_eq!(
        early["difference"]["definition"]["element"],
        json!({"n": 1, "acc": 2})
    );
    assert_eq!(
        traced_verdict(document, "ends-early", "s", "ticks")["verdict"],
        "different"
    );

    // The definition ends where the implementation goes on.
    let on = traced_verdict(document, "runs-on", "a", "ticks");
    assert_eq!(on["verdict"], "different", "{on:#}");
    assert_eq!(on["difference"]["kind"], "closure", "{on:#}");
    assert_eq!(on["difference"]["index"], 2, "{on:#}");
    assert_eq!(
        on["difference"]["definition"],
        json!({"closed": "end", "rule": null, "side": null, "steps": null}),
        "{on:#}"
    );
    assert_eq!(
        on["difference"]["implementation"],
        json!({"element": {"n": 0, "acc": 3}, "count": 2}),
        "{on:#}"
    );
    // Neither side ends: nothing tells them apart up to the horizon.
    assert_eq!(
        traced_verdict(document, "runs-on", "s", "ticks")["verdict"],
        "agree-up-to"
    );
}

/// An answer that leaves positions unstated, an unknown element, and a channel nothing was
/// observed on: none passes a required view.
fn assert_unanswered(document: &Value) {
    // One element where the definition states two and its closure.
    let short = traced_verdict(document, "short", "a", "ticks");
    assert_eq!(short["verdict"], "agree-up-to", "{short:#}");
    assert_eq!(
        short["horizon"],
        json!({"ticks": {"elements": 1, "limited_by": "implementation", "definition": null,
                         "implementation": "the fake stops here"}}),
        "{short:#}"
    );
    assert_eq!(short["status"], 3, "{short:#}");
    // On the run that never ends, too: the definition states five positions more.
    let spin = traced_verdict(document, "short", "s", "ticks");
    assert_eq!(
        spin["horizon"]["ticks"]["limited_by"], "implementation",
        "{spin:#}"
    );

    let unknown = traced_verdict(document, "unknown", "a", "ticks");
    assert_eq!(unknown["verdict"], "not-compared", "{unknown:#}");
    assert_eq!(unknown["reason"], "undecided", "{unknown:#}");
    let detail = unknown["detail"].as_str().unwrap();
    assert!(
        detail.contains("`ticks` element 1")
            && detail.contains("the implementation's element is not decided")
            && detail.contains("the fake does not know"),
        "{detail}"
    );

    // `downs` holds no element of a run that only spins, and is open at the bound: nothing was
    // compared. On a run that ticks it is compared as any channel.
    let nothing = traced_verdict(document, "downs", "s", "downs");
    assert_eq!(nothing["verdict"], "not-compared", "{nothing:#}");
    assert_eq!(nothing["reason"], "observed-nothing", "{nothing:#}");
    assert_eq!(
        traced_verdict(document, "downs", "a", "downs")["verdict"],
        "equal"
    );
}

/// A record that is none of the declaration fails the run: `malformed`, and no verdict.
fn assert_malformed(document: &Value) {
    for (name, case, named) in [
        ("bad-type", "a", "channels[0].elements[0].value.n"),
        ("bad-rule", "a", "channels[0].elements[0].rule"),
        ("no-channel", "a", "ticks"),
        // No element, so nothing of `bad-type`'s record is of another type.
        ("no-channel", "z", "ticks"),
    ] {
        let row = row(document, name, case);
        assert_eq!(row["failure"]["kind"], "malformed", "{name}: {row:#}");
        assert_eq!(row["views"], json!([]), "{name}: {row:#}");
        let detail = row["failure"]["detail"].as_str().unwrap();
        assert!(
            detail.contains("observations") && detail.contains(named),
            "{name}: {detail}"
        );
    }
}

/// Equal values are equal elements whatever document states them, and a `collapse` channel is
/// compared as collapsed whatever granularity the implementation states it at.
fn assert_values(document: &Value) {
    // `seen` as pairs with `$int` forms, against the definition's canonical object.
    for case in ["a", "b", "z"] {
        assert_eq!(
            traced_verdict(document, "maps", case, "maps")["verdict"],
            "equal",
            "{case}"
        );
    }
    let maps = traced_verdict(document, "maps", "s", "maps");
    assert_eq!(maps["verdict"], "agree-up-to", "{maps:#}");
    assert_eq!(maps["horizon"]["maps"]["elements"], 6, "{maps:#}");

    // Every element stated twice: the same channel once collapsed.
    for case in ["a", "b", "z"] {
        assert_eq!(
            traced_verdict(document, "fine", case, "sign")["verdict"],
            "equal",
            "{case}"
        );
    }
    // `n` never changes on the run that never ends: one element, then the bound.
    let sign = traced_verdict(document, "fine", "s", "sign");
    assert_eq!(sign["verdict"], "agree-up-to", "{sign:#}");
    assert_eq!(
        sign["horizon"]["sign"],
        json!({"elements": 1, "limited_by": "definition", "definition": "bound",
               "implementation": "the requested positions"}),
        "{sign:#}"
    );
}

/// A `/1` implementation in a flow with `/2` ones: its request and its rows are `/1`'s.
fn assert_v1(package: &Package, document: &Value) {
    let log = requests(package, "kink", "v1.log");
    // No request on the program with no end.
    assert_eq!(log.len(), 3, "{log:#?}");
    assert!(
        log.contains(
            &r#"{"inputs":{"n":5},"program":"cases/b/case.toml","protocol":"kink-implementation/1","stop":{"count":3}}"#
                .to_owned()
        ),
        "{log:#?}"
    );
    for case in ["a", "b", "z"] {
        let row = row(document, "v1", case);
        assert_eq!(
            row["views"],
            json!([{"view": "whole", "required": true, "verdict": "equal", "difference": null,
                    "reason": null, "detail": null, "omitted": ["k", "seen"], "status": null}]),
            "{row:#}"
        );
    }
    let spin = verdict(row(document, "v1", "s"), "whole");
    assert_eq!(spin["verdict"], "not-compared", "{spin:#}");
    assert_eq!(spin["reason"], "definition", "{spin:#}");
}

/// Every trace verdict, on one corpus, and the exit policy.
#[test]
fn a_trace_view_compares_the_channels_up_to_the_horizon() {
    let package = Package::new();
    package.corpus("kink", &main_implementations(), &CASES);
    let output = package.compare("kink", &[]);
    // The malformed records fail runs with a required view: the question is unasked.
    assert_status(&output, 2);
    let document = json_of(&output);
    assert_eq!(document["schema"], "kink-flow-compare", "{document:#}");
    assert_eq!(document["evidence"], "testing", "{document:#}");
    assert_eq!(
        document["protocols"],
        json!(["kink-implementation/1", "kink-implementation/2"]),
        "{document:#}"
    );
    let classes = document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|program| program["class"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        classes,
        [
            "comparable",
            "comparable",
            "comparable-prefix",
            "comparable"
        ],
        "{document:#}"
    );

    assert_agreement(&package, &document);
    assert_differences(&document);
    assert_unanswered(&document);
    assert_malformed(&document);
    assert_values(&document);
    assert_v1(&package, &document);

    // The status: agreement up to the definition's horizon passes a required view; a
    // difference is a finding; positions left unstated, an unknown element and a channel
    // nothing was observed on leave the question open.
    assert_status(
        &package.compare("kink", &only(&["agree", "maps", "fine"])),
        0,
    );
    assert_status(&package.compare("kink", &only(&["differ"])), 1);
    assert_status(&package.compare("kink", &only(&["ends-early"])), 1);
    assert_status(&package.compare("kink", &only(&["runs-on"])), 1);
    assert_status(&package.compare("kink", &only(&["short"])), 3);
    assert_status(&package.compare("kink", &only(&["unknown"])), 3);
    assert_status(&package.compare("kink", &only(&["downs"])), 3);

    // One line per verdict: the difference names the definition's rule and step count and the
    // place inside the value; a horizon is never spelled `equal`.
    let text = package.compare(
        "kink",
        &[&only(&["agree", "differ"])[..], &["--output", "text"]].concat(),
    );
    assert_status(&text, 1);
    let text = String::from_utf8(text.stdout).unwrap();
    let testing = "(testing: that element k is the definition's point k is";
    assert!(
        text.contains(&format!(
            "differ cases/a/case.toml ticks (required): different at `ticks` element 1 at `acc`: \
             definition {{\"acc\":2,\"n\":1}} (before `crate::tick`, after 1 steps); implementation \
             {{\"acc\":102,\"n\":1}} (its element 1, its count 1) {testing} differ's claim)"
        )),
        "{text}"
    );
    assert!(
        text.contains(&format!(
            "agree cases/s/case.toml ticks (required): agree-up-to: `ticks` 6 elements agree, \
             then the definition's run is cut (bound); nothing past it is compared {testing} \
             agree's claim)"
        )),
        "{text}"
    );
    assert!(
        !text.contains("agree cases/s/case.toml ticks (required): equal"),
        "{text}"
    );
}

/// A trace view under `/1` is refused before any run: a trace view is never run as an end view.
#[test]
fn a_trace_view_is_never_run_under_the_first_protocol() {
    let package = Package::new();
    package.corpus(
        "corpora/v1-trace",
        "[[implementation]]\nname = \"x\"\ncommand = [\"sh\", \"fake1.sh\", \"equal\", \
         \"x.log\"]\ngiven = \"inputs\"\nomits = [\"k\", \"seen\"]\nviews = [{ name = \"ticks\", \
         channels = [\"ticks\"], required = true }]\n",
        &[("a", 2)],
    );
    let output = package.compare("corpora/v1-trace", &[]);
    assert_status(&output, 2);
    let refusal = &json_of(&output)["refusal"];
    assert_eq!(refusal["stage"], "implementation", "{refusal:#}");
    assert_eq!(refusal["reason"], "declaration", "{refusal:#}");
    assert!(requests(&package, "corpora/v1-trace", "x.log").is_empty());
}

/// A trace view over a channel a component of which has no value with a document: no
/// implementation can state an element of it, so the declaration is refused before any run,
/// naming the channel and the component.
#[test]
fn a_channel_no_implementation_can_state_is_refused() {
    // `Ghost` has no constructor, so no document is a value of it, and `ghosts` holds a list of
    // them.
    let library = LIBRARY
        .replace(
            "use k::builtin::{Int, KSequence, Map, map};",
            "use k::builtin::{Int, KSequence, List, Map, map};",
        )
        .replace("    Op: KItem;\n", "    Op: KItem;\n    Ghost;\n")
        .replace(
            "    pub seen: Map<Int, Int>,\n",
            "    pub seen: Map<Int, Int>,\n    #[k::cell]\n    pub ghosts: List<Ghost>,\n",
        )
        .replace(
            "            seen: map![1 -> n, 2 -> 0],\n",
            "            seen: map![1 -> n, 2 -> 0],\n            ghosts: [],\n",
        );
    assert!(library.contains("ghosts: []") && library.contains("    Ghost;"));
    let package = Package::with_library(&library);
    let corpus = "corpora/no-document";
    package.corpus(
        corpus,
        &traced("x", &["agree", "ghosts", "-", "x.log"], "ghosts", ""),
        &[("a", 2)],
    );
    let flow = format!("{corpus}/FLOW.toml");
    package.write(
        &flow,
        &package.read(&flow).replace(
            "[[program]]",
            "[[observe.point]]\nname = \"ghosts\"\nbefore = [\"crate::tick\"]\nstutter = \
             \"count\"\ncells = [\"ghosts\"]\n\n[[program]]",
        ),
    );
    let output = package.compare(corpus, &[]);
    assert_status(&output, 2);
    let refusal = &json_of(&output)["refusal"];
    assert_eq!(refusal["stage"], "implementation", "{refusal:#}");
    assert_eq!(refusal["reason"], "declaration", "{refusal:#}");
    let detail = refusal["detail"].as_str().unwrap();
    assert!(
        detail.contains("views[0].channels")
            && detail.contains("the component `ghosts` of the channel `ghosts`")
            && detail.contains("`Ghost`"),
        "{detail}"
    );
    assert!(requests(&package, corpus, "x.log").is_empty());
}

/// The trace verdicts are rows of the corpus record's `[compare]` section, version 29, each
/// horizon with its row; an implementation with `identity` is answered from the cache with the
/// same verdict; and a horizon that moved makes `--locked` find the record stale.
#[test]
fn a_horizon_is_recorded_and_a_moved_one_is_stale() {
    let package = Package::new();
    let corpus = "corpora/record";
    package.corpus(
        corpus,
        &traced(
            "named",
            &["agree", "ticks", "-", "named.log"],
            "ticks",
            "identity = { file = \"fake2.sh\" }\n",
        ),
        &[("a", 2), ("s", -1)],
    );
    let record = package.directory.path().join(corpus).join("kink.lock");

    let first = package.compare(corpus, &[]);
    assert_status(&first, 0);
    let first = json_of(&first);
    assert_eq!(first["lock"]["status"], "created", "{first:#}");
    let written = fs::read_to_string(&record).unwrap();
    let section = &written[written.find("[compare]\n").expect("a compare section")..];
    assert!(section.contains("\nversion = 29\n"), "{section}");
    assert!(
        section.contains("protocols = [\"kink-implementation/2\"]\n"),
        "{section}"
    );
    let request = |document: &Value, case: &str| {
        row(document, "named", case)["request_sha256"]
            .as_str()
            .unwrap()
            .to_owned()
    };
    assert!(
        section.contains(&format!(
            "implementation = \"named\"\nprogram = \"cases/s/case.toml\"\nview = \
             \"ticks\"\nrequired = true\nverdict = \"agree-up-to\"\nhorizon = \
             '{{\"ticks\":{{\"definition\":\"bound\",\"elements\":6,\"implementation\":\"the \
             requested positions\",\"limited_by\":\"definition\"}}}}'\nrequest_sha256 = \"{}\"\n",
            request(&first, "s")
        )),
        "{section}"
    );
    assert!(
        section.contains(&format!(
            "implementation = \"named\"\nprogram = \"cases/a/case.toml\"\nview = \
             \"ticks\"\nrequired = true\nverdict = \"equal\"\nrequest_sha256 = \"{}\"\n",
            request(&first, "a")
        )),
        "{section}"
    );
    assert_eq!(requests(&package, corpus, "named.log").len(), 2);

    // A second run: answered from the cache, the same verdicts, the record current.
    let second = package.compare(corpus, &["--locked"]);
    assert_status(&second, 0);
    let second = json_of(&second);
    assert_eq!(second["lock"]["status"], "unchanged", "{second:#}");
    assert_eq!(requests(&package, corpus, "named.log").len(), 2);
    for case in ["a", "s"] {
        let (ran, cached) = (row(&first, "named", case), row(&second, "named", case));
        assert_eq!(ran["cached"], false, "{ran:#}");
        assert_eq!(cached["cached"], true, "{cached:#}");
        assert_eq!(ran["views"], cached["views"], "{case}");
    }
    assert_eq!(fs::read_to_string(&record).unwrap(), written);

    // The implementation now stops after three elements: the same word on `s`, another
    // horizon. `--locked` finds the record stale and writes nothing.
    let flow = format!("{corpus}/FLOW.toml");
    package.write(
        &flow,
        &package
            .read(&flow)
            .replace("\"agree\", \"ticks\", \"-\"", "\"short\", \"ticks\", \"3\""),
    );
    let moved = package.compare(corpus, &["--locked"]);
    assert_status(&moved, 1);
    let document = json_of(&moved);
    assert_eq!(document["lock"]["status"], "stale", "{document:#}");
    let ticks = traced_verdict(&document, "named", "s", "ticks");
    assert_eq!(ticks["verdict"], "agree-up-to", "{ticks:#}");
    assert_eq!(ticks["horizon"]["ticks"]["elements"], 3, "{ticks:#}");
    assert_eq!(
        ticks["horizon"]["ticks"]["limited_by"], "implementation",
        "{ticks:#}"
    );
    let stderr = String::from_utf8_lossy(&moved.stderr);
    assert!(
        stderr.contains("named cases/s/case.toml ticks: agree-up-to: its horizon moved"),
        "{stderr}"
    );
    assert_eq!(fs::read_to_string(&record).unwrap(), written);
}

/// The entries of the definition trace cache of `corpus`: each file's name, bytes and time of
/// last write. An entry is published by a rename, so one a command wrote again has another time.
fn definition_traces(
    package: &Package,
    corpus: &str,
) -> Vec<(String, Vec<u8>, std::time::SystemTime)> {
    let directory = package
        .directory
        .path()
        .join(corpus)
        .join(".kink-flow/definition-traces");
    let mut entries = fs::read_dir(&directory)
        .map(|entries| {
            entries
                .map(|entry| {
                    let entry = entry.unwrap();
                    (
                        entry.file_name().into_string().unwrap(),
                        fs::read(entry.path()).unwrap(),
                        entry.metadata().unwrap().modified().unwrap(),
                    )
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    entries.sort();
    entries
}

/// The definition's values of a program's channels are kept in the cache directory: a second
/// `compare` reads them and writes none (so it made no value run), and its document, status and
/// record are those of a command that computes them; a damaged entry is computed again and
/// written again; another `[stop]`, `[observe]` or channel set reads no entry of the first.
#[test]
fn the_definitions_values_are_read_from_the_cache() {
    let package = Package::new();
    let corpus = "corpora/values";
    let named = |mode: &str, channel: &str| {
        traced(
            "named",
            &[mode, channel, "-", "named.log"],
            channel,
            "identity = { file = \"fake2.sh\" }\n",
        )
    };
    let cases = [("a", 2), ("s", -1)];
    package.corpus(corpus, &named("agree", "ticks"), &cases);
    let record = package.directory.path().join(corpus).join("kink.lock");
    let traces = package
        .directory
        .path()
        .join(corpus)
        .join(".kink-flow/definition-traces");

    // Cold: one value run per program, each stored.
    let cold = package.compare(corpus, &[]);
    assert_status(&cold, 0);
    let cold = json_of(&cold);
    assert_eq!(cold["lock"]["status"], "created", "{cold:#}");
    let written = fs::read_to_string(&record).unwrap();
    let stored = definition_traces(&package, corpus);
    assert_eq!(stored.len(), 2, "{stored:?}");

    // Warm: no entry is written again, and the verdicts are the cold run's.
    let warm = package.compare(corpus, &["--locked"]);
    assert_status(&warm, 0);
    assert_eq!(definition_traces(&package, corpus), stored);
    let warm_document = json_of(&warm);
    for (case, _) in cases {
        assert_eq!(
            row(&cold, "named", case)["views"],
            row(&warm_document, "named", case)["views"],
            "{case}"
        );
    }

    // The same command with the values computed (no entry) and with one entry damaged: the
    // output byte for byte, the record, and the entries as they were first written.
    let name_and_bytes = |entries: &[(String, Vec<u8>, std::time::SystemTime)]| {
        entries
            .iter()
            .map(|(name, bytes, _)| (name.clone(), bytes.clone()))
            .collect::<Vec<_>>()
    };
    fs::remove_dir_all(&traces).unwrap();
    let computed = package.compare(corpus, &["--locked"]);
    assert_status(&computed, 0);
    assert_eq!(
        String::from_utf8_lossy(&computed.stdout),
        String::from_utf8_lossy(&warm.stdout)
    );
    assert_eq!(computed.stderr, warm.stderr);
    let computed = definition_traces(&package, corpus);
    assert_eq!(name_and_bytes(&computed), name_and_bytes(&stored));
    let damaged = traces.join(&stored[0].0);
    fs::write(&damaged, &stored[0].1[..stored[0].1.len() / 2]).unwrap();
    let repaired = package.compare(corpus, &["--locked"]);
    assert_status(&repaired, 0);
    assert_eq!(
        String::from_utf8_lossy(&repaired.stdout),
        String::from_utf8_lossy(&warm.stdout)
    );
    let now = definition_traces(&package, corpus);
    assert_eq!(name_and_bytes(&now), name_and_bytes(&stored));
    // Only the damaged entry was written again.
    let rewritten = computed
        .iter()
        .zip(&now)
        .filter(|(before, after)| before.2 != after.2)
        .map(|(before, _)| before.0.clone())
        .collect::<Vec<_>>();
    assert_eq!(rewritten, [stored[0].0.clone()]);
    assert_eq!(fs::read_to_string(&record).unwrap(), written);
    // The implementation ran once per program, on the cold command only.
    assert_eq!(requests(&package, corpus, "named.log").len(), 2);

    // Another `[stop]`, another `[observe]` (a channel no view names) and another channel set:
    // each is another key for each program, so each command computes and stores two entries
    // more, and none of the entries before it is written again.
    let flow = format!("{corpus}/FLOW.toml");
    let edit = |from: &str, to: &str| {
        let text = package.read(&flow);
        assert!(text.contains(from), "{text}");
        package.write(&flow, &text.replace(from, to));
    };
    let mut held = now;
    let mut assert_missed = |what: &str| {
        assert_status(&package.compare(corpus, &[]), 0);
        let entries = definition_traces(&package, corpus);
        assert_eq!(entries.len(), held.len() + 2, "{what}: {entries:?}");
        for entry in &held {
            assert!(entries.contains(entry), "{what}: {} was written", entry.0);
        }
        held = entries;
    };
    edit("count = 3", "count = 2");
    assert_missed("[stop]");
    edit(
        "stutter = \"collapse\"\ncells = [\"n\"]",
        "stutter = \"count\"\ncells = [\"n\"]",
    );
    assert_missed("[observe]");
    // The first declaration again, with a view of another channel.
    package.corpus(corpus, &named("agree", "maps"), &cases);
    assert_missed("channels");
}
