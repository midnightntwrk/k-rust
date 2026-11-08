//! The verdicts of a `coverage` or `run` document as deterministic TOML (`--output verdicts`):
//! what the corpus and the specification decide, and nothing that depends on the host, the build,
//! the cache or the order the work was done in. It is the format of recorded outputs and, without
//! `killed_by`, of a corpus's `verdicts.lock` ([`lock_text`], [`crate::lock`]), which `run --lock`
//! writes, so that a change of a verdict shows in review and an unchanged corpus renders the same
//! bytes.
//!
//! ```toml
//! schema = "kink-flow-verdicts"
//! version = 9
//! document = "coverage"
//! profile = "z3"
//! z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
//! z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"
//! krs_annotation = 5
//!
//! [spec]
//! outcome = "admitted"
//!
//! [settings]
//! tiers = [1]
//! depth = 1
//! mcdc = []
//!
//! [rules]
//! open = ["rule:crate::plus_succ"]
//!
//! [requirements]
//! open = []
//!
//! [flips]
//! run = false
//! ```
//!
//! The header names the document and the build's solver `profile` (`no-z3` or `z3`): under Z3 a
//! class, a status and a cell can move between `killed`, `unknown` and `survived` with the solver's
//! answers, so a diff of two renderings across profiles shows why. Under the Z3 profile it also
//! names the Z3 build the answers came from (the document's `z3`): `z3_version`, Z3's own version
//! string, and `z3_library_sha256`, the SHA-256 of the library file Z3's code comes from (k-rust
//! `z3_build`; the archive of a static link, the shared library of a dynamic one). Whether a
//! resource-bounded query is decided is a function of the query, its units and the machine code
//! that counts them, so a kink build linking another Z3 can move a class, a status or a killer
//! with the same inputs and the same profile; the two lines are the profile's argument applied
//! to the build. The digest is the identity: two builds of one release (another compiler, other
//! flags, another architecture) can count units differently and report one version string, which
//! is there so that a reader sees which release moved. A build that cannot name its library (a
//! shared library replaced since it was mapped, a static link whose archive the build could not
//! name) has no `z3_library_sha256` line, the caches being off for it for the same reason
//! (kink-native `UNNAMED_Z3_BUILD`). The portable profile renders neither line. A `coverage`
//! document the KRS
//! front end annotated also has `krs_annotation`, the version of that annotation (the document's
//! `krs.version`), since an item's id spells its rule's KRS item as the annotation spells it: two
//! renderings of the same coverage under different annotation versions differ in that line and in
//! the ids, not in what is open. A run rendering names no rule, so it has no `krs_annotation`
//! line, which could only move a lock without any verdict moving.
//!
//! A `coverage` document gives its settings (the tiers computed, `depth`, `mcdc`), then per
//! family the ids of its open obligations, in item order (`[rules]`, `[requirements]`;
//! [`crate::coverage::open_ids`]), and for the flips family whether it ran. It lists no programs
//! and no counts, so that it moves only when a gap opens or closes: a case that covers nothing new
//! renders the same bytes. A `run` document
//! gives each mutation it judged (`[[mutation]]`, in list order) its status, a killed mutation's
//! `killer` (under both schedules), under `full` its `killed_by` too (every killing program in
//! corpus order), and, when a corpus error stopped it, the mutation and the reason under
//! `[stopped]` (the mutations after it have no status). A refused specification has its `stage`
//! and `reason` under `[spec]`, a refused mutation list its `outcome` under `[mutation_list]` (a
//! run document of a list that does not decode has no `[spec]`), and a refused lock its `outcome`
//! under `[lock]`, with no case or mutation. A mutation its author must fix before it is
//! judged, `invalid-mutation` or `not-admitted`, has its `reason` too, as a refused specification
//! has: the reason is a function of the specification and the mutation alone (the resolution,
//! the mutant's compile, its consistency, its stop), so it is the refusal's verdict, and a lock
//! shows which refusal moved. The refusals' texts are not rendered, since they explain a refusal
//! rather than record a verdict ([`refusal_details`] gives them, and `kink-flow` prints them on
//! stderr). `report --output verdicts` renders the stored run document,
//! so it prints what `run --output verdicts` printed; when there is no stored run document to
//! render, the reason is the error ([`verdicts`]).
//!
//! Left out, each because it is not a function of the specification, the corpus, the budget, the
//! killer record and the solver (the profile and, under Z3, its build, in the header): timings,
//! digests, kink's own build identity, the cache's state, the schedule, and the reason of any other status, since the reason
//! of `unknown` is the first exclusion in run order. A status does not depend on the order or the
//! cache while no `budget.time_ms` bound fires (README, the program order), and neither does a
//! full run's `killed_by`: it is the set of comparable programs whose cell is a proved difference,
//! each cell an outcome that does not depend on the other programs of the call, live or cached
//! under a key that names every input. A killer is the recorded one while it kills, else the
//! first killing program in the search's order, which is a function of the inputs (README, "The
//! killer record"): so a first-kill and a full rendering state the same facts apart from the
//! `killed_by` lines, and a full rendering of a run with no kill is the first-kill rendering. A
//! `timeout` class or status depends on the host by its nature.

use serde_json::Value;
use std::fmt::Write as _;

/// The `schema` of the rendering.
pub const VERDICTS_SCHEMA: &str = "kink-flow-verdicts";
/// The version of the rendering: 1, the first; 2 since CF-23 added the header's `schedule` (run
/// documents) and `profile`, and a full run's `killed_by`; 3 since a mutation's `status` names
/// the runner status version 2 rendered `invalid` `not-admitted` (run document version 18), so a
/// lock that moves from one name to the other shows a new version, not a moved verdict; 4 since
/// the header's `krs_annotation` names the front end's annotation version, which a rule's KRS
/// item is spelled by, so that a lock whose names move with the annotation shows why; 5 since an
/// `invalid-mutation` or `not-admitted` mutation has its `reason`; 6 since a killed mutation of a
/// run has its `killer` under both schedules (the recorded killer while it kills, else the first
/// in the search's order), the header no longer names the schedule, a run rendering no longer has
/// `krs_annotation`, and a refused lock has its `[lock]` section; 7 since a `results` rendering
/// lists each fired or matched rule whose guard misses an outcome (`[[guard]]`); 8 since the
/// header names the Z3 build under the Z3 profile (`z3_version`, `z3_library_sha256`), so that a
/// lock whose verdicts moved with the solver build says why, and one recorded on another build is
/// a finding under `--locked` ([`crate::lock`]); 9 since the `coverage` document replaces the
/// `results` document: its rendering (`document = "coverage"`) gives the settings and each
/// family's open obligations by id, and no case.
pub const VERDICTS_VERSION: u64 = 9;

/// The rendering of a `coverage` or `run` document (module documentation). The error names what
/// the document is when it is neither: for `report`'s document saying why there is no stored run
/// document (`kink-flow-report`), why there is none, so that `report --output verdicts` states
/// the reason where the rendering would have been.
pub fn verdicts(document: &Value) -> Result<String, String> {
    render(document, true)
}

/// The text of a `verdicts.lock` (`run --lock`, [`crate::lock`]): the rendering of a run document
/// without `killed_by`, so that a first-kill and a full run of the same inputs write the same
/// bytes, and for a first-kill run `run --output verdicts`, `report --output verdicts` and the lock
/// are the same bytes. The error names what the document is when it is not a run document.
pub fn lock_text(document: &Value) -> Result<String, String> {
    if document["schema"] != crate::report::RUN_SCHEMA {
        return Err("a lock is the rendering of a run document".to_owned());
    }
    render(document, false)
}

fn render(document: &Value, killed_by: bool) -> Result<String, String> {
    let kind = match document["schema"].as_str() {
        Some(crate::coverage::COVERAGE_SCHEMA) => "coverage",
        Some(crate::report::RUN_SCHEMA) => "run",
        Some(crate::report::MISSING_SCHEMA) => {
            return Err(match document["outcome"].as_str() {
                Some(outcome) => format!(
                    "{outcome} run report {}: {}",
                    document["path"].as_str().unwrap_or("?"),
                    document["detail"].as_str().unwrap_or("no detail")
                ),
                // The manifest, or what a front end needs before it, was refused.
                None => format!(
                    "no run report is read: {}",
                    refusal_details(document).join("; ")
                ),
            });
        }
        other => {
            return Err(format!(
                "--output verdicts renders a coverage or run document, not {}",
                other.map_or_else(|| "a document with no schema".to_owned(), str::to_owned)
            ));
        }
    };
    let mut text = String::new();
    line(&mut text, "schema", &string(VERDICTS_SCHEMA));
    line(&mut text, "version", &VERDICTS_VERSION.to_string());
    line(&mut text, "document", &string(kind));
    if let Some(value) = document["profile"].as_str() {
        line(&mut text, "profile", &string(value));
    }
    // The Z3 build, which a document has under the Z3 profile only (`crate::with_z3_build`); its
    // digest when the build could name its library.
    if let Some(version) = document["z3"]["version"].as_str() {
        line(&mut text, "z3_version", &string(version));
    }
    if let Some(digest) = document["z3"]["library_sha256"].as_str() {
        line(&mut text, "z3_library_sha256", &string(digest));
    }
    if kind == "coverage"
        && let Some(annotation) = document["krs"]["version"].as_u64()
    {
        line(&mut text, "krs_annotation", &annotation.to_string());
    }
    for section in ["spec", "mutation_list", "lock"] {
        let Some(object) = document[section].as_object() else {
            continue;
        };
        // A run's lock is rendered only when it was refused; otherwise it is the run's state,
        // not a verdict.
        if section == "lock" && object.get("outcome").and_then(Value::as_str) != Some("refused") {
            continue;
        }
        let _ = write!(text, "\n[{section}]\n");
        for key in ["outcome", "stage", "reason"] {
            if let Some(value) = object.get(key).and_then(Value::as_str) {
                line(&mut text, key, &string(value));
            }
        }
    }
    if kind == "coverage" {
        coverage(&mut text, document);
    } else {
        mutations(&mut text, document, killed_by);
    }
    if let Some(stopped) = document["stopped"].as_object() {
        text.push_str("\n[stopped]\n");
        for key in ["mutation", "reason"] {
            if let Some(value) = stopped.get(key).and_then(Value::as_str) {
                line(&mut text, key, &string(value));
            }
        }
    }
    Ok(text)
}

/// The texts of a document's refusals and of the stop of its run, which [`verdicts`] leaves out
/// (`spec`, `mutation_list`: `<section>: <stage or outcome> <reason>: <detail>`; a mutation its
/// author must fix: `mutation <id>: <status> <reason>: <detail>`, its `action` when it has no
/// `detail`; a stopped run: `stopped at
/// <mutation>: <reason>: <detail>`), for a front end to print beside the rendering (`kink-flow`
/// prints them on stderr).
#[must_use]
pub fn refusal_details(document: &Value) -> Vec<String> {
    let mut details = Vec::new();
    for section in ["spec", "mutation_list", "lock"] {
        let object = &document[section];
        if object["outcome"] != "refused" {
            continue;
        }
        let what = [&object["stage"], &object["reason"]]
            .into_iter()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join(" ");
        let what = if what.is_empty() {
            "refused".to_owned()
        } else {
            what
        };
        details.push(format!(
            "{section}: {what}: {}",
            object["detail"].as_str().unwrap_or("no detail")
        ));
    }
    for row in document["mutations"].as_array().into_iter().flatten() {
        if refused_mutation(row) {
            details.push(format!(
                "mutation {}: {} {}: {}",
                row["id"].as_str().unwrap_or("?"),
                row["status"].as_str().unwrap_or("?"),
                row["reason"].as_str().unwrap_or("?"),
                row["detail"]
                    .as_str()
                    .or_else(|| row["action"].as_str())
                    .unwrap_or("no detail")
            ));
        }
    }
    if let Some(stopped) = document["stopped"].as_object() {
        let mutation = stopped.get("mutation").and_then(Value::as_str);
        let row = document["mutations"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|row| mutation.is_some_and(|id| row["id"] == id));
        details.push(format!(
            "stopped at {}: {}: {}",
            mutation.unwrap_or("?"),
            stopped.get("reason").and_then(Value::as_str).unwrap_or("?"),
            row.and_then(|row| row["detail"].as_str())
                .unwrap_or("no detail")
        ));
    }
    details
}

/// A coverage document's settings, each family's open ids and whether the flips ran (module
/// documentation); nothing for a refused specification, which has no families.
fn coverage(text: &mut String, document: &Value) {
    let settings = &document["settings"];
    if settings.is_object() {
        text.push_str("\n[settings]\n");
        let numbers = |value: &Value| {
            let items = value
                .as_array()
                .into_iter()
                .flatten()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            format!("[{}]", items.join(", "))
        };
        line(text, "tiers", &numbers(&settings["tiers"]));
        line(text, "depth", &settings["depth"].to_string());
        let mcdc = settings["mcdc"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect::<Vec<_>>();
        line(text, "mcdc", &strings(&mcdc));
    }
    if !document["families"].is_object() {
        return;
    }
    for (family, open) in crate::coverage::open_ids(document) {
        let _ = write!(text, "\n[{family}]\n");
        line(text, "open", &strings(&open));
    }
    let flips = &document["families"]["flips"];
    if flips.is_object() {
        text.push_str("\n[flips]\n");
        line(
            text,
            "run",
            &flips["run"].as_bool().unwrap_or(false).to_string(),
        );
    }
}

/// Whether a run document's row is of a mutation its author must fix before it is judged:
/// `invalid-mutation` or `not-admitted` ([`crate::cli::invalid_mutations`]).
fn refused_mutation(row: &Value) -> bool {
    matches!(
        row["status"].as_str(),
        Some(crate::search::INVALID_MUTATION | "not-admitted")
    )
}

/// The reason a rendering writes for a run document's row: the reason of a mutation its author
/// must fix ([`refused_mutation`]), else none (module documentation).
#[must_use]
pub fn rendered_reason(row: &Value) -> Value {
    if refused_mutation(row) {
        row["reason"].clone()
    } else {
        Value::Null
    }
}

/// Each mutation's id and status, the reason of one its author must fix ([`refused_mutation`]),
/// a killed mutation's `killer`, and with `killed_by` a full row's `killed_by` (module
/// documentation).
fn mutations(text: &mut String, document: &Value, killed_by: bool) {
    for row in document["mutations"].as_array().into_iter().flatten() {
        text.push_str("\n[[mutation]]\n");
        line(text, "id", &string(row["id"].as_str().unwrap_or_default()));
        line(
            text,
            "status",
            &string(row["status"].as_str().unwrap_or_default()),
        );
        if let Some(reason) = rendered_reason(row).as_str() {
            line(text, "reason", &string(reason));
        }
        if row["status"] != "killed" {
            continue;
        }
        if let Some(killer) = row["killer"].as_str() {
            line(text, "killer", &string(killer));
        }
        if killed_by && let Some(killers) = row["killed_by"].as_array() {
            let killers = killers
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect::<Vec<_>>();
            line(text, "killed_by", &strings(&killers));
        }
    }
}

fn line(text: &mut String, key: &str, value: &str) {
    let _ = writeln!(text, "{key} = {value}");
}

/// A TOML basic string.
fn string(value: &str) -> String {
    toml::Value::String(value.to_owned()).to_string()
}

/// A TOML array of basic strings, on one line.
fn strings(values: &[String]) -> String {
    let items = values.iter().map(|value| string(value)).collect::<Vec<_>>();
    format!("[{}]", items.join(", "))
}
