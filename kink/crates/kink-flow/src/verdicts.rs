//! The verdicts of a `results` or `run` document as deterministic TOML (`--output verdicts`):
//! what the corpus and the specification decide, and nothing that depends on the host, the build,
//! the cache or the order the work was done in. It is meant as the format of a corpus's committed
//! `verdicts.lock` and of recorded outputs, so that a change of a verdict shows in review and an
//! unchanged corpus renders the same bytes.
//!
//! ```toml
//! schema = "kink-flow-verdicts"
//! version = 1
//! document = "results"
//!
//! [spec]
//! outcome = "admitted"
//!
//! [[case]]
//! id = "t1"
//! class = "comparable"
//! fired = ["plus_zero"]
//! matched = ["plus_zero"]
//! ```
//!
//! A `results` document gives each program (`[[case]]`, in manifest order) its class and the
//! rules its run fires (a rule's `fired_by`) and reaches (`reached_by`, k-rust `matched`), each
//! rule named by its KRS item when a front end annotated it (`krs.item`), else its label, else
//! its `file:line`, ordered by module name, then by position in the module. A `run` document
//! gives each mutation it judged (`[[mutation]]`, in list order) its status, and, when a corpus
//! error stopped it, the mutation and the reason under `[stopped]` (the mutations after it have
//! no status). A refused specification has its `stage` and `reason` under `[spec]`, and a refused
//! mutation list its `outcome` under `[mutation_list]` (a run document of a list that does not
//! decode has no `[spec]`), with no case or mutation; the refusal's text is not rendered, since
//! it explains a refusal rather than records a verdict ([`refusal_details`] gives it, and
//! `kink-flow` prints it on stderr).
//!
//! Left out, each because it is not a function of the specification, the corpus and the budget:
//! timings, digests, the build and the cache's state; the killer of a killed mutation, since
//! under the first-kill search it is the first killing program the search reached, which depends
//! on the order (`--order cost` reads wall times) and on the outcomes the cache already holds
//! (the killers become part of the rendering, under a new version, once a run proves every
//! killer of a mutation); and a status's reason, since the reason of `unknown` is the first
//! exclusion in run order. A status itself does not depend on the order or the cache in the
//! no-Z3 profile while no `budget.time_ms` bound fires (README, the program order). A `timeout`
//! class or status depends on the host by its nature.

use serde_json::Value;
use std::fmt::Write as _;

/// The `schema` of the rendering.
pub const VERDICTS_SCHEMA: &str = "kink-flow-verdicts";
/// The version of the rendering: 1, the first.
pub const VERDICTS_VERSION: u64 = 1;

/// The rendering of a `results` or `run` document (module documentation); the error names what
/// the document is when it is neither.
pub fn verdicts(document: &Value) -> Result<String, String> {
    let kind = match document["schema"].as_str() {
        Some("kink-flow-results") => "results",
        Some(crate::report::RUN_SCHEMA) => "run",
        other => {
            return Err(format!(
                "--output verdicts renders a results or run document, not {}",
                other.map_or_else(|| "a document with no schema".to_owned(), str::to_owned)
            ));
        }
    };
    let mut text = String::new();
    line(&mut text, "schema", &string(VERDICTS_SCHEMA));
    line(&mut text, "version", &VERDICTS_VERSION.to_string());
    line(&mut text, "document", &string(kind));
    for section in ["spec", "mutation_list"] {
        let Some(object) = document[section].as_object() else {
            continue;
        };
        let _ = write!(text, "\n[{section}]\n");
        for key in ["outcome", "stage", "reason"] {
            if let Some(value) = object.get(key).and_then(Value::as_str) {
                line(&mut text, key, &string(value));
            }
        }
    }
    if kind == "results" {
        cases(&mut text, document);
    } else {
        mutations(&mut text, document);
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
/// (`spec`, `mutation_list`: `<section>: <stage or outcome> <reason>: <detail>`; a stopped run:
/// `stopped at <mutation>: <reason>: <detail>`), for a front end to print beside the rendering
/// (`kink-flow` prints them on stderr).
#[must_use]
pub fn refusal_details(document: &Value) -> Vec<String> {
    let mut details = Vec::new();
    for section in ["spec", "mutation_list"] {
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

fn cases(text: &mut String, document: &Value) {
    let mut rules = document["rules"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or_default()
        .iter()
        .collect::<Vec<_>>();
    rules.sort_by_key(|rule| (rule["module"].as_str(), rule["index"].as_u64()));
    let names = |key: &str, id: &str| {
        let mut names = Vec::<String>::new();
        for rule in &rules {
            let listed = rule[key]
                .as_array()
                .is_some_and(|programs| programs.iter().any(|program| program == id));
            let name = rule_name(rule);
            if listed && !names.contains(&name) {
                names.push(name);
            }
        }
        names
    };
    for program in document["programs"].as_array().into_iter().flatten() {
        let id = program["id"].as_str().unwrap_or_default();
        text.push_str("\n[[case]]\n");
        line(text, "id", &string(id));
        line(
            text,
            "class",
            &string(program["class"].as_str().unwrap_or("refused")),
        );
        line(text, "fired", &strings(&names("fired_by", id)));
        line(text, "matched", &strings(&names("reached_by", id)));
    }
}

fn mutations(text: &mut String, document: &Value) {
    for row in document["mutations"].as_array().into_iter().flatten() {
        text.push_str("\n[[mutation]]\n");
        line(text, "id", &string(row["id"].as_str().unwrap_or_default()));
        line(
            text,
            "status",
            &string(row["status"].as_str().unwrap_or_default()),
        );
    }
}

/// A rule's name: its KRS item, its label, or its `file:line` (`module#index` without a file).
fn rule_name(rule: &Value) -> String {
    if let Some(item) = rule["krs"]["item"].as_str() {
        return item.to_owned();
    }
    if let Some(label) = rule["label"].as_str() {
        return label.to_owned();
    }
    match (rule["file"].as_str(), rule["start_line"].as_u64()) {
        (Some(file), Some(line)) => format!("{file}:{line}"),
        _ => format!(
            "{}#{}",
            rule["module"].as_str().unwrap_or_default(),
            rule["index"]
        ),
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
