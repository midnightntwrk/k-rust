//! The `kink-flow` command line. Every command prints one JSON document on stdout.
//!
//! Exit status: [`EXIT_OK`] when the command did its job and found nothing wrong with the
//! corpus, [`EXIT_CORPUS`] when the manifest, the specification or a program is refused
//! (the document says which and why), and [`EXIT_USAGE`] on a usage error (stderr).

use crate::{
    admit::{FlowAdmission, admit},
    manifest::{FlowManifest, ManifestError},
    mutation::MutationList,
    report::{ReportOptions, render},
    results::ResultsOptions,
    search::{RunOptions, mutation_list_refused},
};
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use serde_json::{Value, json};
use std::{
    ffi::OsString,
    io::Write,
    path::{Path, PathBuf},
};

pub const EXIT_OK: u8 = 0;
pub const EXIT_CORPUS: u8 = 1;
pub const EXIT_USAGE: u8 = 2;

pub const USAGE: &str = "usage: kink-flow check FLOW.toml | kink-flow results FLOW.toml \
                         [--verify] [--cache DIR] | kink-flow run FLOW.toml MUTATIONS.toml \
                         [--only ID]... [--cache DIR] | kink-flow report FLOW.toml [--cache DIR]";

/// Run one command; returns the process exit status.
pub fn execute(args: Vec<OsString>) -> u8 {
    let args = args
        .into_iter()
        .map(|arg| arg.into_string())
        .collect::<Result<Vec<_>, _>>();
    let (document, status) = match args.as_deref() {
        Ok([command, manifest]) if command == "check" => {
            let manifest = PathBuf::from(manifest);
            if !manifest.is_file() {
                return usage(&format!("{} is not a file", manifest.display()));
            }
            match on_stack(move || check(&manifest)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the admission thread panicked");
                    return EXIT_CORPUS;
                }
            }
        }
        Ok([command, manifest, rest @ ..]) if command == "results" => {
            let manifest = PathBuf::from(manifest);
            if !manifest.is_file() {
                return usage(&format!("{} is not a file", manifest.display()));
            }
            let options = match results_options(rest) {
                Ok(options) => options,
                Err(message) => return usage(&message),
            };
            match on_stack(move || results(&manifest, &options)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the results thread panicked");
                    return EXIT_CORPUS;
                }
            }
        }
        Ok([command, manifest, mutations, rest @ ..]) if command == "run" => {
            let manifest = PathBuf::from(manifest);
            let mutations = PathBuf::from(mutations);
            for file in [&manifest, &mutations] {
                if !file.is_file() {
                    return usage(&format!("{} is not a file", file.display()));
                }
            }
            let options = match run_options(rest) {
                Ok(options) => options,
                Err(message) => return usage(&message),
            };
            if let Ok(list) = MutationList::read(&mutations)
                && let Some(id) = options
                    .only
                    .iter()
                    .find(|id| !list.mutations.iter().any(|m| &m.id == *id))
            {
                return usage(&format!("--only {id}: no mutation has this id"));
            }
            match on_stack(move || run(&manifest, &mutations, &options)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the run thread panicked");
                    return EXIT_CORPUS;
                }
            }
        }
        Ok([command, manifest, rest @ ..]) if command == "report" => {
            let manifest = PathBuf::from(manifest);
            if !manifest.is_file() {
                return usage(&format!("{} is not a file", manifest.display()));
            }
            let options = match report_options(rest) {
                Ok(options) => options,
                Err(message) => return usage(&message),
            };
            report(&manifest, &options)
        }
        _ => return usage(USAGE),
    };
    let mut stdout = std::io::stdout().lock();
    if writeln!(stdout, "{}", render(&document)).is_err() {
        return EXIT_CORPUS;
    }
    status
}

fn usage(message: &str) -> u8 {
    eprintln!("kink-flow: {message}");
    if message != USAGE {
        eprintln!("{USAGE}");
    }
    EXIT_USAGE
}

/// Run `body` on a thread with kink-corpus's definition stack allowance.
fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    std::thread::Builder::new()
        .name("kink-flow".into())
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .ok()?
        .join()
        .ok()
}

fn results_options(args: &[String]) -> Result<ResultsOptions, String> {
    let mut options = ResultsOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--verify" if !options.verify => options.verify = true,
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

fn run_options(args: &[String]) -> Result<RunOptions, String> {
    let mut options = RunOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--only" => {
                let id = args.next().ok_or("--only needs a mutation id")?;
                if !options.only.contains(id) {
                    options.only.push(id.clone());
                }
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

fn report_options(args: &[String]) -> Result<ReportOptions, String> {
    let mut options = ReportOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

/// `kink-flow report FLOW.toml [--cache DIR]`: the run document the last `run` wrote, as `run`
/// printed it, and [`EXIT_OK`]; or a `kink-flow-report` document saying why there is none
/// (`missing`, `unreadable`) and [`EXIT_CORPUS`], which is also the status when the manifest
/// does not decode.
pub fn report(manifest: &Path, options: &ReportOptions) -> (Value, u8) {
    match FlowManifest::read(manifest) {
        Err(error) => {
            let mut document = manifest_refused(&error);
            document["schema"] = json!(crate::report::MISSING_SCHEMA);
            (document, EXIT_CORPUS)
        }
        Ok(manifest) => {
            let (document, ok) = crate::report::report(&manifest, options);
            (document, if ok { EXIT_OK } else { EXIT_CORPUS })
        }
    }
}

/// `kink-flow run FLOW.toml MUTATIONS.toml [--only ID]... [--cache DIR]`: the run document
/// (README 5.6) and the exit status: [`EXIT_OK`] when every selected mutation got its status
/// (survivors, timeouts and invalid mutations included); [`EXIT_CORPUS`] when the manifest,
/// the mutation list, the specification or a program is refused, a run failed, a cache file
/// could not be written, no program is comparable, or a baseline run no longer matches its
/// cached result (the run then stops).
pub fn run(manifest: &Path, mutations: &Path, options: &RunOptions) -> (Value, u8) {
    let manifest = match FlowManifest::read(manifest) {
        Ok(manifest) => manifest,
        Err(error) => {
            let mut document = manifest_refused(&error);
            document["schema"] = json!("kink-flow-run");
            return (document, EXIT_CORPUS);
        }
    };
    let list = match MutationList::read(mutations) {
        Ok(list) => list,
        Err(error) => return (mutation_list_refused(&error.to_string()), EXIT_CORPUS),
    };
    let (document, ok) = crate::search::run(&manifest, &list, options);
    (document, if ok { EXIT_OK } else { EXIT_CORPUS })
}

/// `kink-flow results FLOW.toml [--verify] [--cache DIR]`: the results document (README 5.3)
/// and the exit status: [`EXIT_OK`] unless the manifest, the specification or a program is
/// refused, a run failed, a record could not be written or `--verify` found a mismatch.
/// A timeout or unknown program is not an error: it is reported, and it cannot kill.
pub fn results(manifest: &Path, options: &ResultsOptions) -> (Value, u8) {
    match FlowManifest::read(manifest) {
        Err(error) => {
            let mut document = manifest_refused(&error);
            document["schema"] = json!("kink-flow-results");
            (document, EXIT_CORPUS)
        }
        Ok(manifest) => {
            let (document, ok) = crate::results::results(&manifest, options);
            (document, if ok { EXIT_OK } else { EXIT_CORPUS })
        }
    }
}

/// `kink-flow check FLOW.toml`: the check document and the exit status.
pub fn check(manifest: &Path) -> (Value, u8) {
    match FlowManifest::read(manifest) {
        Err(error) => (manifest_refused(&error), EXIT_CORPUS),
        Ok(manifest) => {
            let admission = admit(&manifest);
            let status = if admission.all_admitted() {
                EXIT_OK
            } else {
                EXIT_CORPUS
            };
            (check_document(&admission), status)
        }
    }
}

fn header(spec: Value, programs: Vec<Value>) -> Value {
    json!({
        "schema": "kink-flow-check",
        "version": 1,
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "spec": spec,
        "programs": programs,
    })
}

/// The document of a manifest that does not decode: the spec is refused at stage
/// `manifest` with the error, which names the key or program.
pub fn manifest_refused(error: &ManifestError) -> Value {
    header(
        json!({
            "outcome": "refused",
            "stage": "manifest",
            "reason": "invalid-manifest",
            "detail": error.to_string(),
            "files": [],
        }),
        Vec::new(),
    )
}

/// The check document of an admission.
pub fn check_document(admission: &FlowAdmission) -> Value {
    let record = &admission.record;
    let refusal = record.refusal.as_ref();
    let spec = json!({
        "outcome": if refusal.is_some() { "refused" } else { "admitted" },
        "stage": refusal.map(|r| &r.stage),
        "reason": refusal.map(|r| &r.reason),
        "detail": refusal.map(|r| &r.detail),
        "files": record
            .files
            .iter()
            .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
            .collect::<Vec<_>>(),
    });
    let programs = admission
        .programs
        .iter()
        .map(|program| {
            let refusal = program.outcome.as_ref().err();
            json!({
                "id": program.id,
                "outcome": if refusal.is_some() { "refused" } else { "ok" },
                "stage": refusal.map(|r| &r.stage),
                "reason": refusal.map(|r| &r.reason),
                "detail": refusal.map(|r| &r.detail),
            })
        })
        .collect();
    header(spec, programs)
}
