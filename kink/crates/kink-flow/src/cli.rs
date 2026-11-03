//! The `kink-flow` command line. Every command prints one JSON document on stdout.
//!
//! Exit status: [`EXIT_OK`] when the command did its job and found nothing wrong with the
//! corpus, [`EXIT_CORPUS`] when the manifest, the specification, a program or a mutation is
//! refused (the document says which and why), and [`EXIT_USAGE`] on a usage error (stderr).
//!
//! A mutation list (`MUTATIONS` below) is a `MUTATIONS.toml` file or a mutations directory of
//! `<topic>.toml` files ([`MutationList::read`]).

use crate::{
    admit::{FlowAdmission, ProgramAdmission, admit, admit_spec},
    check::{CorpusCoverage, MutationCheck, check_mutations, corpus_coverage},
    fuzz::{FuzzJob, FuzzOptions, TemplateList},
    manifest::{FlowManifest, ManifestError},
    memo::MemoUse,
    mutation::MutationList,
    pattern::PatternList,
    query::{QueryOptions, pattern_list_refused},
    report::{ReportOptions, render},
    results::{ResultsOptions, cache_directory},
    search::{ProgramOrder, RunMode, RunOptions, mutation_list_refused},
};
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::{
    ffi::OsString,
    io::Write,
    path::{Path, PathBuf},
};

pub const EXIT_OK: u8 = 0;
pub const EXIT_CORPUS: u8 = 1;
pub const EXIT_USAGE: u8 = 2;

pub const USAGE: &str = "usage: kink-flow --version | kink-flow check FLOW.toml [--mutations \
                         MUTATIONS] [--cache DIR] | kink-flow \
                         results FLOW.toml [--verify] [--mutations MUTATIONS] [--cache DIR] \
                         | kink-flow run \
                         FLOW.toml MUTATIONS [--only ID]... [--verify] [--order cost|corpus] \
                         [--compile-workers N] [--no-memo] [--cache DIR] | kink-flow report \
                         FLOW.toml [--cache DIR] | kink-flow query FLOW.toml PATTERNS.toml \
                         [--only ID]... [--verify] [--cache DIR] | kink-flow fuzz FLOW.toml \
                         TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS \
                         | --reach RULE [--fired] | --pattern ID --patterns PATTERNS.toml) \
                         [--cases N | --work W] [--seed S] [--max-work N] [--time-limit-ms T] \
                         [--assume-joined NAME]... [--one-path] [--cache DIR] [--no-confirm] \
                         [--no-filter]; MUTATIONS is a MUTATIONS.toml or a directory of \
                         <topic>.toml files";

/// Run one command; returns the process exit status.
pub fn execute(args: Vec<OsString>) -> u8 {
    let args = args
        .into_iter()
        .map(|arg| arg.into_string())
        .collect::<Result<Vec<_>, _>>();
    let (document, status) = match args.as_deref() {
        // The builds a document's identity names, as `krust-fuzz --version` prints its own.
        Ok([flag]) if flag == "--version" => {
            println!(
                "kink-flow {} (k-rust {})",
                env!("CARGO_PKG_VERSION"),
                crate::k_rust_revision()
            );
            return EXIT_OK;
        }
        Ok([command, manifest, rest @ ..]) if command == "check" => {
            let manifest = PathBuf::from(manifest);
            if !manifest.is_file() {
                return usage(&format!("{} is not a file", manifest.display()));
            }
            let options = match check_options(rest) {
                Ok(options) => options,
                Err(message) => return usage(&message),
            };
            if let Some(list) = options.mutations.as_ref().filter(|list| !list.exists()) {
                return usage(&format!("{} is not a file or directory", list.display()));
            }
            match on_stack(move || check_with(&manifest, &options)) {
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
            if let Some(list) = options.mutations.as_ref().filter(|list| !list.exists()) {
                return usage(&format!("{} is not a file or directory", list.display()));
            }
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
            if !manifest.is_file() {
                return usage(&format!("{} is not a file", manifest.display()));
            }
            if !mutations.exists() {
                return usage(&format!(
                    "{} is not a file or directory",
                    mutations.display()
                ));
            }
            let (options, mode) = match run_options(rest) {
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
            match on_stack(move || run_mode(&manifest, &mutations, &options, mode)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the run thread panicked");
                    return EXIT_CORPUS;
                }
            }
        }
        Ok([command, manifest, patterns, rest @ ..]) if command == "query" => {
            let manifest = PathBuf::from(manifest);
            let patterns = PathBuf::from(patterns);
            for file in [&manifest, &patterns] {
                if !file.is_file() {
                    return usage(&format!("{} is not a file", file.display()));
                }
            }
            let options = match query_options(rest) {
                Ok(options) => options,
                Err(message) => return usage(&message),
            };
            if let Ok(list) = PatternList::read(&patterns)
                && let Some(id) = options
                    .only
                    .iter()
                    .find(|id| !list.patterns.iter().any(|p| &p.id == *id))
            {
                return usage(&format!("--only {id}: no pattern has this id"));
            }
            match on_stack(move || query(&manifest, &patterns, &options)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the query thread panicked");
                    return EXIT_CORPUS;
                }
            }
        }
        Ok([command, manifest, templates, rest @ ..]) if command == "fuzz" => {
            let manifest = PathBuf::from(manifest);
            let templates = PathBuf::from(templates);
            for file in [&manifest, &templates] {
                if !file.is_file() {
                    return usage(&format!("{} is not a file", file.display()));
                }
            }
            let request = match fuzz_options(rest) {
                Ok(request) => request,
                Err(message) => return usage(&message),
            };
            match &request.job {
                FuzzJobRequest::Kill {
                    mutations: list, ..
                } if !list.exists() => {
                    return usage(&format!("{} is not a file or directory", list.display()));
                }
                FuzzJobRequest::Pattern { patterns: file, .. } if !file.is_file() => {
                    return usage(&format!("{} is not a file", file.display()));
                }
                _ => {}
            }
            if let Ok(list) = TemplateList::read(&templates)
                && list.get(&request.template).is_none()
            {
                return usage(&format!(
                    "--template {}: no template has this id",
                    request.template
                ));
            }
            if let FuzzJobRequest::Kill {
                mutation,
                mutations,
            } = &request.job
                && let Ok(list) = MutationList::read(mutations)
                && !list.mutations.iter().any(|m| &m.id == mutation)
            {
                return usage(&format!("--kill {mutation}: no mutation has this id"));
            }
            if let FuzzJobRequest::Pattern { id, patterns } = &request.job
                && let Ok(list) = PatternList::read(patterns)
                && !list.patterns.iter().any(|p| &p.id == id)
            {
                return usage(&format!("--pattern {id}: no pattern has this id"));
            }
            match on_stack(move || fuzz(&manifest, &templates, &request)) {
                Some(result) => result,
                None => {
                    eprintln!("kink-flow: the fuzz thread panicked");
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

/// Options of `kink-flow check`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CheckOptions {
    /// A mutation list to resolve against the specification ([`crate::check`]).
    pub mutations: Option<PathBuf>,
    /// The cache directory whose result records decide `unreached-rule`; default
    /// `<directory of FLOW.toml>/.kink-flow`. Nothing is written to it.
    pub cache: Option<PathBuf>,
}

fn check_options(args: &[String]) -> Result<CheckOptions, String> {
    let mut options = CheckOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--mutations" if options.mutations.is_none() => {
                let list = args.next().ok_or("--mutations needs a file or directory")?;
                options.mutations = Some(PathBuf::from(list));
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
            "--mutations" if options.mutations.is_none() => {
                let list = args.next().ok_or("--mutations needs a file or directory")?;
                options.mutations = Some(PathBuf::from(list));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    Ok(options)
}

fn run_options(args: &[String]) -> Result<(RunOptions, RunMode), String> {
    let mut options = RunOptions::default();
    let mut mode = RunMode::Search;
    let mut order = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--verify" if mode == RunMode::Search => mode = RunMode::Verify,
            "--order" if order.is_none() => {
                let value = args.next().ok_or("--order needs cost or corpus")?;
                order = Some(match value.as_str() {
                    "cost" => ProgramOrder::Cost,
                    "corpus" => ProgramOrder::Corpus,
                    _ => return Err(format!("--order {value:?}: expected cost or corpus")),
                });
                options.order = order.unwrap_or_default();
            }
            "--compile-workers" if options.compile_workers.is_none() => {
                let value = args.next().ok_or("--compile-workers needs a number")?;
                options.compile_workers = Some(
                    value
                        .parse::<usize>()
                        .ok()
                        .filter(|workers| *workers >= 1)
                        .ok_or_else(|| {
                            format!("--compile-workers {value:?}: expected a positive integer")
                        })?,
                );
            }
            "--no-memo" if options.memo == MemoUse::On => options.memo = MemoUse::Off,
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
    Ok((options, mode))
}

fn query_options(args: &[String]) -> Result<QueryOptions, String> {
    let mut options = QueryOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--verify" if !options.verify => options.verify = true,
            "--only" => {
                let id = args.next().ok_or("--only needs a pattern id")?;
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

/// A parsed `kink-flow fuzz` command line (after FLOW.toml and TEMPLATES.toml).
#[derive(Clone, Debug)]
pub struct FuzzRequest {
    pub template: String,
    pub job: FuzzJobRequest,
    pub options: FuzzOptions,
}

/// The job a `kink-flow fuzz` command line names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FuzzJobRequest {
    /// `--kill MUTATION --mutations MUTATIONS.toml`.
    Kill {
        mutation: String,
        mutations: PathBuf,
    },
    /// `--reach RULE [--fired]`.
    Reach { rule: String, fired: bool },
    /// `--pattern ID --patterns PATTERNS.toml`.
    Pattern { id: String, patterns: PathBuf },
}

fn number(flag: &str, value: Option<&String>) -> Result<u64, String> {
    let value = value.ok_or_else(|| format!("{flag} needs a number"))?;
    value
        .parse::<u64>()
        .map_err(|_| format!("{flag} {value:?}: expected a nonnegative integer"))
}

fn fuzz_options(args: &[String]) -> Result<FuzzRequest, String> {
    let mut options = FuzzOptions::default();
    let (mut template, mut mutation, mut mutations) = (None, None, None);
    let (mut reach, mut pattern, mut patterns, mut fired) = (None, None, None, false);
    let (mut budget, mut seed, mut max_work, mut time_limit) = (None, None, None, None);
    let (mut one_path, mut no_confirm, mut no_filter) = (false, false, false);
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--template" if template.is_none() => {
                template = Some(args.next().ok_or("--template needs a template id")?.clone());
            }
            "--kill" if mutation.is_none() => {
                mutation = Some(args.next().ok_or("--kill needs a mutation id")?.clone());
            }
            "--mutations" if mutations.is_none() => {
                mutations = Some(PathBuf::from(
                    args.next().ok_or("--mutations needs a file or directory")?,
                ));
            }
            "--reach" if reach.is_none() => {
                reach = Some(args.next().ok_or("--reach needs a rule")?.clone());
            }
            "--fired" if !fired => fired = true,
            "--pattern" if pattern.is_none() => {
                pattern = Some(args.next().ok_or("--pattern needs a pattern id")?.clone());
            }
            "--patterns" if patterns.is_none() => {
                patterns = Some(PathBuf::from(args.next().ok_or("--patterns needs a file")?));
            }
            "--attempts" => {
                return Err(
                    "--attempts: there is no seed retry; when kink refuses the shrunk witness the \
                     unshrunk one is confirmed, and nothing more (fz26 D33)"
                        .into(),
                );
            }
            "--cases" if budget.is_none() => {
                let cases = number("--cases", args.next())?;
                if cases == 0 {
                    return Err("--cases 0: give at least one case".into());
                }
                budget = Some(k_rust_fuzz::Budget::Cases(cases));
            }
            "--work" if budget.is_none() => {
                let work = number("--work", args.next())?;
                if work == 0 {
                    return Err("--work 0: give a positive work budget".into());
                }
                budget = Some(k_rust_fuzz::Budget::Work(work));
            }
            "--seed" if seed.is_none() => seed = Some(number("--seed", args.next())?),
            "--max-work" if max_work.is_none() => {
                let work = number("--max-work", args.next())?;
                if work == 0 {
                    return Err("--max-work 0: give a positive bound".into());
                }
                max_work = Some(work);
            }
            "--time-limit-ms" if time_limit.is_none() => {
                time_limit = Some(number("--time-limit-ms", args.next())?);
            }
            "--assume-joined" => {
                let name = args
                    .next()
                    .ok_or("--assume-joined needs a finding's name")?;
                if name.trim().is_empty() {
                    return Err("--assume-joined needs a nonempty name".into());
                }
                if !options.assume_joined.contains(name) {
                    options.assume_joined.push(name.clone());
                }
            }
            "--one-path" if !one_path => one_path = true,
            "--no-confirm" if !no_confirm => no_confirm = true,
            "--no-filter" if !no_filter => no_filter = true,
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(format!("unexpected argument {arg:?}")),
        }
    }
    let template = template.ok_or("give --template ID")?;
    let job = match (mutation, reach, pattern) {
        (Some(mutation), None, None) => {
            if fired || patterns.is_some() {
                return Err("--fired and --patterns belong to --reach and --pattern".into());
            }
            let mutations = mutations.ok_or("--kill needs --mutations MUTATIONS.toml")?;
            FuzzJobRequest::Kill {
                mutation,
                mutations,
            }
        }
        (None, Some(rule), None) => {
            if mutations.is_some() || patterns.is_some() {
                return Err("--mutations and --patterns belong to --kill and --pattern".into());
            }
            FuzzJobRequest::Reach { rule, fired }
        }
        (None, None, Some(id)) => {
            if mutations.is_some() || fired {
                return Err("--mutations and --fired belong to --kill and --reach".into());
            }
            if !options.assume_joined.is_empty() {
                return Err(
                    "--assume-joined: a pattern job reads no data end, so it takes no assumed \
                     name"
                        .into(),
                );
            }
            let patterns = patterns.ok_or("--pattern needs --patterns PATTERNS.toml")?;
            FuzzJobRequest::Pattern { id, patterns }
        }
        (None, None, None) => {
            return Err(
                "give the job: --kill MUTATION --mutations MUTATIONS.toml, --reach RULE \
                        [--fired], or --pattern ID --patterns PATTERNS.toml"
                    .into(),
            );
        }
        _ => return Err("give one job: --kill, --reach or --pattern".into()),
    };
    options.confirm = !no_confirm;
    options.filter = !no_filter;
    if let Some(budget) = budget {
        options.budget = budget;
    }
    options.seed = seed.unwrap_or(0);
    options.max_work = max_work;
    options.time_limit_ms = time_limit;
    if one_path {
        options.paths = k_rust_fuzz::PathMode::OnePath;
    }
    Ok(FuzzRequest {
        template,
        job,
        options,
    })
}

/// `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations
/// MUTATIONS.toml | --reach RULE [--fired] | --pattern ID --patterns PATTERNS.toml) [options]
/// [--no-confirm] [--no-filter]`: the fuzz document ([`crate::fuzz`]) and the exit
/// status: [`EXIT_OK`] when the job reached a verdict (`stopped` is `null`, `budget`,
/// `client-refused`, `unconfirmed`, `assembly-mismatch`, `equivalent`, `rejected-out` or
/// `time-limit`); [`EXIT_CORPUS`] when an input, the template or the mutation is refused
/// (`refused`), the campaign is `not-comparable`, or it `aborted` (the README's and the guide's
/// table).
pub fn fuzz(manifest: &Path, templates: &Path, request: &FuzzRequest) -> (Value, u8) {
    let manifest = match FlowManifest::read(manifest) {
        Ok(manifest) => manifest,
        Err(error) => return (crate::fuzz::input_refused("FLOW.toml", &error), EXIT_CORPUS),
    };
    let templates = match TemplateList::read(templates) {
        Ok(templates) => templates,
        Err(error) => {
            return (
                crate::fuzz::input_refused("TEMPLATES.toml", &error),
                EXIT_CORPUS,
            );
        }
    };
    let (document, ok) = match &request.job {
        FuzzJobRequest::Kill {
            mutation,
            mutations,
        } => {
            let list = match MutationList::read(mutations) {
                Ok(list) => list,
                Err(error) => {
                    return (
                        crate::fuzz::input_refused("MUTATIONS.toml", &error),
                        EXIT_CORPUS,
                    );
                }
            };
            crate::fuzz::fuzz_job(
                &manifest,
                &templates,
                &request.template,
                FuzzJob::Kill {
                    list: &list,
                    mutation,
                },
                &request.options,
            )
        }
        FuzzJobRequest::Reach { rule, fired } => crate::fuzz::fuzz_job(
            &manifest,
            &templates,
            &request.template,
            FuzzJob::Reach {
                rule,
                fired: *fired,
            },
            &request.options,
        ),
        FuzzJobRequest::Pattern { id, patterns } => {
            let list = match PatternList::read(patterns) {
                Ok(list) => list,
                Err(error) => {
                    return (
                        crate::fuzz::input_refused("PATTERNS.toml", &error),
                        EXIT_CORPUS,
                    );
                }
            };
            crate::fuzz::fuzz_job(
                &manifest,
                &templates,
                &request.template,
                FuzzJob::Pattern { list: &list, id },
                &request.options,
            )
        }
    };
    (document, if ok { EXIT_OK } else { EXIT_CORPUS })
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

/// `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify] [--cache DIR]`: the query
/// document (flow F-18, [`crate::query`]) and the exit status: [`EXIT_OK`] when every selected
/// (pattern, program) got its answer (`hit`, `no`, `unknown` or `invalid-pattern`; a refuted claim
/// included); [`EXIT_CORPUS`] when the manifest, the pattern list, the specification or a program
/// is refused, a search failed, an answer's record could not be written, or `--verify` found a
/// stored answer that differs from a live one.
pub fn query(manifest: &Path, patterns: &Path, options: &QueryOptions) -> (Value, u8) {
    let manifest = match FlowManifest::read(manifest) {
        Ok(manifest) => manifest,
        Err(error) => {
            let mut document = manifest_refused(&error);
            document["schema"] = json!(crate::query::QUERY_SCHEMA);
            return (document, EXIT_CORPUS);
        }
    };
    let list = match PatternList::read(patterns) {
        Ok(list) => list,
        Err(error) => return (pattern_list_refused(&error), EXIT_CORPUS),
    };
    let (document, ok) = crate::query::query(&manifest, &list, options);
    (document, if ok { EXIT_OK } else { EXIT_CORPUS })
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

/// `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--cache DIR]`: the run
/// document (README 5.6, 7.5) and the exit status: [`EXIT_OK`] when every selected mutation got
/// its status (survivors and timeouts included) and none is invalid; [`EXIT_CORPUS`] when the
/// manifest, the mutation list, the specification or a program is refused, a selected mutation
/// is invalid (`invalid-mutation` or `invalid`: [`invalid_mutations`]), a run failed, a
/// cache file could not be written, no program is comparable, a baseline run no longer matches
/// its cached result (the run then stops), or `--verify` found a cached outcome that differs
/// from a live run.
pub fn run(manifest: &Path, mutations: &Path, options: &RunOptions) -> (Value, u8) {
    run_mode(manifest, mutations, options, RunMode::Search)
}

/// `kink-flow run` ([`RunMode::Search`]) or `kink-flow run --verify` ([`RunMode::Verify`]);
/// see [`run`].
pub fn run_mode(
    manifest: &Path,
    mutations: &Path,
    options: &RunOptions,
    mode: RunMode,
) -> (Value, u8) {
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
    let (document, ok) = crate::search::run_with(&manifest, &list, options, mode);
    let status = if ok && invalid_mutations(&document) == 0 {
        EXIT_OK
    } else {
        EXIT_CORPUS
    };
    (document, status)
}

/// The number of a run document's rows whose mutation its author must fix before it is judged:
/// status `invalid-mutation` (it does not resolve) or `invalid` (its mutant does not compile, or
/// may have no model: `inconsistent-mutant`). Every other status is a verdict about the corpus or
/// a fault of the tool or the host, not of the mutation.
pub fn invalid_mutations(document: &Value) -> u64 {
    [crate::search::INVALID_MUTATION, "invalid"]
        .iter()
        .map(|status| document["counts"][*status].as_u64().unwrap_or(0))
        .sum()
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
    check_with(manifest, &CheckOptions::default())
}

/// `kink-flow check FLOW.toml [--mutations MUTATIONS] [--cache DIR]`: the check document and the
/// exit status. With a mutation list, every mutation is also resolved against the admitted
/// specification and no program runs ([`crate::check`]): [`check_corpus_mutations`] then
/// [`check_mutations_document`], with nothing added between them.
pub fn check_with(manifest: &Path, options: &CheckOptions) -> (Value, u8) {
    let Some(path) = &options.mutations else {
        return check_admission(manifest);
    };
    let manifest = match FlowManifest::read(manifest) {
        Ok(manifest) => manifest,
        Err(error) => return (manifest_refused(&error), EXIT_CORPUS),
    };
    let checked = check_corpus_mutations(
        &manifest,
        MutationList::read(path),
        options.cache.as_deref(),
    );
    check_mutations_document(&checked)
}

/// `check --mutations` before it is rendered: the admission of the specification and the
/// programs, the mutation list, and, when the specification is admitted and the list decodes, the
/// check of every mutation ([`MutationCheck`]) and the coverage that decided `unreached-rule`.
/// A front end adds its own findings to [`Self::mutations`] (the admitted specification is
/// `admission.spec`) and renders with [`check_mutations_document`].
#[derive(Debug)]
pub struct CorpusMutationCheck {
    pub admission: FlowAdmission,
    /// The decoded list, or why it does not decode.
    pub list: Result<MutationList, ManifestError>,
    /// `None` when the specification is refused or the list does not decode.
    pub mutations: Option<MutationCheck>,
    /// `None` when the specification is refused.
    pub coverage: Option<CorpusCoverage>,
}

/// Admit `manifest`'s specification and programs, read the cached coverage (from `cache`, default
/// `.kink-flow/` next to `FLOW.toml`; nothing is written) and check every mutation of `list`;
/// nothing is compiled or run.
pub fn check_corpus_mutations(
    manifest: &FlowManifest,
    list: Result<MutationList, ManifestError>,
    cache: Option<&Path>,
) -> CorpusMutationCheck {
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return CorpusMutationCheck {
            admission: FlowAdmission {
                record,
                spec: None,
                programs: Vec::new(),
            },
            list,
            mutations: None,
            coverage: None,
        };
    };
    let (programs, coverage) = {
        let mut session = inputs.session(&spec);
        let programs = manifest
            .programs
            .iter()
            .map(|program| ProgramAdmission {
                id: program.id.clone(),
                outcome: session
                    .text(program)
                    .and_then(|text| session.test_case(program, text)),
            })
            .collect::<Vec<_>>();
        let cache = cache_directory(manifest, cache);
        (programs, corpus_coverage(&spec, manifest, &session, &cache))
    };
    let mutations = list
        .as_ref()
        .ok()
        .map(|list| check_mutations(manifest, &spec.loaded, list, Some(&coverage)));
    CorpusMutationCheck {
        admission: FlowAdmission {
            record,
            spec: Some(spec),
            programs,
        },
        list,
        mutations,
        coverage: Some(coverage),
    }
}

/// The document of `check --mutations` and its exit status: the check document
/// ([`check_document`]) with `mutation_list`, `mutations` and `coverage`, and [`EXIT_OK`] when the
/// specification and every program are admitted, the list decodes and no mutation is refused
/// (by resolution or by a finding with `refusal: true`), else [`EXIT_CORPUS`].
pub fn check_mutations_document(checked: &CorpusMutationCheck) -> (Value, u8) {
    let mut document = check_document(&checked.admission);
    match &checked.list {
        Err(error) => {
            document["mutation_list"] = json!({"outcome": "refused", "detail": error.to_string()});
        }
        Ok(_) if checked.admission.spec.is_none() => {}
        Ok(_) => {
            document["mutation_list"] = json!({"outcome": "ok", "detail": null});
            if let Some(mutations) = &checked.mutations {
                document["mutations"] = mutations.value();
            }
            if let Some(coverage) = &checked.coverage {
                document["coverage"] = coverage.value();
            }
        }
    }
    let refused = checked.list.is_err()
        || checked
            .mutations
            .as_ref()
            .is_some_and(MutationCheck::refused);
    let status = if checked.admission.all_admitted() && !refused {
        EXIT_OK
    } else {
        EXIT_CORPUS
    };
    (document, status)
}

/// `kink-flow check FLOW.toml` without a mutation list: admission alone.
fn check_admission(manifest: &Path) -> (Value, u8) {
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

/// The version of the check document: 2 adds `mutation_list`, `mutations` and `coverage` (null
/// without `--mutations`).
pub const CHECK_VERSION: u64 = 2;

fn header(spec: Value, programs: Vec<Value>) -> Value {
    json!({
        "schema": "kink-flow-check",
        "version": CHECK_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "spec": spec,
        "programs": programs,
        "mutation_list": null,
        "mutations": null,
        "coverage": null,
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
