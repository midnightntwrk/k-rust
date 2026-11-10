//! The `kink-flow` command line. Every command prints one JSON document on stdout, or with
//! `--output verdicts` (`coverage`, `run` and `report`) its deterministic rendering
//! ([`crate::verdicts`]), or with `coverage --output text` a summary for a reader
//! ([`crate::coverage::text`]).
//!
//! Exit status: what the caller does next, one of four: [`EXIT_YES`] when the
//! command answered its question (rely on the answer), [`EXIT_NO`] when the answer is a finding
//! (act on it), [`EXIT_UNASKED`] when the question could not be asked (fix the input or the
//! command: a usage error on stderr, or a refusal the document names), and [`EXIT_UNANSWERED`]
//! when the command ran and has no answer (retry with more budget or another approach). A
//! command that answers for several parts (programs, mutations, (pattern, program) pairs) exits
//! with the [`exit_join`] of the parts' statuses. Each verb's statuses are its function's
//! (`check_with`, `coverage`, `run`, `report`, `query`, `fuzz`).
//!
//! A mutation list (`MUTATIONS` below) is a `MUTATIONS.toml` file or a mutations directory of
//! `<topic>.toml` files ([`MutationList::read`]).
//!
//! The command layer is a library both front ends use: kink-flow's own command line, and the krs
//! front end, which binds a KRS corpus's manifest to the K it emits
//! ([`crate::manifest::ManifestFile::bind`]). [`FlowCommand::parse`] reads a verb's options
//! exactly as `kink-flow <verb>` does, the corpus's files given by the front end
//! ([`CommandFiles`]: kink-flow's operands, or the front end's layout); [`dispatch`] runs the
//! command on the large stack kink's definitions need. A [`FrontEnd`] adds how next steps spell
//! the front end's commands ([`CommandSpelling`]), the mutations it refused before the engine
//! ([`FrontEnd::refused`]), an annotation of the document ([`FrontEnd::annotate`]), and the
//! mutations it derives from the definition's source for `coverage` ([`FrontEnd::derived`]).
//! kink-flow itself runs every command with [`FrontEnd::default`].

use crate::{
    admit::{FlowAdmission, admit_spec},
    check::{CorpusCoverage, Finding, MutationCheck, check_mutations, corpus_coverage},
    coverage::{CoverageOptions, Tier},
    flips::Derived,
    fuzz::{FuzzJob, FuzzOptions, TemplateList},
    manifest::{FlowManifest, ManifestError},
    memo::MemoUse,
    mutation::{InvalidMutation, MutationList},
    pattern::PatternList,
    query::{QueryOptions, pattern_list_refused},
    report::{ReportOptions, render},
    results::cache_directory,
    search::{RunMode, RunOptions, mutation_list_refused},
};
use kink_campaign::ScheduleMode;
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    ffi::OsString,
    io::{IsTerminal, Write},
    path::{Path, PathBuf},
};

/// The command answered its question: rely on the answer.
pub const EXIT_YES: u8 = 0;
/// The answer is a finding: act on it (a `--verify` mismatch, a fact `check` finds that makes a
/// verdict impossible, an expectation or a claim the baseline does not meet).
pub const EXIT_NO: u8 = 1;
/// The question could not be asked: fix the input or the command (a usage error, a refused
/// manifest, specification, program, list, mutation, pattern or template, a failed run or write).
pub const EXIT_UNASKED: u8 = 2;
/// No answer: retry with more budget or another approach (a timeout, an unknown).
pub const EXIT_UNANSWERED: u8 = 3;

/// The usage line, as a literal so that [`USAGE`] and [`HELP`] share it.
macro_rules! usage_line {
    () => {
        "usage: kink-flow --version | kink-flow check FLOW.toml [--mutations \
         MUTATIONS] [--cache DIR] | kink-flow \
         coverage FLOW.toml [--tier 1|2] [--depth N] [--verify] [--lock FILE [--locked]] \
         [--cache DIR] [--output json|text|verdicts] | kink-flow run \
         FLOW.toml MUTATIONS [--only ID]... [--verify] \
         [--full] [--lock FILE [--locked]] [--compile-workers N] [--no-memo] [--progress] [--cache DIR] [--output \
         json|verdicts] | kink-flow report \
         FLOW.toml [--cache DIR] [--output json|verdicts] | kink-flow query FLOW.toml PATTERNS.toml \
         [--only ID]... [--verify] [--cache DIR] | kink-flow fuzz FLOW.toml \
         TEMPLATES.toml --template ID (--kill MUTATION --mutations MUTATIONS \
         | --matched RULE | --fired RULE | --refuted RULE | --cover ITEM | --pattern ID \
         --patterns PATTERNS.toml) [--cases N | --work W] [--seed S] [--max-work N] [--time-limit-ms T] \
         [--stack-stops N] [--open-stops N] [--assume-joined NAME]... [--one-path] [--cache DIR] \
         [--no-confirm] [--no-filter]; MUTATIONS is a MUTATIONS.toml or a directory of \
         <topic>.toml files | kink-flow compare FLOW.toml [--only NAME]... [--cache DIR] \
         [--output json|text]; --help (or -h), anywhere, prints the loop, the mutation format and \
         the exit statuses"
    };
}

/// The usage line of every command, the first line `kink-flow --help` prints; a usage error
/// prints its verb's ([`Verb::synopsis`]).
pub const USAGE: &str = usage_line!();

/// What `kink-flow --help` (or `-h`) prints on stdout when the command line names no verb: the
/// usage line, then the loop, the mutation format and the exit statuses in one screen, for a
/// caller starting cold. After a verb, anywhere on the command line, it prints the verb's help
/// ([`verb_help`]).
pub const HELP: &str = concat!(
    usage_line!(),
    "

The loop:
  1. write programs in FLOW.toml; kink-flow coverage FLOW.toml --output text until nothing is
     open: every rule in scope fires, and every requirement of its condition is covered
  2. write mutations (MUTATIONS.toml, or one <topic>.toml per topic in a directory);
     kink-flow check FLOW.toml --mutations MUTATIONS until it exits 0
  3. kink-flow run FLOW.toml MUTATIONS: it reports the survivors, mutations no program kills
  4. for each survivor, write a program that kills it, or argue that no program can and
     drop the mutation, or keep it with the argument in its misunderstanding and
     expect = \"survive\" (its status stays survived, and run fails if a program kills
     it); run again (cached outcomes are not re-run)

A mutation (MUTATIONS.toml):
  [[mutation]]
  id = \"add-becomes-sub\"
  misunderstanding = \"addition evaluates as subtraction\"   # required: the mistake it writes down
  expect = \"kill\"                   # optional, \"kill\" or \"survive\": run fails when unmet
    [[mutation.edit]]               # one or more, applied together
    rule = \"add\"                    # a rule label, or a unique suffix of its components
    find = \"I1 +Int I2\"             # exact text, exactly once in that rule
    replace = \"I1 -Int I2\"          # its replacement
    # or, in place of find and replace: delete = true, which removes the rule
  An edit of emitted K (krs emit-k's definition.k) is anchored by rule, never by line =:
  its lines move with every emission.

Exit status:
  0  the command answered its question: rely on the answer
  1  the answer is a finding: act on it
  2  the question could not be asked: fix the input or the command
  3  the command ran and has no answer: retry with more budget or another approach

`kink-flow VERB --help` lists the verb's options.
Reference: kink/crates/kink-flow/README.md; guide: kink/README.md, \"Using kink-flow\"
"
);

/// What a usage error prints on stderr after its message when the command line names no verb:
/// the shape of every command line, and where the rest is.
const GENERAL_USAGE: &str = "usage: kink-flow --version | kink-flow VERB FLOW.toml [OPERAND] \
     [OPTIONS], VERB one of check, coverage, run, report, query, fuzz, compare\n`kink-flow --help` \
     explains the loop; `kink-flow VERB --help` lists a verb's options";

/// Run one command; returns the process exit status.
pub fn execute(args: Vec<OsString>) -> u8 {
    let Ok(args) = args
        .into_iter()
        .map(|arg| arg.into_string())
        .collect::<Result<Vec<_>, _>>()
    else {
        return usage("an argument is not valid UTF-8", None);
    };
    // The builds a document's identity names, as `krust-fuzz --version` prints its own.
    if let [flag] = args.as_slice()
        && flag == "--version"
    {
        println!(
            "kink-flow {} (k-rust {})",
            env!("CARGO_PKG_VERSION"),
            crate::k_rust_revision()
        );
        return EXIT_YES;
    }
    // Asking for help is a question the tool answers wherever it is asked, as after a verb
    // (`kink-flow run --help`): no operand or option value of kink-flow begins with `-h` or is
    // `--help`. After a verb it is the verb's help, which lists its options.
    let named = args.first().and_then(|first| Verb::parse(first));
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        match named {
            Some(verb) => print!("{}", verb_help(verb)),
            None => print!("{HELP}"),
        }
        return EXIT_YES;
    }
    let Some(verb) = named else {
        return usage(
            &args.first().map_or_else(
                || "missing verb".to_owned(),
                |first| {
                    if first == "--version" {
                        "--version takes no operand or option".to_owned()
                    } else {
                        Verb::retired(first).unwrap_or_else(|| format!("unknown verb {first:?}"))
                    }
                },
            ),
            None,
        );
    };
    let Some((verb, manifest, files, options)) = operands(&args) else {
        return usage(
            &format!("{} needs {}", verb.as_str(), verb.operands()),
            Some(verb),
        );
    };
    if !manifest.is_file() {
        return usage(&format!("{} is not a file", manifest.display()), Some(verb));
    }
    let command = match FlowCommand::parse(verb.as_str(), files, options) {
        Ok(command) => command,
        Err(message) => return usage(&message, Some(verb)),
    };
    let output = command.output();
    let progress = |line: &str| eprintln!("kink-flow: {line}");
    let front = FrontEnd {
        progress: command
            .shows_progress()
            .then_some(&progress as &(dyn Fn(&str) + Sync)),
        ..FrontEnd::default()
    };
    let (document, status) = match FlowManifest::read(&manifest) {
        Err(error) => (command.manifest_refused(&error), EXIT_UNASKED),
        Ok(manifest) => match dispatch(manifest, command, front) {
            Ok(result) => result,
            Err(panicked) => {
                eprintln!("kink-flow: {panicked}");
                return EXIT_UNASKED;
            }
        },
    };
    // A lock `--locked` found stale: what would change, one line each, whatever the output.
    for line in crate::lock::stale_lines(&document) {
        eprintln!("kink-flow: {line}");
    }
    for line in crate::lock::lock_notes(&document) {
        eprintln!("kink-flow: {line}");
    }
    // What of the lock rests on a run the clock stopped, and each entry it kept unverified.
    for line in crate::clock::clock_lines(&document) {
        eprintln!("kink-flow: {line}");
    }
    // A mutation's expectation the run does not meet, or cannot confirm: one line each.
    for line in crate::report::expectation_lines(&document) {
        eprintln!("kink-flow: {line}");
    }
    let text = match output {
        OutputFormat::Json => format!("{}\n", render(&document)),
        OutputFormat::Text => match text(&document) {
            Ok(text) => text,
            Err(message) => {
                eprintln!("kink-flow: {message}");
                return EXIT_UNASKED;
            }
        },
        OutputFormat::Verdicts => match crate::verdicts::verdicts(&document) {
            Ok(text) => {
                // The rendering names a refusal or a stop by its reason; its text goes to stderr.
                for detail in crate::verdicts::refusal_details(&document) {
                    eprintln!("kink-flow: {detail}");
                }
                text
            }
            Err(message) => {
                eprintln!("kink-flow: {message}");
                return EXIT_UNASKED;
            }
        },
    };
    let mut stdout = std::io::stdout().lock();
    if stdout.write_all(text.as_bytes()).is_err() {
        return EXIT_UNASKED;
    }
    status
}

/// A `kink-flow` command line's verb, manifest, operand files and options: `run`, `query` and
/// `fuzz` take one more operand (the mutation list, the patterns, the templates).
fn operands(args: &[String]) -> Option<(Verb, PathBuf, CommandFiles, &[String])> {
    let [command, manifest, rest @ ..] = args else {
        return None;
    };
    let verb = Verb::parse(command)?;
    let mut files = CommandFiles::default();
    let rest = match verb {
        Verb::Run | Verb::Query | Verb::Fuzz => {
            let (file, rest) = rest.split_first()?;
            let file = Some(PathBuf::from(file));
            match verb {
                Verb::Run => files.mutations = file,
                Verb::Query => files.patterns = file,
                _ => files.templates = file,
            }
            rest
        }
        Verb::Check | Verb::Coverage | Verb::Report | Verb::Compare => rest,
    };
    Some((verb, PathBuf::from(manifest), files, rest))
}

/// A usage error: its message, then the usage line of the verb the command line names (every
/// command line's shape when it names none) and where the rest is, on stderr. The whole help
/// would bury the message under the loop and the mutation format; the verb's usage line shows the
/// shape of the command the caller attempted, which is what a misspelt option, a missing operand
/// or a bad value is corrected against.
fn usage(message: &str, verb: Option<Verb>) -> u8 {
    eprintln!("kink-flow: {message}");
    match verb {
        Some(verb) => eprintln!(
            "usage: kink-flow {}\n`kink-flow {} --help` lists its options",
            verb.synopsis(),
            verb.as_str()
        ),
        None => eprintln!("{GENERAL_USAGE}"),
    }
    EXIT_UNASKED
}

/// One option of a verb, as its help lists it ([`Verb::options`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerbOption {
    /// The option as a command line writes it, with its value's name (`--cache DIR`).
    pub spelling: &'static str,
    /// What it does, in one line.
    pub meaning: &'static str,
}

impl VerbOption {
    /// The flag the option is given by (`--cache`), its spelling without the value's name.
    #[must_use]
    pub fn flag(&self) -> &'static str {
        self.spelling
            .split_once(' ')
            .map_or(self.spelling, |(flag, _)| flag)
    }
}

/// The usage error of a command-line argument no parser takes: `invalid option '--bogus'` for one
/// that begins with `-`, `unexpected argument 'x'` otherwise, as krs words both, so that one
/// error reads the same from `kink-flow`, `krs` and `krs kink`.
#[must_use]
pub fn unexpected_argument(arg: &str) -> String {
    if arg.starts_with('-') {
        format!("invalid option '{arg}'")
    } else {
        format!("unexpected argument '{arg}'")
    }
}

/// The usage error of an option given again: each parser refuses a flag no table of its verb
/// lists first ([`listed`]), so a listed flag that no arm takes is one whose value or switch an
/// earlier occurrence already set, worded as krs words it.
fn repeated(arg: &str) -> String {
    format!("{arg} specified more than once")
}

/// Refuse `arg`, read where an option begins, unless it is the flag of one of `verb`'s options
/// ([`Verb::options`]). Each option parser calls it first, so a flag its table does not list is
/// refused before any arm that would accept it: the verb's help, which prints the table, lists
/// every option the verb accepts.
fn listed(verb: Verb, arg: &str) -> Result<(), String> {
    if verb.options().iter().any(|option| option.flag() == arg) {
        Ok(())
    } else {
        Err(unexpected_argument(arg))
    }
}

const fn option(spelling: &'static str, meaning: &'static str) -> VerbOption {
    VerbOption { spelling, meaning }
}

const CACHE: VerbOption = option(
    "--cache DIR",
    "the cache directory (default: .kink-flow beside FLOW.toml)",
);
const OUTPUT: VerbOption = option(
    "--output json|verdicts",
    "print the JSON document (default) or its deterministic verdicts rendering",
);
const VERIFY: VerbOption = option(
    "--verify",
    "recompute every stored record and report each that differs (a finding, exit 1)",
);

const CHECK_OPTIONS: &[VerbOption] = &[
    option(
        "--mutations MUTATIONS",
        "resolve this mutation list against the specification, compiling and running nothing",
    ),
    option(
        "--cache DIR",
        "the cache whose result records decide unmatched-rule and unapplied-rule (default: \
         .kink-flow beside FLOW.toml); nothing is written to it",
    ),
];

const COVERAGE_OPTIONS: &[VerbOption] = &[
    option(
        "--tier 1|2",
        "1: the families read from the baseline runs, no mutant run; 2 (the default): also the \
         condition flips, where the front end derives them",
    ),
    option(
        "--depth N",
        "count sequences of length N instead of [coverage] depth (the lock is left unwritten)",
    ),
    VERIFY,
    option(
        "--lock FILE",
        "the coverage lock: try each flip's recorded killer first, and rewrite FILE after a run \
         with the manifest's own settings",
    ),
    option(
        "--locked",
        "with --lock: write nothing, and exit 1 when the run would change FILE",
    ),
    CACHE,
    option(
        "--output json|text|verdicts",
        "print the JSON document (default), a summary with one line per open target, or the \
         deterministic verdicts rendering",
    ),
];

const RUN_OPTIONS: &[VerbOption] = &[
    option(
        "--only ID",
        "judge only this mutation of the list (repeatable)",
    ),
    VERIFY,
    option(
        "--full",
        "run every comparable program on every mutation, and list every killer (killed_by)",
    ),
    option(
        "--lock FILE",
        "the killer record: try each mutation's recorded killer first, and rewrite FILE after a \
         run that judged the whole list",
    ),
    option(
        "--locked",
        "with --lock: leave FILE unwritten, and exit 1 when the run would change it",
    ),
    option(
        "--compile-workers N",
        "compile mutants ahead of their turn on up to N threads (default: 4)",
    ),
    option("--no-memo", "read and write none of the warm path's memos"),
    option(
        "--progress",
        "print a line on stderr as each phase starts and as each row is decided (also without \
         the flag when stderr is a terminal)",
    ),
    CACHE,
    OUTPUT,
];

const REPORT_OPTIONS: &[VerbOption] = &[CACHE, OUTPUT];

const QUERY_OPTIONS: &[VerbOption] = &[
    option(
        "--only ID",
        "answer only this pattern of the list (repeatable)",
    ),
    VERIFY,
    CACHE,
];

const FUZZ_OPTIONS: &[VerbOption] = &[
    option(
        "--template ID",
        "the template whose holes are searched (required)",
    ),
    option(
        "--kill MUTATION",
        "the job: hole values whose program kills this mutation of --mutations, or, where no \
         list holds the id, this condition flip the front end derives (an id of coverage's flips)",
    ),
    option(
        "--mutations MUTATIONS",
        "the mutation list --kill names a mutation of",
    ),
    option(
        "--matched RULE",
        "the job: hole values whose program matches RULE (FILE:LINE, a label or an id)",
    ),
    option(
        "--fired RULE",
        "the job: hole values whose program fires RULE",
    ),
    option(
        "--refuted RULE",
        "the job: hole values whose program refutes RULE's condition (its requirement refuted)",
    ),
    option(
        "--cover ITEM",
        "the job: hole values whose program covers this obligation of coverage (a target's item)",
    ),
    option(
        "--pattern ID",
        "the job: hole values whose program hits this pattern of --patterns",
    ),
    option(
        "--patterns PATTERNS.toml",
        "the pattern list --pattern names a pattern of",
    ),
    option("--cases N", "try N cases (default: 1000)"),
    option(
        "--work W",
        "bound the search by the work W in place of a number of cases",
    ),
    option("--seed S", "the proposer's seed (default: 0)"),
    option(
        "--max-work N",
        "the work bound of each case (default: 100000)",
    ),
    option(
        "--time-limit-ms T",
        "cancel the campaign's run after T ms (not the admission and compiles before it)",
    ),
    option(
        "--stack-stops N",
        "end the search after N cases in a row that stopped for lack of native stack (default: \
         25)",
    ),
    option(
        "--open-stops N",
        "with --kill, end the search after N cases in a row whose mutant run ends holding a term \
         not shown to exist (not-ceil-free; default: 25)",
    ),
    option(
        "--assume-joined NAME",
        "read this critical-pair finding as joined, for this command (repeatable)",
    ),
    option(
        "--one-path",
        "a case is a hit when one path tells the sides apart, not all paths",
    ),
    option(
        "--cache DIR",
        "the cache whose last run document is read (default: .kink-flow beside FLOW.toml)",
    ),
    option(
        "--no-confirm",
        "skip kink's own confirmation of the witness",
    ),
    option(
        "--no-filter",
        "do not judge candidates by kink's rules inside the campaign",
    ),
];

const COMPARE_OPTIONS: &[VerbOption] = &[
    option(
        "--only NAME",
        "compare only this implementation of the manifest (repeatable)",
    ),
    option(
        "--cache DIR",
        "the cache of the definition's baseline runs (default: .kink-flow beside FLOW.toml)",
    ),
    option(
        "--output json|text",
        "print the JSON document (default) or one line per verdict and a summary",
    ),
];

/// `kink-flow VERB --help`: the verb's usage line, what it asks, and its options.
#[must_use]
pub fn verb_help(verb: Verb) -> String {
    format!(
        "usage: kink-flow {}\n\n{}\n\nOptions:\n{}\nExit status: 0 yes, 1 a finding, 2 the \
         question could not be asked, 3 no answer (`kink-flow --help`).\nReference: \
         kink/crates/kink-flow/README.md, \"{}\"\n",
        verb.synopsis(),
        verb.summary(),
        options_text(verb.options()),
        verb.reference(),
    )
}

/// `options`, one per line, each meaning aligned after the longest spelling.
#[must_use]
pub fn options_text(options: &[VerbOption]) -> String {
    let width = options
        .iter()
        .map(|option| option.spelling.len())
        .max()
        .unwrap_or(0);
    let mut text = String::new();
    for option in options {
        text.push_str(&format!(
            "  {:width$}  {}\n",
            option.spelling, option.meaning
        ));
    }
    text
}

/// Run `body` on a thread with kink-corpus's definition stack allowance, and wait for it; `None`
/// when the thread cannot be started or `body` panics. `body` may borrow from the caller.
pub fn on_stack<T: Send>(body: impl FnOnce() -> T + Send) -> Option<T> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("kink-flow".into())
            .stack_size(DEFINITION_STACK_BYTES)
            .spawn_scoped(scope, body)
            .ok()?
            .join()
            .ok()
    })
}

/// A kink-flow verb, as both front ends spell it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Verb {
    Check,
    Coverage,
    Run,
    Report,
    Query,
    Fuzz,
    Compare,
}

impl Verb {
    /// Every verb, in the order the usage lists them.
    pub const ALL: [Self; 7] = [
        Self::Check,
        Self::Coverage,
        Self::Run,
        Self::Report,
        Self::Query,
        Self::Fuzz,
        Self::Compare,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Coverage => "coverage",
            Self::Run => "run",
            Self::Report => "report",
            Self::Query => "query",
            Self::Fuzz => "fuzz",
            Self::Compare => "compare",
        }
    }

    /// Why `name` is no verb when a verb of an earlier kink-flow had that name, with the verb that
    /// replaced it: `results`, which `coverage` replaced.
    #[must_use]
    pub fn retired(name: &str) -> Option<String> {
        (name == "results").then(|| {
            "`results` is no longer a verb: `coverage` replaced it, and lists the same programs \
             and rules with each obligation covered or open and a target for each open one"
                .to_owned()
        })
    }

    /// The verb spelled `name`.
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|verb| verb.as_str() == name)
    }

    /// `kink-flow <verb>`'s usage line after `kink-flow`: the verb, its operands and its
    /// options, as [`USAGE`] lists it.
    #[must_use]
    pub const fn synopsis(self) -> &'static str {
        match self {
            Self::Check => "check FLOW.toml [--mutations MUTATIONS] [--cache DIR]",
            Self::Coverage => {
                "coverage FLOW.toml [--tier 1|2] [--depth N] [--verify] [--lock FILE \
                 [--locked]] [--cache DIR] [--output json|text|verdicts]"
            }
            Self::Run => {
                "run FLOW.toml MUTATIONS [--only ID]... [--verify] [--full] [--lock FILE \
                 [--locked]] [--compile-workers N] [--no-memo] [--progress] [--cache DIR] [--output \
                 json|verdicts]"
            }
            Self::Report => "report FLOW.toml [--cache DIR] [--output json|verdicts]",
            Self::Query => "query FLOW.toml PATTERNS.toml [--only ID]... [--verify] [--cache DIR]",
            Self::Fuzz => {
                "fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations \
                 MUTATIONS | --matched RULE | --fired RULE | --refuted RULE | --cover ITEM | \
                 --pattern ID --patterns PATTERNS.toml) [--cases N | --work W] [--seed S] [--max-work N] \
                 [--time-limit-ms T] [--stack-stops N] [--open-stops N] \
                 [--assume-joined NAME]... [--one-path] [--cache DIR] [--no-confirm] \
                 [--no-filter]"
            }
            Self::Compare => {
                "compare FLOW.toml [--only NAME]... [--cache DIR] [--output json|text]"
            }
        }
    }

    /// What the verb asks, in one line, as its help states it.
    #[must_use]
    pub const fn summary(self) -> &'static str {
        match self {
            Self::Check => {
                "Whether every verdict the corpus promises is possible, before any mutant runs; \
                 with --mutations, also each mutation's resolution, shown before and after."
            }
            Self::Coverage => {
                "What the corpus covers of the obligations the specification states (its rules, \
                 the requirements of their conditions), each covered or open with a target, and \
                 each program's baseline class and expectation."
            }
            Self::Run => {
                "Each mutation's verdict: is there a program of the corpus whose result the \
                 mutation changes?"
            }
            Self::Report => {
                "The last run's stored document (or its verdicts), as that run printed it."
            }
            Self::Query => {
                "Whether each program reaches a state that matches each pattern of the list. \
                 PATTERNS.toml holds [[pattern]] tables, each an `id`, a `pattern` written as a \
                 rule's left-hand side (pattern = \"<k> s ( s ( zero ) ) ~> _ </k>\") and \
                 optionally `programs`, the programs claimed to hit it. Each row of a pattern and \
                 a program is `hit` (a run reaches a matching state, shown), `no` (no run does: \
                 the program's whole state space was explored within the budget, so a claim of it \
                 is refuted) or `unknown` with its cause (a bounded or open run is never `no`)."
            }
            Self::Fuzz => {
                "Hole values of a template whose program is a witness of the job: it kills a \
                 mutation, matches or fires a rule, or hits a pattern; kink confirms it."
            }
            Self::Compare => {
                "Whether each [[implementation]] of the manifest ends as the definition does on \
                 every program, under each of its views: equal, different (with the first \
                 difference), could-not-apply or not-compared; only a required view decides the \
                 exit status."
            }
        }
    }

    /// The verb's own options, which its help lists; its operands are not among them.
    #[must_use]
    pub const fn options(self) -> &'static [VerbOption] {
        match self {
            Self::Check => CHECK_OPTIONS,
            Self::Coverage => COVERAGE_OPTIONS,
            Self::Run => RUN_OPTIONS,
            Self::Report => REPORT_OPTIONS,
            Self::Query => QUERY_OPTIONS,
            Self::Fuzz => FUZZ_OPTIONS,
            Self::Compare => COMPARE_OPTIONS,
        }
    }

    /// The section of kink-flow's README that states the verb.
    const fn reference(self) -> &'static str {
        match self {
            Self::Check => "kink-flow check",
            Self::Coverage => "kink-flow coverage",
            Self::Run => "kink-flow run",
            Self::Report => "kink-flow report",
            Self::Query => "Checking a pattern",
            Self::Fuzz => "Killing a survivor with fuzz",
            Self::Compare => "Comparing implementations: kink-flow compare",
        }
    }

    /// The operands `kink-flow <verb>` takes before its options.
    pub const fn operands(self) -> &'static str {
        match self {
            Self::Check | Self::Coverage | Self::Report | Self::Compare => "FLOW.toml",
            Self::Run => "FLOW.toml MUTATIONS.toml",
            Self::Query => "FLOW.toml PATTERNS.toml",
            Self::Fuzz => "FLOW.toml TEMPLATES.toml",
        }
    }

    /// The document of this verb for a manifest that does not decode: the specification refused
    /// at stage `manifest` with the error, under the verb's schema (`fuzz`: its input refusal).
    /// A run's document also names its schedule, which only the parsed command knows
    /// ([`FlowCommand::manifest_refused`]).
    #[must_use]
    pub fn manifest_refused(self, error: &ManifestError) -> Value {
        let schema = match self {
            Self::Check => return manifest_refused(error),
            Self::Fuzz => return crate::fuzz::input_refused("FLOW.toml", error),
            Self::Coverage => crate::coverage::COVERAGE_SCHEMA,
            Self::Run => crate::report::RUN_SCHEMA,
            Self::Report => crate::report::MISSING_SCHEMA,
            Self::Query => crate::query::QUERY_SCHEMA,
            Self::Compare => crate::compare::COMPARE_SCHEMA,
        };
        // Under the Z3 profile the document names the build (`crate::with_z3_build`), as every
        // document of every verb does; a refused `coverage` or `run` document is also rendered
        // (`--output verdicts`), and its rendering names it.
        let mut document = manifest_refused(error);
        document["schema"] = json!(schema);
        document
    }

    /// What the thread that runs the verb is named in a panic's message.
    const fn task(self) -> &'static str {
        match self {
            Self::Check => "admission",
            Self::Coverage => "coverage",
            Self::Run => "run",
            Self::Report => "report",
            Self::Query => "query",
            Self::Fuzz => "fuzz",
            Self::Compare => "compare",
        }
    }
}

/// How a front end spells its commands in the next steps documents give ("run `kink-flow coverage
/// --verify`", "run `krs kink coverage --verify`"). A front end implements it with whatever
/// selects the corpus it runs on (a package path, a definition facet), so that a next step
/// reproduces the step for that corpus; kink-flow's own is [`KinkFlowSpelling`]. The texts a
/// document appends, such as ` --verify` or ` --only ID`, are the verb's own options, so both
/// methods end where the verb's options may start.
pub trait CommandSpelling: Sync {
    /// The command that runs `verb` on this corpus, its operands and selection included
    /// (`kink-flow run FLOW.toml MUTATIONS.toml`; `krs kink run --definition main`).
    fn command(&self, verb: Verb) -> String;

    /// The command that runs `verb`, as a text that names it in passing gives it (`kink-flow
    /// run`); the front end's selection is part of it as of [`Self::command`]. By default
    /// [`Self::command`].
    fn verb(&self, verb: Verb) -> String {
        self.command(verb)
    }

    /// The command that runs `run` on this corpus over the mutation list at `mutations`, with the
    /// cache directory `cache` when one was named, so that the run judges the list another
    /// command (`fuzz --kill`) read and writes the document that command reads. By default
    /// [`Self::command`] of `run` with `--mutations` and `--cache`.
    fn run_list(&self, mutations: &Path, cache: Option<&Path>) -> String {
        format!(
            "{} --mutations {}{}",
            self.command(Verb::Run),
            shell_word(&mutations.display().to_string()),
            cache_option(cache)
        )
    }
}

/// ` --cache DIR` for a named cache directory, empty otherwise.
#[must_use]
pub fn cache_option(cache: Option<&Path>) -> String {
    cache.map_or_else(String::new, |cache| {
        format!(" --cache {}", shell_word(&cache.display().to_string()))
    })
}

/// `word` as a shell reads it back: unchanged when it has no character a shell treats
/// specially, single-quoted otherwise.
#[must_use]
pub fn shell_word(word: &str) -> String {
    let plain = !word.is_empty()
        && word
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_./:=@+,%".contains(c));
    if plain {
        word.to_owned()
    } else {
        format!("'{}'", word.replace('\'', r"'\''"))
    }
}

/// kink-flow's own spelling: `kink-flow <verb>` with the verb's operands ([`Verb::operands`]),
/// and without them where a text names the verb in passing.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct KinkFlowSpelling;

impl CommandSpelling for KinkFlowSpelling {
    fn command(&self, verb: Verb) -> String {
        format!("{} {}", self.verb(verb), verb.operands())
    }

    fn verb(&self, verb: Verb) -> String {
        format!("kink-flow {}", verb.as_str())
    }

    /// `kink-flow run FLOW.toml MUTATIONS`, the list given as `run`'s operand.
    fn run_list(&self, mutations: &Path, cache: Option<&Path>) -> String {
        format!(
            "kink-flow run FLOW.toml {}{}",
            shell_word(&mutations.display().to_string()),
            cache_option(cache)
        )
    }
}

/// What a command prints.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OutputFormat {
    /// The JSON document.
    #[default]
    Json,
    /// The deterministic rendering of a `coverage` or `run` document ([`crate::verdicts`]).
    Verdicts,
    /// The summary of a `coverage` document for a reader ([`crate::coverage::text`]).
    Text,
}

/// The files a verb reads besides the manifest, as the front end finds them: kink-flow's
/// operands (`run`'s mutation list, `query`'s patterns, `fuzz`'s templates), or a front end's
/// layout. A verb's own flag (`--mutations`, `--patterns`) takes precedence over a file given
/// here.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CommandFiles {
    pub mutations: Option<PathBuf>,
    pub patterns: Option<PathBuf>,
    pub templates: Option<PathBuf>,
}

/// The ids a list holds, as a usage error names them: the first few, and how many more.
fn ids<'a>(ids: impl Iterator<Item = &'a str>) -> String {
    const SHOWN: usize = 6;
    let ids = ids.collect::<Vec<_>>();
    match ids.len() {
        0 => "it has none".to_owned(),
        count if count <= SHOWN => format!("it has {}", ids.join(", ")),
        count => format!(
            "it has {}, and {} more",
            ids[..SHOWN].join(", "),
            count - SHOWN
        ),
    }
}

/// One parsed command ([`FlowCommand::parse`]).
#[derive(Clone, Debug)]
pub enum FlowCommand {
    Check(CheckOptions),
    Coverage {
        options: CoverageOptions,
        output: OutputFormat,
    },
    Run {
        mutations: PathBuf,
        options: RunOptions,
        mode: RunMode,
        output: OutputFormat,
        /// `--progress`: a line on stderr as the run passes each program's baseline and each
        /// mutation ([`FrontEnd::progress`]), which the command line also prints when stderr is
        /// a terminal.
        progress: bool,
    },
    Report {
        options: ReportOptions,
        output: OutputFormat,
    },
    Query {
        patterns: PathBuf,
        options: QueryOptions,
    },
    Fuzz {
        templates: PathBuf,
        request: FuzzRequest,
    },
    Compare {
        options: crate::compare::CompareOptions,
        output: OutputFormat,
    },
}

impl FlowCommand {
    /// Parse `verb`'s `options` exactly as `kink-flow <verb>` does, with the files `files` gives:
    /// each file must exist, and each id `--only`, `--kill`, `--pattern` and `--template` names
    /// must be one of its list when the list decodes (a list that does not decode is the
    /// command's refusal, not a usage error). The error is the usage message.
    pub fn parse(verb: &str, files: CommandFiles, options: &[String]) -> Result<Self, String> {
        let verb = Verb::parse(verb).ok_or_else(|| {
            Verb::retired(verb).unwrap_or_else(|| format!("unknown command {verb:?}"))
        })?;
        let not_found = |path: &Path| format!("{} is not a file or directory", path.display());
        let not_file = |path: &Path| format!("{} is not a file", path.display());
        match verb {
            Verb::Check => {
                let mut options = check_options(options)?;
                options.mutations = options.mutations.or(files.mutations);
                if let Some(list) = options.mutations.as_ref().filter(|list| !list.exists()) {
                    return Err(not_found(list));
                }
                Ok(Self::Check(options))
            }
            Verb::Coverage => {
                let (options, output) = coverage_options(options)?;
                Ok(Self::Coverage { options, output })
            }
            Verb::Run => {
                let mutations = files.mutations.ok_or("run needs a mutation list")?;
                if !mutations.exists() {
                    return Err(not_found(&mutations));
                }
                let (options, mode, output, progress) = run_options(options)?;
                if let Ok(list) = MutationList::read(&mutations)
                    && let Some(id) = options
                        .only
                        .iter()
                        .find(|id| !list.mutations.iter().any(|m| &m.id == *id))
                {
                    return Err(format!(
                        "--only {id}: no mutation of {} has this id ({})",
                        mutations.display(),
                        ids(list.mutations.iter().map(|m| m.id.as_str()))
                    ));
                }
                Ok(Self::Run {
                    mutations,
                    options,
                    mode,
                    output,
                    progress,
                })
            }
            Verb::Report => {
                let (options, output) = report_options(options)?;
                Ok(Self::Report { options, output })
            }
            Verb::Query => {
                let patterns = files.patterns.ok_or("query needs a pattern list")?;
                if !patterns.is_file() {
                    return Err(not_file(&patterns));
                }
                let options = query_options(options)?;
                if let Ok(list) = PatternList::read(&patterns)
                    && let Some(id) = options
                        .only
                        .iter()
                        .find(|id| !list.patterns.iter().any(|p| &p.id == *id))
                {
                    return Err(format!(
                        "--only {id}: no pattern of {} has this id ({})",
                        patterns.display(),
                        ids(list.patterns.iter().map(|p| p.id.as_str()))
                    ));
                }
                Ok(Self::Query { patterns, options })
            }
            Verb::Fuzz => {
                let templates = files
                    .templates
                    .clone()
                    .ok_or("fuzz needs a template list")?;
                if !templates.is_file() {
                    return Err(not_file(&templates));
                }
                let request = fuzz_options(options, &files)?;
                match &request.job {
                    FuzzJobRequest::Kill {
                        mutations: list, ..
                    } if !list.exists() => return Err(not_found(list)),
                    FuzzJobRequest::Pattern { patterns: file, .. } if !file.is_file() => {
                        return Err(not_file(file));
                    }
                    _ => {}
                }
                if let Ok(list) = TemplateList::read(&templates)
                    && list.get(&request.template).is_none()
                {
                    return Err(format!(
                        "--template {}: no template of {} has this id ({})",
                        request.template,
                        templates.display(),
                        ids(list.templates.iter().map(|t| t.id.as_str()))
                    ));
                }
                if let FuzzJobRequest::Kill {
                    mutation,
                    mutations,
                } = &request.job
                    && let Ok(list) = MutationList::read(mutations)
                    && !list.mutations.iter().any(|m| &m.id == mutation)
                {
                    // The list may be a front end's default, not the one the last run judged:
                    // the message names it, and the option that names another.
                    return Err(format!(
                        "--kill {mutation}: no mutation of {} has this id ({}); --mutations \
                         names the list to read",
                        mutations.display(),
                        ids(list.mutations.iter().map(|m| m.id.as_str()))
                    ));
                }
                if let FuzzJobRequest::Pattern { id, patterns } = &request.job
                    && let Ok(list) = PatternList::read(patterns)
                    && !list.patterns.iter().any(|p| &p.id == id)
                {
                    return Err(format!(
                        "--pattern {id}: no pattern of {} has this id ({})",
                        patterns.display(),
                        ids(list.patterns.iter().map(|p| p.id.as_str()))
                    ));
                }
                Ok(Self::Fuzz { templates, request })
            }
            Verb::Compare => {
                let (options, output) = compare_options(options)?;
                Ok(Self::Compare { options, output })
            }
        }
    }

    /// The command's verb.
    #[must_use]
    pub const fn verb(&self) -> Verb {
        match self {
            Self::Check(_) => Verb::Check,
            Self::Coverage { .. } => Verb::Coverage,
            Self::Run { .. } => Verb::Run,
            Self::Report { .. } => Verb::Report,
            Self::Query { .. } => Verb::Query,
            Self::Fuzz { .. } => Verb::Fuzz,
            Self::Compare { .. } => Verb::Compare,
        }
    }

    /// The lock the command reads and writes (`--lock FILE`), for `run` and `coverage`.
    #[must_use]
    pub fn lock(&self) -> Option<&Path> {
        match self {
            Self::Coverage { options, .. } => options.lock.as_deref(),
            Self::Run { options, .. } => options.lock.as_deref(),
            _ => None,
        }
    }

    /// Name the old file a front end kept the command's lock in before version 24 (krs's
    /// `<corpus>/verdicts.lock` and `<corpus>/coverage.lock`), beside the record the command's
    /// `--lock` names ([`crate::lock::Lock::adopt_legacy`]): read while the record has no section
    /// for the command, and refused under `--locked` while it is there. A command with no lock, or
    /// another verb, is left as it is.
    pub fn set_legacy_lock(&mut self, path: PathBuf) {
        match self {
            Self::Coverage { options, .. } if options.lock.is_some() => {
                options.legacy_lock = Some(path);
            }
            Self::Run { options, .. } if options.lock.is_some() => {
                options.legacy_lock = Some(path);
            }
            _ => {}
        }
    }

    /// The command's document for a manifest that does not decode ([`Verb::manifest_refused`]).
    /// A run's names the command's `schedule` and a null `matrix`, as every run document does,
    /// so that a refusal under `--full` reads as a full run's, whichever input was refused
    /// ([`mutation_list_refused`]).
    #[must_use]
    pub fn manifest_refused(&self, error: &ManifestError) -> Value {
        let mut document = self.verb().manifest_refused(error);
        if let Self::Run { options, .. } = self {
            document["schedule"] = json!(crate::search::schedule_name(options.schedule));
            document["matrix"] = Value::Null;
            document["lock"] = refused_lock(options);
        }
        document
    }

    /// What the command prints: `--output` of `coverage`, `run` and `report`, the JSON document
    /// otherwise.
    #[must_use]
    pub const fn output(&self) -> OutputFormat {
        match self {
            Self::Coverage { output, .. }
            | Self::Run { output, .. }
            | Self::Report { output, .. }
            | Self::Compare { output, .. } => *output,
            _ => OutputFormat::Json,
        }
    }

    /// Whether a command line prints the command's progress on stderr ([`FrontEnd::progress`]):
    /// a `run` given `--progress`, or one whose stderr is a terminal, where someone watches a run
    /// that can take minutes. A run whose stderr is read by a program (a CI step, an agent, a
    /// recorded output) reports progress only when asked, so what it reads stays the refusals and
    /// notes alone.
    #[must_use]
    pub fn shows_progress(&self) -> bool {
        match self {
            Self::Run { progress, .. } => *progress || std::io::stderr().is_terminal(),
            _ => false,
        }
    }
}

/// What a front end adds to a command ([`dispatch`]).
pub struct FrontEnd<'a> {
    /// How next steps spell the front end's commands.
    pub spelling: &'a dyn CommandSpelling,
    /// The mutations the front end refused before kink-flow resolved them, by id, each with the
    /// refusal its row shows (reason [`crate::InvalidReason::External`] for a check of the front
    /// end's own). `run` gives each the row of a mutation that does not resolve and runs nothing
    /// for it; `check --mutations` adds the refusal to its row; a `fuzz` kill job of one is
    /// refused. An id that is not in the list is ignored.
    pub refused: BTreeMap<String, InvalidMutation>,
    /// Applied to the document before it is returned, and, for `run`, before each write of the
    /// report, so that `report` prints what `run` printed. It must be idempotent: `report`
    /// applies it again to the document `run` stored.
    pub annotate: Option<&'a (dyn Fn(&mut Value) + Sync)>,
    /// Where `run` reports its progress, one line at a time, without a trailing newline: before
    /// the baseline update, how many programs and mutations the run has; as the specification's
    /// admission starts, and as the baseline runner's preparation starts; as each program's
    /// baseline row is decided, its place, its id, its class and whether its record was stored
    /// ([`crate::results::update_results`]); before the list is resolved, how many mutations it
    /// has; then, as each selected mutation's row is decided, its place, its id and its status
    /// ([`crate::search::run_front`]).
    /// The lines are functions of the corpus and the cache, never of time, and nothing else
    /// reads them; the document is the same with or without them. `None` reports nothing.
    pub progress: Option<&'a (dyn Fn(&str) + Sync)>,
    /// The condition flips the front end derives from the definition's source, which `coverage`
    /// runs as its flips family under tier 2 ([`crate::flips`]), or why it derives none.
    /// kink-flow's own front end reads K alone, so it derives none
    /// ([`crate::flips::DERIVES_NONE`]).
    pub derived: Derived<'a>,
    /// How the front end resolves the function and the cells a `[[coverage.invariant]]` names to
    /// the definition's KORE symbol and cell paths, which `coverage` checks an argued item's
    /// invariant with ([`crate::coverage::InvariantResolver`]); `None` for a front end that
    /// resolves none, whose corpus `coverage` refuses where it declares an invariant
    /// (`invariant-unsupported-front-end`). kink-flow's own front end reads K, so it resolves the
    /// function by its K label and the cells by their K names
    /// ([`crate::coverage::KInvariants`]).
    pub invariants: Option<&'a (dyn crate::coverage::InvariantResolver + Sync)>,
    /// The front end's cell vocabulary, in which `compare` gives an implementation the start and
    /// reads its end, and the comparison of an end under a view ([`crate::compare::Vocabulary`]);
    /// `None` for a front end with none, whose corpus `compare` refuses (stage
    /// `implementation`, reason `unsupported-front-end`). kink-flow's own front end reads K
    /// terms, which have no such vocabulary.
    pub implementations: Option<&'a (dyn crate::compare::Vocabulary + Sync)>,
}

impl Default for FrontEnd<'_> {
    /// kink-flow's own: its spelling, nothing refused, no annotation, invariants named in K.
    fn default() -> Self {
        Self {
            spelling: &KinkFlowSpelling,
            refused: BTreeMap::new(),
            annotate: None,
            progress: None,
            derived: Derived::default(),
            invariants: Some(&crate::coverage::KInvariants),
            implementations: None,
        }
    }
}

impl std::fmt::Debug for FrontEnd<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FrontEnd")
            .field("spelling", &self.spelling.command(Verb::Run))
            .field("refused", &self.refused)
            .field("annotate", &self.annotate.map(|_| ".."))
            .field("progress", &self.progress.map(|_| ".."))
            .field("derived", &self.derived)
            .field("invariants", &self.invariants.map(|_| ".."))
            .field("implementations", &self.implementations.map(|_| ".."))
            .finish()
    }
}

impl FrontEnd<'_> {
    pub(crate) fn annotated(&self, mut document: Value) -> Value {
        if let Some(annotate) = self.annotate {
            annotate(&mut document);
        }
        document
    }

    /// Add each refused mutation's refusal to its row of `checked`.
    fn refuse(&self, checked: &mut CorpusMutationCheck) {
        let Some(mutations) = checked.mutations.as_mut() else {
            return;
        };
        for row in &mut mutations.rows {
            if let Some(refusal) = self.refused.get(&row.id) {
                row.findings.push(Finding::refused(
                    refusal.reason.as_str(),
                    refusal.edit,
                    None,
                    refusal.detail.clone(),
                    Some(refusal.reason.next_step().to_owned()),
                ));
            }
        }
    }
}

/// Run `command` on `manifest` on the large stack kink's definitions need ([`on_stack`];
/// `report`, which loads no definition, on the calling thread): the document and the exit status,
/// or the message of the command's thread panicking.
pub fn dispatch(
    manifest: FlowManifest,
    command: FlowCommand,
    front: FrontEnd<'_>,
) -> Result<(Value, u8), String> {
    let verb = command.verb();
    if verb == Verb::Report {
        return Ok(run_command(&manifest, &command, &front));
    }
    on_stack(|| run_command(&manifest, &command, &front))
        .ok_or_else(|| format!("the {} thread panicked", verb.task()))
}

/// Run `command` on `manifest` on the calling thread, which must have the stack kink's
/// definitions need ([`dispatch`] provides it): the document and the exit status of
/// `kink-flow <verb>`.
pub fn run_command(
    manifest: &FlowManifest,
    command: &FlowCommand,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let (document, status) = match command {
        FlowCommand::Check(options) => match &options.mutations {
            None => check_admission(manifest, options.cache.as_deref()),
            Some(path) => {
                let mut checked = check_corpus_mutations(
                    manifest,
                    MutationList::read(path),
                    options.cache.as_deref(),
                );
                front.refuse(&mut checked);
                check_mutations_document(&checked, front.spelling)
            }
        },
        FlowCommand::Coverage { options, .. } => {
            let (document, ok) = crate::coverage::command(manifest, options, front);
            let status = completed(coverage_status(&document), ok);
            (document, status)
        }
        FlowCommand::Run {
            mutations,
            options,
            mode,
            ..
        } => {
            // `run_front` annotates every document it writes and returns.
            return match MutationList::read(mutations) {
                Err(error) => {
                    let mut document = mutation_list_refused(&error.to_string(), options.schedule);
                    document["lock"] = refused_lock(options);
                    (front.annotated(document), EXIT_UNASKED)
                }
                Ok(list) => {
                    let (document, ok) =
                        crate::search::run_front(manifest, &list, options, *mode, front);
                    let status = completed(run_status(&document), ok);
                    (document, status)
                }
            };
        }
        FlowCommand::Report { options, .. } => {
            let (document, ok) = crate::report::report_spelled(manifest, options, front.spelling);
            let status = if ok {
                run_status(&document)
            } else {
                EXIT_UNASKED
            };
            (document, status)
        }
        FlowCommand::Query { patterns, options } => match PatternList::read(patterns) {
            Err(error) => (
                crate::query::named(manifest, pattern_list_refused(&error)),
                EXIT_UNASKED,
            ),
            Ok(list) => {
                let (document, ok) = crate::query::query(manifest, &list, options);
                let status = completed(query_status(&document), ok);
                (document, status)
            }
        },
        FlowCommand::Fuzz { templates, request } => {
            fuzz_command(manifest, templates, request, front)
        }
        FlowCommand::Compare { options, .. } => {
            let document = crate::compare::command(
                manifest,
                options,
                front
                    .implementations
                    .map(|vocabulary| vocabulary as &dyn crate::compare::Vocabulary),
            );
            let status = crate::compare::compare_status(&document);
            (document, status)
        }
    };
    let mut document = front.annotated(document);
    if matches!(command, FlowCommand::Coverage { .. }) {
        // A front end's annotation may rebuild the items it adds, each with the status its
        // records give (krs's field values); deriving again restores what the derived part
        // decides of them, such as an argued item's status. Both steps are idempotent.
        crate::coverage::derive(&mut document, front.spelling);
    }
    (document, status)
}

/// The status of two parts whose statuses are `left` and `right`: the one that comes first of
/// [`EXIT_UNASKED`], [`EXIT_NO`], [`EXIT_UNANSWERED`] and [`EXIT_YES`]. A part that could not be
/// asked leaves the whole answer incomplete, a finding stands whatever else has no answer, and
/// the whole is a yes only when every part is. A status that is none of the four counts as
/// [`EXIT_UNASKED`].
#[must_use]
pub const fn exit_join(left: u8, right: u8) -> u8 {
    const fn rank(status: u8) -> u8 {
        match status {
            EXIT_YES => 0,
            EXIT_UNANSWERED => 1,
            EXIT_NO => 2,
            _ => 3,
        }
    }
    const fn normal(status: u8) -> u8 {
        match status {
            EXIT_YES | EXIT_NO | EXIT_UNASKED | EXIT_UNANSWERED => status,
            _ => EXIT_UNASKED,
        }
    }
    let (left, right) = (normal(left), normal(right));
    if rank(left) >= rank(right) {
        left
    } else {
        right
    }
}

/// `status`, the status a command's document gives, joined with [`EXIT_UNASKED`] when the command
/// reports a failure (`ok` false) its status does not show. The status functions read every
/// failure a document records (a refusal, a failed run or search, and a record or report the
/// command could not write, a row's `cache_error`), so `ok` is false with [`EXIT_NO`] only for
/// the finding itself (a `--verify` mismatch), and the join is a guard for a failure a document
/// would not record.
const fn completed(status: u8, ok: bool) -> u8 {
    if ok || matches!(status, EXIT_NO | EXIT_UNASKED) {
        status
    } else {
        exit_join(status, EXIT_UNASKED)
    }
}

/// Whether a document's specification is refused (`spec.outcome`).
fn spec_refused(document: &Value) -> bool {
    document["spec"]["outcome"] == "refused"
}

/// The status of a row's expectation: a case's (`crate::expect`) or a mutation's
/// (`crate::report::mutation_expectation`). Met [`EXIT_YES`], unmet [`EXIT_NO`] (a finding: about
/// the specification against the reference the case was written from, or about the corpus or the
/// definition against what the mutation claims of them), inconclusive [`EXIT_UNANSWERED`];
/// [`EXIT_YES`] for a row without one.
fn expectation_status(row: &Value) -> u8 {
    match row["expectation"]["verdict"].as_str() {
        Some("unmet") => EXIT_NO,
        Some("inconclusive") => EXIT_UNANSWERED,
        _ => EXIT_YES,
    }
}

/// Whether a row reports a record the command could not write (`cache_error`), which fails the
/// command ([`EXIT_UNASKED`]: fix the cache directory): every `cache_error` but
/// [`crate::results::RESULT_CACHE_NO_BUILD`], which says only that no result record is written
/// when kink's build identity is unknown, and leaves the answer and the command whole.
fn record_unwritten(row: &Value) -> bool {
    row["cache_error"]
        .as_str()
        .is_some_and(|error| error != crate::results::RESULT_CACHE_NO_BUILD)
}

/// [`EXIT_UNASKED`] for a row that reports an unwritten record ([`record_unwritten`]), else
/// [`EXIT_YES`].
fn record_status(row: &Value) -> u8 {
    if record_unwritten(row) {
        EXIT_UNASKED
    } else {
        EXIT_YES
    }
}

/// The status of a program's baseline row of a `coverage` document by its class
/// ([`crate::results::ResultClass`]): `comparable` and `comparable-prefix` [`EXIT_YES`] (a
/// prefix program answers what the baseline computes for the declared observation, up to its
/// horizons, and some channel of it kept an element within its budget: one that kept none is
/// `unknown`, since it observed nothing); `timeout` and `unknown`
/// [`EXIT_UNANSWERED`], since the run has no end kink compares; `refused` and `error`
/// [`EXIT_UNASKED`]; joined with [`EXIT_UNASKED`] for a result record it could not write.
fn program_status(row: &Value) -> u8 {
    let class = match row["class"].as_str() {
        Some("comparable" | "comparable-prefix") => EXIT_YES,
        Some("timeout" | "unknown") => EXIT_UNANSWERED,
        _ => EXIT_UNASKED,
    };
    exit_join(class, record_status(row))
}

/// The status of a program's baseline row of a `run` or `query` document, whose questions are
/// about the mutations and the patterns: [`EXIT_UNASKED`] for a program refused or failed on the
/// baseline (whose kills or answers could not be asked) or a result record it could not write,
/// else [`EXIT_YES`]. A program that times out or is unknown on the baseline only cannot kill or
/// hit: the rows of the mutations and the patterns already say so.
fn baseline_status(row: &Value) -> u8 {
    match row["class"].as_str() {
        Some("refused" | "error") => EXIT_UNASKED,
        _ => record_status(row),
    }
}

/// The exit status of a `coverage` document: the corpus ran, every program is comparable and
/// every expectation is met. The join of each program's class ([`program_status`]: a timeout or
/// unknown program covers nothing, so the answer is incomplete) and expectation
/// ([`expectation_status`]), [`EXIT_NO`] for a `--verify` mismatch, [`EXIT_UNANSWERED`] for a
/// flip the kill search gave no verdict (`unknown`), [`EXIT_UNASKED`] for one whose search ended
/// in an error (`kink_status` `error`: a corpus error, a failed run or an unwritten record),
/// [`EXIT_NO`] for a needless argument (`summary.needless_arguments`: a `[[coverage.argued]]`
/// entry whose item a program covers or that is no obligation, which would turn the item's next
/// regression into `argued` instead of `open`), [`EXIT_NO`] for a refuted argument
/// (`summary.failed_arguments`: an invariant a check showed does not exclude the item, which is
/// open again), [`EXIT_UNANSWERED`] for an argued item whose
/// argument rests on an invariant no check decided (`summary.argued_by_standing.unchecked`: the
/// corpus is done only by a claim nothing confirmed, so the answer is inconclusive, as an
/// `unknown` program's is), and [`EXIT_UNASKED`] for a refused
/// specification. An open obligation is no finding: coverage states the gap, and the corpus's
/// author decides what to write; nor is a refused flip, which is a disagreement between the
/// flips' generator and an admission, not a fault of the corpus.
#[must_use]
pub fn coverage_status(document: &Value) -> u8 {
    if spec_refused(document) || document["lock"]["outcome"] == "refused" {
        return EXIT_UNASKED;
    }
    let programs = document["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|row| exit_join(program_status(row), expectation_status(row)))
        .fold(EXIT_YES, exit_join);
    let flips = document["families"]["flips"]["items"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|item| {
            if item["kink_status"] == "error" {
                EXIT_UNASKED
            } else if item["status"] == crate::flips::UNKNOWN {
                EXIT_UNANSWERED
            } else {
                EXIT_YES
            }
        })
        .fold(EXIT_YES, exit_join);
    let needless = if document["summary"]["needless_arguments"]
        .as_array()
        .is_some_and(|needless| !needless.is_empty())
    {
        EXIT_NO
    } else {
        EXIT_YES
    };
    // A refuted argument stands in for nothing, and its item is open again: a finding.
    let failed = if document["summary"]["failed_arguments"]
        .as_array()
        .is_some_and(|failed| !failed.is_empty())
    {
        EXIT_NO
    } else {
        EXIT_YES
    };
    let unchecked = if document["summary"]["argued_by_standing"]["unchecked"]
        .as_u64()
        .is_some_and(|unchecked| unchecked > 0)
    {
        EXIT_UNANSWERED
    } else {
        EXIT_YES
    };
    [
        mismatch_status(document),
        lock_status(document),
        needless,
        failed,
        unchecked,
    ]
    .into_iter()
    .fold(exit_join(programs, flips), exit_join)
}

/// The status of a document's lock: [`EXIT_NO`] when `--locked` found the command would change
/// it (`stale`: a stored record that differs from the live value, as `--verify` reports one),
/// [`EXIT_UNANSWERED`] when `--locked` found no difference but some entry rests on a run the
/// clock stopped (`undecided`: not decided on this host, [`crate::clock`]), [`EXIT_UNASKED`] when
/// it could not be written, else [`EXIT_YES`].
fn lock_status(document: &Value) -> u8 {
    match document["lock"]["status"].as_str() {
        Some("stale") => EXIT_NO,
        Some("undecided") => EXIT_UNANSWERED,
        Some("not-written") if document["lock"]["reason"] == "write-failed" => EXIT_UNASKED,
        _ => EXIT_YES,
    }
}

/// [`EXIT_NO`] when a document's `mismatches` lists a stored record that differs from the live
/// value (`--verify`), else [`EXIT_YES`].
fn mismatch_status(document: &Value) -> u8 {
    if document["mismatches"]
        .as_array()
        .is_some_and(|mismatches| !mismatches.is_empty())
    {
        EXIT_NO
    } else {
        EXIT_YES
    }
}

/// The status of a mutation of a run document by its `status` and `reason`: `run` asks each
/// mutation's verdict, so every verdict is an answer ([`EXIT_YES`]: `killed`, `survived`,
/// `equivalent`, `unkillable`), whatever verdict the mutation expects, which [`run_status`] joins
/// apart ([`expectation_status`]); `timeout` and `unknown` have none ([`EXIT_UNANSWERED`]);
/// `invalid-mutation` and `not-admitted` name a mutation its author must fix before it is judged
/// ([`EXIT_UNASKED`]); `error` is a finding ([`EXIT_NO`]) when it reports a stored record
/// `--verify` found different from the live one (`outcome-mismatch`, `resolution-mismatch`), and
/// otherwise a failure that left the mutation unjudged ([`EXIT_UNASKED`]: a corpus error, no
/// comparable program, a failed run).
#[must_use]
pub fn mutation_exit_status(status: &str, reason: Option<&str>) -> u8 {
    match status {
        "killed" | "survived" | "equivalent" | crate::search::UNKILLABLE => EXIT_YES,
        "timeout" | "unknown" => EXIT_UNANSWERED,
        "error"
            if reason.is_some_and(|reason| {
                reason.starts_with("outcome-mismatch:") || reason == "resolution-mismatch"
            }) =>
        {
            EXIT_NO
        }
        _ => EXIT_UNASKED,
    }
}

/// The exit status of a run document, which `run` prints and `report` prints again: the join of
/// every mutation's ([`mutation_exit_status`]) and its expectation's ([`expectation_status`]: an
/// unmet one [`EXIT_NO`], an inconclusive one [`EXIT_UNANSWERED`], checked from the row on every
/// run, with or without `--locked`) and each program's baseline row's ([`baseline_status`]),
/// [`EXIT_NO`] for a `--verify` mismatch and for a lock `--locked` found the run would change
/// (`lock.status` `stale`: a stored record that differs from the live value, as `--verify`
/// reports one), and [`EXIT_UNASKED`] for a refused specification or lock, or a record, report or
/// lock the run could not write.
#[must_use]
pub fn run_status(document: &Value) -> u8 {
    if spec_refused(document) || document["lock"]["outcome"] == "refused" {
        return EXIT_UNASKED;
    }
    let programs = document["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(baseline_status)
        .fold(EXIT_YES, exit_join);
    let mutations = document["mutations"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|row| {
            let status = mutation_exit_status(
                row["status"].as_str().unwrap_or_default(),
                row["reason"].as_str(),
            );
            exit_join(
                exit_join(status, expectation_status(row)),
                record_status(row),
            )
        })
        .fold(EXIT_YES, exit_join);
    exit_join(
        exit_join(exit_join(programs, mutations), mismatch_status(document)),
        lock_status(document),
    )
}

/// The status of one row of a query document: `query` asks whether each program reaches a state
/// that matches each pattern. `hit` and `no` answer it ([`EXIT_YES`]), except that `no` for a
/// program the pattern claims refutes the claim, a finding ([`EXIT_NO`]); `unknown` has no answer
/// ([`EXIT_UNANSWERED`]); `invalid-pattern` names a pattern its author must fix and `error` a
/// failed search ([`EXIT_UNASKED`]); joined with [`EXIT_UNASKED`] for a pattern record the row
/// says the command could not write.
fn answer_status(row: &Value) -> u8 {
    let answer = match row["answer"].as_str() {
        Some("hit") => EXIT_YES,
        Some("no") if row["claim"] == "refuted" => EXIT_NO,
        Some("no") => EXIT_YES,
        Some("unknown") => EXIT_UNANSWERED,
        _ => EXIT_UNASKED,
    };
    exit_join(answer, record_status(row))
}

/// The exit status of a query document: the join of every row's ([`answer_status`]), [`EXIT_NO`]
/// and each program's baseline row's ([`baseline_status`]), [`EXIT_NO`] for a `--verify`
/// mismatch, and [`EXIT_UNASKED`] for a refused specification.
#[must_use]
pub fn query_status(document: &Value) -> u8 {
    if spec_refused(document) {
        return EXIT_UNASKED;
    }
    let programs = document["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(baseline_status)
        .fold(EXIT_YES, exit_join);
    let rows = document["rows"]
        .as_array()
        .into_iter()
        .flatten()
        .map(answer_status)
        .fold(EXIT_YES, exit_join);
    exit_join(exit_join(programs, rows), mismatch_status(document))
}

/// The exit status of a fuzz document by its `stopped` ([`crate::fuzz`]): `fuzz` asks whether
/// the template's hole values hold a witness of its job that kink accepts. A witness kink offers
/// (`null`) or a proof that no input has one (`equivalent`: the two definitions denote one
/// theory) answers it ([`EXIT_YES`]). A search that ran its cases and ended without a witness kink
/// accepts (`budget`, `time-limit`, `cancelled`, `domain-exhausted`, `client-refused`,
/// `unconfirmed`, `assembly-mismatch`, `stack-stops`, `open-stops`) leaves the job's own
/// question, whether some input witnesses it, without an answer ([`EXIT_UNANSWERED`]): the
/// caller retries with more cases or time, or with other holes or another template;
/// `domain-exhausted` answers only that this
/// template's holes hold none. A job refused before any case (`refused`, `not-comparable`), a
/// campaign that `aborted`, and one stopped `rejected-out`, whose generated hole values mostly do
/// not read back or violate their sort, so that the template's holes must be fixed before cases
/// can be asked and more cases cannot help, could not ask ([`EXIT_UNASKED`]). A witness of a kill
/// job whose mutation expects to survive (`job.expect` `survive`) is a candidate refutation of
/// that expectation ([`crate::fuzz::refutes_survival`]): a finding ([`EXIT_NO`]) when kink's own
/// run confirmed the kill on the flow as it stands, with no premise `FLOW.toml` lacks; otherwise
/// the claim is neither refuted nor confirmed, and the job is unanswered ([`EXIT_UNANSWERED`]).
#[must_use]
pub fn fuzz_status(document: &Value) -> u8 {
    match document["stopped"].as_str() {
        None if document["stopped"].is_null() && document["job"]["expect"] == "survive" => {
            if crate::fuzz::refutes_survival(&document["program"]) {
                EXIT_NO
            } else {
                EXIT_UNANSWERED
            }
        }
        None if document["stopped"].is_null() => EXIT_YES,
        Some("equivalent") => EXIT_YES,
        Some(
            "budget" | "time-limit" | "cancelled" | "domain-exhausted" | "client-refused"
            | "unconfirmed" | "assembly-mismatch" | "stack-stops" | "open-stops",
        ) => EXIT_UNANSWERED,
        _ => EXIT_UNASKED,
    }
}

/// The `lock` of a run refused before its lock was read (its manifest or its mutation list does
/// not decode): null without `--lock`, else the lock left unwritten for reason `refused`, as a
/// run whose specification is refused gives it.
fn refused_lock(options: &RunOptions) -> Value {
    options.lock.as_deref().map_or(Value::Null, |path| {
        crate::lock::not_written(path, "refused")
    })
}

/// `fuzz` on a decoded manifest.
fn fuzz_command(
    manifest: &FlowManifest,
    templates: &Path,
    request: &FuzzRequest,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let templates = match TemplateList::read(templates) {
        Ok(templates) => templates,
        Err(error) => {
            return (
                crate::fuzz::input_refused("TEMPLATES.toml", &error),
                EXIT_UNASKED,
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
                        EXIT_UNASKED,
                    );
                }
            };
            crate::fuzz::fuzz_front(
                manifest,
                &templates,
                &request.template,
                FuzzJob::Kill {
                    list: &list,
                    mutation,
                    path: Some(mutations),
                    flip: false,
                },
                &request.options,
                front,
            )
        }
        FuzzJobRequest::Derived { mutation, list } => crate::fuzz::fuzz_derived(
            manifest,
            &templates,
            &request.template,
            mutation,
            list.as_deref(),
            &request.options,
            front,
        ),
        FuzzJobRequest::Rule { rule, fired } => crate::fuzz::fuzz_front(
            manifest,
            &templates,
            &request.template,
            FuzzJob::Rule {
                rule,
                fired: *fired,
            },
            &request.options,
            front,
        ),
        FuzzJobRequest::Refuted { rule } => crate::fuzz::fuzz_front(
            manifest,
            &templates,
            &request.template,
            FuzzJob::Refuted { rule },
            &request.options,
            front,
        ),
        FuzzJobRequest::Cover { item } => crate::fuzz::fuzz_front(
            manifest,
            &templates,
            &request.template,
            FuzzJob::Cover { item },
            &request.options,
            front,
        ),
        FuzzJobRequest::Pattern { id, patterns } => {
            let list = match PatternList::read(patterns) {
                Ok(list) => list,
                Err(error) => {
                    return (
                        crate::fuzz::input_refused("PATTERNS.toml", &error),
                        EXIT_UNASKED,
                    );
                }
            };
            crate::fuzz::fuzz_front(
                manifest,
                &templates,
                &request.template,
                FuzzJob::Pattern { list: &list, id },
                &request.options,
                front,
            )
        }
    };
    let status = completed(fuzz_status(&document), ok);
    (document, status)
}

/// [`run_command`] of `command` on the manifest at `path`, as kink-flow runs it, on the calling
/// thread; a manifest that does not decode gives the command's refusal
/// ([`FlowCommand::manifest_refused`]).
fn on_manifest(path: &Path, command: &FlowCommand) -> (Value, u8) {
    match FlowManifest::read(path) {
        Err(error) => (command.manifest_refused(&error), EXIT_UNASKED),
        Ok(manifest) => run_command(&manifest, command, &FrontEnd::default()),
    }
}

/// Options of `kink-flow check`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CheckOptions {
    /// A mutation list to resolve against the specification ([`crate::check`]).
    pub mutations: Option<PathBuf>,
    /// The cache directory whose result records decide `unmatched-rule` and `unapplied-rule`;
    /// default `<directory of FLOW.toml>/.kink-flow`. Nothing is written to it.
    pub cache: Option<PathBuf>,
}

fn check_options(args: &[String]) -> Result<CheckOptions, String> {
    let mut options = CheckOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Check, arg)?;
        match arg.as_str() {
            "--mutations" if options.mutations.is_none() => {
                let list = args.next().ok_or("--mutations needs a file or directory")?;
                options.mutations = Some(PathBuf::from(list));
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(repeated(arg)),
        }
    }
    Ok(options)
}

fn output_format(value: Option<&String>) -> Result<OutputFormat, String> {
    let value = value.ok_or("--output needs json or verdicts")?;
    match value.as_str() {
        "json" => Ok(OutputFormat::Json),
        "verdicts" => Ok(OutputFormat::Verdicts),
        _ => Err(format!("--output {value:?}: expected json or verdicts")),
    }
}

fn coverage_options(args: &[String]) -> Result<(CoverageOptions, OutputFormat), String> {
    let mut options = CoverageOptions::default();
    let mut tier = None;
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Coverage, arg)?;
        match arg.as_str() {
            "--output" if output.is_none() => {
                let value = args.next().ok_or("--output needs json, text or verdicts")?;
                output = Some(match value.as_str() {
                    "json" => OutputFormat::Json,
                    "text" => OutputFormat::Text,
                    "verdicts" => OutputFormat::Verdicts,
                    _ => {
                        return Err(format!(
                            "--output {value:?}: expected json, text or verdicts"
                        ));
                    }
                });
            }
            "--tier" if tier.is_none() => {
                let value = args.next().ok_or("--tier needs 1 or 2")?;
                tier = Some(match value.as_str() {
                    "1" => Tier::One,
                    "2" => Tier::Two,
                    _ => return Err(format!("--tier {value:?}: expected 1 or 2")),
                });
            }
            "--depth" if options.depth.is_none() => {
                let value = args.next().ok_or("--depth needs a positive integer")?;
                options.depth = Some(
                    value
                        .parse()
                        .map_err(|_| format!("--depth {value:?}: expected a positive integer"))?,
                );
            }
            "--verify" if !options.verify => options.verify = true,
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            "--lock" if options.lock.is_none() => {
                let file = args.next().ok_or("--lock needs a file")?;
                options.lock = Some(PathBuf::from(file));
            }
            "--locked" if !options.locked => options.locked = true,
            _ => return Err(repeated(arg)),
        }
    }
    options.tier = tier.unwrap_or_default();
    if options.locked {
        // `--locked` asks whether a run with the manifest's own settings writes the lock: a run
        // that computes no flip, or another depth, cannot answer it.
        if options.lock.is_none() {
            return Err("--locked compares the run with its lock: give --lock FILE".to_owned());
        }
        if options.tier == Tier::One {
            return Err(
                "--locked compares a run of the manifest's own settings with its lock, \
                        and --tier 1 runs no flip: drop one of them"
                    .to_owned(),
            );
        }
        if options.depth.is_some() {
            return Err(
                "--locked compares a run of the manifest's own settings with its lock, \
                        and --depth replaces [coverage] depth: drop one of them"
                    .to_owned(),
            );
        }
    }
    Ok((options, output.unwrap_or_default()))
}

fn run_options(args: &[String]) -> Result<(RunOptions, RunMode, OutputFormat, bool), String> {
    let mut options = RunOptions::default();
    let mut mode = RunMode::Search;
    let mut progress = false;
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Run, arg)?;
        match arg.as_str() {
            "--output" if output.is_none() => output = Some(output_format(args.next())?),
            "--verify" if mode == RunMode::Search => mode = RunMode::Verify,
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
            "--full" if options.schedule == ScheduleMode::FirstKill => {
                options.schedule = ScheduleMode::Full;
            }
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
            "--progress" if !progress => progress = true,
            "--lock" if options.lock.is_none() => {
                let file = args.next().ok_or("--lock needs a file")?;
                options.lock = Some(PathBuf::from(file));
            }
            "--locked" if !options.locked => options.locked = true,
            _ => return Err(repeated(arg)),
        }
    }
    if options.locked && options.lock.is_none() {
        return Err("--locked compares the run with its lock: give --lock FILE".to_owned());
    }
    Ok((options, mode, output.unwrap_or_default(), progress))
}

fn query_options(args: &[String]) -> Result<QueryOptions, String> {
    let mut options = QueryOptions::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Query, arg)?;
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
            _ => return Err(repeated(arg)),
        }
    }
    Ok(options)
}

fn compare_options(
    args: &[String],
) -> Result<(crate::compare::CompareOptions, OutputFormat), String> {
    let mut options = crate::compare::CompareOptions::default();
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Compare, arg)?;
        match arg.as_str() {
            "--only" => {
                let name = args.next().ok_or("--only needs an implementation's name")?;
                if !options.only.contains(name) {
                    options.only.push(name.clone());
                }
            }
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            "--output" if output.is_none() => {
                let value = args.next().ok_or("--output needs json or text")?;
                output = Some(match value.as_str() {
                    "json" => OutputFormat::Json,
                    "text" => OutputFormat::Text,
                    _ => return Err(format!("--output {value:?}: expected json or text")),
                });
            }
            _ => return Err(repeated(arg)),
        }
    }
    Ok((options, output.unwrap_or_default()))
}

/// The `--output text` rendering of a document: a `compare` document's lines
/// ([`crate::compare::text`]), else a `coverage` document's summary ([`crate::coverage::text`]).
///
/// # Errors
///
/// When the document has no text rendering.
pub fn text(document: &Value) -> Result<String, String> {
    if document["schema"] == crate::compare::COMPARE_SCHEMA {
        crate::compare::text(document)
    } else {
        crate::coverage::text(document)
    }
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
    /// `--kill MUTATION --mutations MUTATIONS.toml`, or `--kill MUTATION` where the front end's
    /// list holds the mutation.
    Kill {
        mutation: String,
        mutations: PathBuf,
    },
    /// `--kill FLIP` where no list given holds the id: a condition flip the front end derives
    /// ([`FrontEnd::derived`]), resolved when the command runs. `list` is the front end's list
    /// that does not hold the id, which a refusal names when no derived flip has it either.
    Derived {
        mutation: String,
        list: Option<PathBuf>,
    },
    /// `--matched RULE` (`fired` false) or `--fired RULE`: a rule's `matched_by` or `fired_by`.
    Rule { rule: String, fired: bool },
    /// `--refuted RULE`: the requirement that the rule's condition is refuted.
    Refuted { rule: String },
    /// `--cover ITEM`: the coverage obligation whose id is `ITEM`.
    Cover { item: String },
    /// `--pattern ID --patterns PATTERNS.toml`.
    Pattern { id: String, patterns: PathBuf },
}

fn number(flag: &str, value: Option<&String>) -> Result<u64, String> {
    let value = value.ok_or_else(|| format!("{flag} needs a number"))?;
    value
        .parse::<u64>()
        .map_err(|_| format!("{flag} {value:?}: expected a nonnegative integer"))
}

/// The usage error of a `fuzz` command line that names more than one job.
const ONE_JOB: &str = "give one job: --kill, --matched, --fired, --refuted, --cover or --pattern";

/// `kink-flow fuzz`'s options; a job's list is `--mutations` or `--patterns`, else the front
/// end's `files`.
fn fuzz_options(args: &[String], files: &CommandFiles) -> Result<FuzzRequest, String> {
    let mut options = FuzzOptions::default();
    let (mut template, mut mutation, mut mutations) = (None, None, None);
    let (mut rule, mut pattern, mut patterns, mut fired) = (None, None, None, false);
    let (mut refuted, mut cover) = (false, None);
    let (mut budget, mut seed, mut max_work, mut time_limit) = (None, None, None, None);
    let mut stack_stops = None;
    let mut open_stops = None;
    let (mut one_path, mut no_confirm, mut no_filter) = (false, false, false);
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        // A retired flag is refused with what replaced it, though no table lists it.
        if !matches!(arg.as_str(), "--reach" | "--attempts") {
            listed(Verb::Fuzz, arg)?;
        }
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
            // No rule is spelled with a leading `--` (a `FILE:LINE`, a label or a compiled id),
            // so an option there is a missing rule, not a rule kink-flow would then refuse.
            flag @ ("--matched" | "--fired" | "--refuted") => {
                if rule.is_some() || cover.is_some() {
                    return Err(ONE_JOB.into());
                }
                let value = args
                    .next()
                    .filter(|value| !value.starts_with("--"))
                    .ok_or_else(|| format!("{flag} needs a rule"))?;
                rule = Some(value.clone());
                fired = flag == "--fired";
                refuted = flag == "--refuted";
            }
            // No obligation's id starts with `--` (`rule:`, `requirement:`, `syntax:`).
            "--cover" => {
                if rule.is_some() || cover.is_some() {
                    return Err(ONE_JOB.into());
                }
                let value = args
                    .next()
                    .filter(|value| !value.starts_with("--"))
                    .ok_or("--cover needs an obligation's id")?;
                cover = Some(value.clone());
            }
            "--reach" => {
                return Err(
                    "--reach RULE is --matched RULE, and --reach RULE --fired is --fired \
                            RULE: each names the predicate its job targets"
                        .into(),
                );
            }
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
            "--stack-stops" if stack_stops.is_none() => {
                let count = number("--stack-stops", args.next())?;
                if count == 0 {
                    return Err("--stack-stops 0: give at least one case".into());
                }
                stack_stops = Some(count);
            }
            "--open-stops" if open_stops.is_none() => {
                let count = number("--open-stops", args.next())?;
                if count == 0 {
                    return Err("--open-stops 0: give at least one case".into());
                }
                open_stops = Some(count);
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
            "--cases" | "--work" => {
                return Err(
                    "--cases and --work each set the campaign's one budget: give one of \
                            them, once"
                        .into(),
                );
            }
            _ => return Err(repeated(arg)),
        }
    }
    let template = template.ok_or("give --template ID")?;
    // A `--cover` job takes the rule job's place in the match below, its operand an item's id.
    let covering = cover.is_some();
    if let Some(item) = cover {
        rule = Some(item);
    }
    let job = match (mutation, rule, pattern) {
        (Some(mutation), None, None) => {
            if patterns.is_some() {
                return Err("--patterns belongs to --pattern".into());
            }
            // `--mutations` names the list; else the front end's list names the mutation when it
            // holds the id, and otherwise the id names a flip the front end derives, resolved
            // when the command runs (only then is the definition's source read).
            match (mutations, files.mutations.clone()) {
                (Some(mutations), _) => FuzzJobRequest::Kill {
                    mutation,
                    mutations,
                },
                (None, Some(list))
                    if MutationList::read(&list)
                        .is_ok_and(|read| !read.mutations.iter().any(|m| m.id == mutation)) =>
                {
                    FuzzJobRequest::Derived {
                        mutation,
                        list: Some(list),
                    }
                }
                (None, Some(mutations)) => FuzzJobRequest::Kill {
                    mutation,
                    mutations,
                },
                (None, None) => FuzzJobRequest::Derived {
                    mutation,
                    list: None,
                },
            }
        }
        (None, Some(rule), None) => {
            if mutations.is_some() || patterns.is_some() {
                return Err("--mutations and --patterns belong to --kill and --pattern".into());
            }
            if covering {
                FuzzJobRequest::Cover { item: rule }
            } else if refuted {
                FuzzJobRequest::Refuted { rule }
            } else {
                FuzzJobRequest::Rule { rule, fired }
            }
        }
        (None, None, Some(id)) => {
            if mutations.is_some() {
                return Err("--mutations belongs to --kill".into());
            }
            if !options.assume_joined.is_empty() {
                return Err(
                    "--assume-joined: a pattern job reads no data end, so it takes no assumed \
                     name"
                        .into(),
                );
            }
            let patterns = patterns
                .or_else(|| files.patterns.clone())
                .ok_or("--pattern needs --patterns PATTERNS.toml")?;
            FuzzJobRequest::Pattern { id, patterns }
        }
        (None, None, None) => {
            return Err(
                "give the job: --kill MUTATION --mutations MUTATIONS.toml, --matched RULE, \
                        --fired RULE, --refuted RULE, --cover ITEM, or --pattern ID --patterns \
                        PATTERNS.toml"
                    .into(),
            );
        }
        _ => return Err(ONE_JOB.into()),
    };
    options.confirm = !no_confirm;
    options.filter = !no_filter;
    if let Some(budget) = budget {
        options.budget = budget;
    }
    options.seed = seed.unwrap_or(0);
    options.max_work = max_work;
    options.time_limit_ms = time_limit;
    if let Some(count) = stack_stops {
        options.stack_stops = count;
    }
    if let Some(count) = open_stops {
        options.open_stops = count;
    }
    if one_path {
        options.paths = k_rust_fuzz::PathMode::OnePath;
    }
    Ok(FuzzRequest {
        template,
        job,
        options,
    })
}

fn report_options(args: &[String]) -> Result<(ReportOptions, OutputFormat), String> {
    let mut options = ReportOptions::default();
    let mut output = None;
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        listed(Verb::Report, arg)?;
        match arg.as_str() {
            "--output" if output.is_none() => output = Some(output_format(args.next())?),
            "--cache" if options.cache.is_none() => {
                let directory = args.next().ok_or("--cache needs a directory")?;
                options.cache = Some(PathBuf::from(directory));
            }
            _ => return Err(repeated(arg)),
        }
    }
    Ok((options, output.unwrap_or_default()))
}

/// `kink-flow fuzz FLOW.toml TEMPLATES.toml --template ID (--kill MUTATION --mutations
/// MUTATIONS.toml | --matched RULE | --fired RULE | --pattern ID --patterns PATTERNS.toml) [options]
/// [--no-confirm] [--no-filter]`: the fuzz document ([`crate::fuzz`]) and the exit status of
/// its `stopped` ([`fuzz_status`]): [`EXIT_YES`] for a witness or `equivalent`, [`EXIT_NO`] for a
/// confirmed witness, needing no premise `FLOW.toml` lacks, of a mutation expected to survive;
/// [`EXIT_UNANSWERED`] when the search ended without a witness kink accepts, or with a witness of
/// such a mutation that does not refute its expectation (unconfirmed, or resting on a premise
/// `FLOW.toml` lacks); [`EXIT_UNASKED`]
/// when an input, the template or the mutation is refused (`refused`), the campaign is
/// `not-comparable`, or it `aborted` (the README's and the guide's table).
pub fn fuzz(manifest: &Path, templates: &Path, request: &FuzzRequest) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Fuzz {
            templates: templates.to_path_buf(),
            request: request.clone(),
        },
    )
}

/// `kink-flow query FLOW.toml PATTERNS.toml [--only ID]... [--verify] [--cache DIR]`: the query
/// document (flow F-18, [`crate::query`]) and the exit status ([`query_status`]): the join of
/// every selected (pattern, program)'s answer, `hit` or `no` [`EXIT_YES`], a refuted claim and a
/// `--verify` mismatch [`EXIT_NO`], `unknown` [`EXIT_UNANSWERED`], and `invalid-pattern` or a
/// failed search [`EXIT_UNASKED`]; [`EXIT_UNASKED`] also when the manifest, the pattern list, the
/// specification or a program is refused or an answer's record could not be written.
pub fn query(manifest: &Path, patterns: &Path, options: &QueryOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Query {
            patterns: patterns.to_path_buf(),
            options: options.clone(),
        },
    )
}

/// `kink-flow report FLOW.toml [--cache DIR] [--output json|verdicts]`: the run document the last
/// `run` wrote, as `run` printed it, and the status its contents give ([`run_status`]), so that
/// `report` exits on the answer as the run did; or a `kink-flow-report` document saying why there
/// is none (`missing`, `unreadable`) and [`EXIT_UNASKED`], which is also the status when the
/// manifest does not decode. `--output verdicts` renders the same document ([`crate::verdicts`]).
pub fn report(manifest: &Path, options: &ReportOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Report {
            options: options.clone(),
            output: OutputFormat::Json,
        },
    )
}

/// `kink-flow run FLOW.toml MUTATIONS [--only ID]... [--verify] [--lock FILE [--locked]]
/// [--cache DIR]`: the run document (README 5.6, 7.5) and the exit status ([`run_status`]):
/// [`EXIT_YES`] when every selected mutation got its verdict (survivors included); [`EXIT_NO`]
/// when `--verify` found a cached outcome or memo record that differs from a live one, or
/// `--locked` found that the run would change its lock; [`EXIT_UNANSWERED`] when a mutation is
/// `timeout` or `unknown`; [`EXIT_UNASKED`] when the manifest, the mutation list, the lock, the
/// specification or a program is refused, a selected mutation is invalid (`invalid-mutation` or
/// `not-admitted`: [`invalid_mutations`]), a run failed, a cache file could not be written, no
/// program is comparable, or a baseline run no longer matches its cached result (the run then
/// stops); a run with several of these exits with their [`exit_join`].
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
    on_manifest(
        manifest,
        &FlowCommand::Run {
            mutations: mutations.to_path_buf(),
            options: options.clone(),
            mode,
            output: OutputFormat::Json,
            progress: false,
        },
    )
}

/// The number of a run document's rows whose mutation its author must fix before it is judged:
/// status `invalid-mutation` (it does not resolve, or a front end refused it) or `not-admitted` (its
/// mutant does not compile, or may have no model: `inconsistent-mutant`). Every other status is a
/// verdict about the corpus or a fault of the tool or the host, not of the mutation.
pub fn invalid_mutations(document: &Value) -> u64 {
    [crate::search::INVALID_MUTATION, "not-admitted"]
        .iter()
        .map(|status| document["counts"][*status].as_u64().unwrap_or(0))
        .sum()
}

/// `kink-flow coverage FLOW.toml [--tier 1|2] [--depth N] [--verify] [--lock FILE [--locked]]
/// [--cache DIR]`: the coverage document
/// ([`crate::coverage`]) and the exit status ([`coverage_status`]): [`EXIT_YES`] when every
/// program is comparable and meets its expectation, if it has one; [`EXIT_NO`] when an
/// expectation is unmet or `--verify` found a mismatch; [`EXIT_UNANSWERED`] for a program that
/// times out or is unknown, or an expectation that is inconclusive; [`EXIT_UNASKED`] when the
/// manifest, the specification, a `[coverage]` value or a program is refused, a run failed or a
/// record could not be written. An open obligation is not a finding.
pub fn coverage(manifest: &Path, options: &CoverageOptions) -> (Value, u8) {
    on_manifest(
        manifest,
        &FlowCommand::Coverage {
            options: options.clone(),
            output: OutputFormat::Json,
        },
    )
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
    on_manifest(manifest, &FlowCommand::Check(options.clone()))
}

/// `check --mutations` before it is rendered: the admission of the specification and the
/// programs, the mutation list, and, when the specification is admitted and the list decodes, the
/// check of every mutation ([`MutationCheck`]) and the coverage that decided `unmatched-rule` and
/// `unapplied-rule`. A front end adds its own findings to [`Self::mutations`] (the admitted
/// specification is `admission.spec`) and renders with [`check_mutations_document`].
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
                stop: manifest.stop_value(),
                observe: manifest.observe_value(),
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
            .map(|program| session.admit(program))
            .collect::<Vec<_>>();
        let cache = cache_directory(manifest, cache);
        let mut programs = programs;
        crate::check::expect_recorded(&spec, manifest, &session, &cache, &mut programs);
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
            stop: manifest.stop_value(),
            observe: manifest.observe_value(),
        },
        list,
        mutations,
        coverage: Some(coverage),
    }
}

/// The document of `check --mutations` and its exit status: the check document
/// ([`check_document`]) with `mutation_list`, `mutations` and `coverage`, and the exit status:
/// [`EXIT_UNASKED`] when the specification, a program or the list is refused, or a mutation is
/// (by resolution or by a finding with `refusal: true`), since each must be fixed before `run`
/// can judge it; else [`EXIT_NO`] when a fact known before any mutant runs makes a verdict
/// impossible ([`FlowAdmission::verdicts_possible`]), the finding `check` exists to make; else
/// [`EXIT_YES`]. Warnings decide no status. Next steps are spelled by `spelling`.
pub fn check_mutations_document(
    checked: &CorpusMutationCheck,
    spelling: &dyn CommandSpelling,
) -> (Value, u8) {
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
                document["coverage"] = coverage.value(spelling);
            }
        }
    }
    let refused = checked.list.is_err()
        || checked
            .mutations
            .as_ref()
            .is_some_and(MutationCheck::refused);
    let status = if refused {
        EXIT_UNASKED
    } else {
        admission_status(&checked.admission)
    };
    (document, status)
}

/// `kink-flow check FLOW.toml` without a mutation list: admission alone, each case's expectation
/// checked against its current result record in `cache` ([`crate::check::admit_checked`]), and
/// the exit status of the admission ([`admission_status`]); an expectation decides no exit
/// status, since `check` runs nothing and asks only whether verdicts are possible.
fn check_admission(manifest: &FlowManifest, cache: Option<&Path>) -> (Value, u8) {
    let admission = crate::check::admit_checked(manifest, cache);
    let status = admission_status(&admission);
    (check_document(&admission), status)
}

/// The exit status of `check`'s admission: `check` asks whether every verdict the corpus promises
/// is possible before any mutant runs. A refused specification or program could not be asked
/// about ([`EXIT_UNASKED`]: fix it); a program every baseline run of which is excluded, or a
/// baseline with no data under `[spec] assume_joined`, is the finding that says no
/// ([`EXIT_NO`]); else [`EXIT_YES`] ([`FlowAdmission::verdicts_possible`]).
fn admission_status(admission: &FlowAdmission) -> u8 {
    if !admission.all_admitted() {
        EXIT_UNASKED
    } else if admission.verdicts_possible() {
        EXIT_YES
    } else {
        EXIT_NO
    }
}

/// The version of the check document: 2 adds `mutation_list`, `mutations` and `coverage` (null
/// without `--mutations`); 3 adds `spec.exclusion` and the program outcome `excluded`, and
/// exits 1 when any program cannot be judged on the baseline, a definition exclusion included;
/// 4 adds `data` and `spec.baseline_findings`, and exits 1 when the baseline has no data under
/// `[spec] assume_joined` ([`FlowAdmission::verdicts_possible`]); 5 adds `result`, the slots and
/// the cells the programs' second slot compares ([`crate::observed`]), and the specification's
/// refusal at stage `result`; 6 (CF-03) adds `spec.short_circuit`, the rules the short-circuit
/// analysis flags, which are no longer a definition exclusion: each run of such a definition is
/// judged by k-rust's list of that run, so no program is `excluded` for them before it runs; and
/// a program whose initial configuration applies a reading-dependent function is `excluded` at
/// stage `initial-state` only when its depth-0 run lists a reading that counts against it; 7
/// gives `unreached-rule` for an edited rule no comparable program reached (k-rust `matched`),
/// whatever the edit (before, an edit that left the `requires` alone was warned about when no
/// program applied the rule), and adds `unapplied-rule` for one some program reached and none
/// applied (`applied`), since `check` compiles no mutant and so cannot read `run`'s witness rule
/// ([`crate::check`]); 8 (CF-40c2) names the first `unmatched-rule`, after the predicate it
/// reads (k-rust `matched`), so that each coverage predicate has one name in every kink-flow
/// document, and says `matches` for `reaches` in both warnings' text; 9 adds `stop` for a corpus
/// with `[stop]` (absent without one), the warnings `stop-hides-edit` and `stop-rule-deleted`,
/// and the specification's refusal at stage `stop` (`stop-unresolved`, `backend-error`); 10 adds
/// named cases of a case document (each a program whose id is the document's path, `#` and its
/// name), and each case's `expectation`, checked against its current result record without
/// running it (`crate::expect`; it decides no exit status), and refuses a program whose
/// expectation no front end reads at stage `inputs` (`typed-expectation`, `expectation-value`);
/// 11 since `result` may name cells inside `?` and `*` cells, each left out (or compared) in
/// every instance, and a narrowing's `compared` names the key of each Map that encloses a named
/// cell; the refusals `unobservable-cell-position` and `result-cell-position` are gone, and a
/// Map's key left out is refused (`map-key-left-out`) ([`crate::observed`]); 12 since `[stop]
/// when`: a stop with a condition names it in `stop` (`when`, the condition's identity as the
/// front end resolved it), a specification whose front end states no condition is refused at
/// stage `stop` (`unsupported-front-end`), and under a condition `stop-hides-edit` is given for
/// a rule no comparable program's run took the step of, read from coverage that decides; 13
/// since `[observe]`: a corpus with observation channels names the declaration (`observe`, as
/// every run compares by it; absent without one), a specification on which a class's rule labels
/// no rewrite rule or a cell states no observation is refused at stage `observe`
/// (`point-unresolved`, `cell-refused`, `backend-error`), a key that names a function of an
/// observer is refused there too (`unsupported-front-end`), and a mutation that deletes a rule a
/// point class names is warned `point-rule-deleted`; 14 since under the Z3 profile the document
/// names the Z3 build (`z3`, [`crate::with_z3_build`]): each case's expectation and the coverage
/// warnings are read from result records, whose classes and coverage baseline runs decided by
/// asking the solver, and a record is read only under a key that names this build, so they are a
/// function of the build as much as of `profile`.
/// 15 names each finding of the full critical-pair check by its kind, sentences and a digest of its
/// compiled sentences (`root:A,B#D`, k-rust-backend `data_term::names`) where it named it by
/// generated-K positions, gives each finding its `sentences` (`{part, at}`, `at` information only),
/// and refuses a `[spec] assume_joined` name with one of the reasons `malformed`, `position-name`,
/// `unnamed-sentence`, `no-digest`, `changed`, `no-finding`, `decided` or `ambiguous` where it
/// refused `name-refused` (KINK-FINDING-NAMES).
pub const CHECK_VERSION: u64 = 15;

/// The check document's members, and under the Z3 profile `z3` ([`crate::with_z3_build`]); every
/// document a verb gives for a manifest that does not decode is built from it
/// ([`Verb::manifest_refused`]), so each names the build as the verb's own documents do.
fn header(spec: Value, programs: Vec<Value>, data: Value, result: Value) -> Value {
    crate::with_z3_build(json!({
        "schema": "kink-flow-check",
        "version": CHECK_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "spec": spec,
        "programs": programs,
        "data": data,
        "result": result,
        "mutation_list": null,
        "mutations": null,
        "coverage": null,
    }))
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
            "exclusion": null,
            "short_circuit": null,
            "baseline_findings": null,
        }),
        Vec::new(),
        Value::Null,
        Value::Null,
    )
}

/// The check document of an admission. `spec.exclusion` is the definition exclusion of the admitted
/// specification ([`crate::exclusion::definition_exclusion`], null when there is none or the
/// specification is refused), and `spec.short_circuit` the rules its short-circuit analysis flags
/// ([`crate::exclusion::short_circuit`], null when it flags none), which make no program
/// `excluded`: a run of such a definition is judged by its own list of readings. A program is `ok`,
/// `refused` (stage, reason and detail of the refusal), or `excluded`: admitted, but every run of
/// it on the baseline is excluded before it runs (stage `definition` or `initial-state`, the
/// exclusion's name as reason, and why). `data` is the baseline's full critical-pair check under
/// `[spec] assume_joined`, as the run, `coverage` and `query` documents print it (kink-native
/// `DataFacts::value`), and `spec.baseline_findings` says why the baseline has no data
/// ([`baseline_findings`]); `result` names the slots and the cells the programs' second slot
/// compares ([`crate::observed::ResultProjection::value`]); all three are null when the
/// specification is refused.
pub fn check_document(admission: &FlowAdmission) -> Value {
    let record = &admission.record;
    let refusal = record.refusal.as_ref();
    let exclusion = admission
        .spec
        .as_ref()
        .filter(|spec| spec.exclusions.definition_exclusion().is_some())
        .map_or(Value::Null, |spec| {
            crate::exclusion::definition_exclusion(
                spec,
                &crate::evidence::EndReader::of(&spec.compiled),
            )
        });
    let short_circuit = admission
        .spec
        .as_ref()
        .filter(|spec| spec.exclusions.short_circuit_flagged())
        .map_or(Value::Null, |spec| {
            crate::exclusion::short_circuit(spec, &crate::evidence::EndReader::of(&spec.compiled))
        });
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
        "exclusion": exclusion,
        "short_circuit": short_circuit,
        "baseline_findings": admission
            .spec
            .as_ref()
            .map_or(Value::Null, |spec| baseline_findings(&spec.data)),
    });
    let programs = admission
        .programs
        .iter()
        .map(|program| match (&program.outcome, &program.exclusion) {
            (Err(refusal), _) => json!({
                "id": program.id,
                "outcome": "refused",
                "stage": refusal.stage,
                "reason": refusal.reason,
                "detail": refusal.detail,
            }),
            (Ok(_), Some(exclusion)) => json!({
                "id": program.id,
                "outcome": "excluded",
                "stage": exclusion.scope.name(),
                "reason": exclusion.exclusion.name(),
                "detail": exclusion.detail(),
            }),
            (Ok(_), None) => json!({
                "id": program.id,
                "outcome": "ok",
                "stage": null,
                "reason": null,
                "detail": null,
            }),
        })
        .zip(&admission.programs)
        .map(|(mut row, program)| {
            // A case's expectation (`crate::expect`); absent without one.
            if let Some(expectation) = &program.expectation {
                row["expectation"] = expectation.clone();
            }
            row
        })
        .collect();
    let data = admission
        .spec
        .as_ref()
        .map_or(Value::Null, |spec| spec.data.value());
    let result = admission
        .spec
        .as_ref()
        .map_or(Value::Null, |spec| spec.result.value());
    let mut document = header(spec, programs, data, result);
    // Absent without a stop, so a document without one is the document it was before stops.
    if let Some(stop) = &admission.stop {
        document["stop"] = stop.clone();
    }
    // The resolved observation declaration; absent without `[observe]`.
    if let Some(observe) = &admission.observe {
        document["observe"] = observe.clone();
    }
    document
}

/// Why the baseline has no data under `[spec] assume_joined`, so that no mutation can have a
/// verdict but `unknown` (`baseline-findings`) and no query a `no`: null when it has data, else
/// `{detail, findings, incomplete}`. `findings` lists each finding no name assumes,
/// `{name, verdict, description, next}`, `next` being what to do about it
/// ([`finding_next`]); `incomplete` is null, or `{detail, next}` when the check did not read the
/// whole definition (kink-native `DataFacts::incomplete`); `detail` says both in one text,
/// naming at most [`crate::exclusion::DETAIL_CAUSES`] findings.
#[must_use]
pub fn baseline_findings(data: &kink_native::data::DataFacts) -> Value {
    if data.has_data() {
        return Value::Null;
    }
    let unnamed = data.unnamed();
    let incomplete = data.incomplete();
    let mut reasons = Vec::new();
    if !unnamed.is_empty() {
        reasons.push(format!(
            "has {} finding(s) that [spec] assume_joined leaves unnamed",
            unnamed.len()
        ));
    }
    if let Some(why) = &incomplete {
        reasons.push(format!("did not read the whole definition ({why})"));
    }
    let mut items = unnamed
        .iter()
        .map(|finding| {
            format!(
                "{} ({}: {}): {}",
                finding.name.as_deref().map_or_else(
                    || "a finding with no name".to_owned(),
                    |name| format!("`{name}`")
                ),
                finding.verdict.name(),
                finding.description,
                finding_next(finding)
            )
        })
        .collect::<Vec<_>>();
    let shown = items.len().min(crate::exclusion::DETAIL_CAUSES);
    let more = items.len() - shown;
    items.truncate(shown);
    if more > 0 {
        items.push(format!("and {more} more (findings)"));
    }
    if incomplete.is_some() {
        items.push(format!(
            "for what the check did not read: {INCOMPLETE_NEXT}"
        ));
    }
    json!({
        "detail": format!(
            "the baseline's full critical-pair check {}, so no end of the definition is data: \
             every mutation with a program to run is unknown (baseline-findings) and no query \
             answers no; {}",
            reasons.join(" and "),
            items.join("; ")
        ),
        "findings": unnamed
            .iter()
            .map(|finding| json!({
                "name": finding.name,
                "verdict": finding.verdict.name(),
                "description": finding.description,
                "next": finding_next(finding),
            }))
            .collect::<Vec<_>>(),
        "incomplete": incomplete.map(|why| json!({"detail": why, "next": INCOMPLETE_NEXT})),
    })
}

/// What to do when the full critical-pair check did not read the whole definition: no name
/// assumes what the check did not read, so only k-rust's checker can remove it.
const INCOMPLETE_NEXT: &str = "report it: it is a limit of k-rust's checker, and no [spec] \
                               assume_joined name can assume a part of the definition the check \
                               did not read";

/// What to do about a finding that `[spec] assume_joined` leaves unnamed, by what it is
/// (kink-native `FindingVerdict`): a name assumes the finding away, so naming it is right only
/// where the definition is right and the checker could not show it. A decided finding is a fact
/// about the definition as written and no name assumes it (admission refuses one,
/// `decided`); a genuine one has a ground input with two normal forms, so a name would be a
/// premise known to be false; an undecided one may be a limit of the checker, which the author
/// reviews; a finding with no name cannot be named at all.
#[must_use]
pub fn finding_next(finding: &kink_native::data::NamedFinding) -> String {
    use kink_native::data::FindingVerdict;
    let Some(name) = &finding.name else {
        return "fix the definition: the finding has no name, so no [spec] assume_joined entry \
                assumes it"
            .to_owned();
    };
    match finding.verdict {
        FindingVerdict::Decided => "fix the definition: a decided finding is a fact about the \
                                    definition as written, which no [spec] assume_joined name \
                                    assumes"
            .to_owned(),
        FindingVerdict::Genuine => format!(
            "fix the definition: a ground input of this pair has two normal forms, so the pair \
             does not join; [spec] assume_joined refuses `{name}` (decided), a premise known to \
             be false"
        ),
        FindingVerdict::Undecided => format!(
            "review it: if the definition is right here and the checker only could not show it \
             (the pair joins, the equation agrees with its hook or applies as written, the \
             precondition is met), name `{name}` in [spec] assume_joined; otherwise fix the \
             definition"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A value the option parsers accept for the value name `name` of a listed option.
    fn value(name: &str) -> &'static str {
        match name {
            "cost|corpus" => "cost",
            "json|verdicts" | "json|text|verdicts" | "json|text" => "json",
            "1|2" => "1",
            "N" | "W" | "S" | "T" => "1",
            _ => "value",
        }
    }

    /// Every option a verb's table lists is one its parser accepts: given alone with a value of
    /// its kind, no option is an unexpected argument (the parser may still ask for the rest of
    /// the command line). With [`listed`], which refuses every flag the table does not list, the
    /// table and the parser accept the same flags.
    #[test]
    fn every_listed_option_is_one_the_parser_accepts() {
        for verb in Verb::ALL {
            for option in verb.options() {
                let mut args = vec![option.flag().to_owned()];
                if let Some((_, name)) = option.spelling.split_once(' ') {
                    args.push(value(name).to_owned());
                }
                let error = match verb {
                    Verb::Check => check_options(&args).err(),
                    Verb::Coverage => coverage_options(&args).err(),
                    Verb::Run => run_options(&args).err(),
                    Verb::Report => report_options(&args).err(),
                    Verb::Query => query_options(&args).err(),
                    Verb::Fuzz => fuzz_options(&args, &CommandFiles::default()).err(),
                    Verb::Compare => compare_options(&args).err(),
                };
                assert!(
                    !error.as_deref().is_some_and(|error| {
                        error.starts_with("unexpected argument")
                            || error.starts_with("invalid option")
                    }),
                    "{} {args:?}: {error:?}",
                    verb.as_str()
                );
            }
            let unlisted = ["--unlisted".to_owned()];
            let error = match verb {
                Verb::Check => check_options(&unlisted).err(),
                Verb::Coverage => coverage_options(&unlisted).err(),
                Verb::Run => run_options(&unlisted).err(),
                Verb::Report => report_options(&unlisted).err(),
                Verb::Query => query_options(&unlisted).err(),
                Verb::Fuzz => fuzz_options(&unlisted, &CommandFiles::default()).err(),
                Verb::Compare => compare_options(&unlisted).err(),
            };
            assert_eq!(error.as_deref(), Some("invalid option '--unlisted'"));
        }
    }

    /// A listed option given twice is refused as a repetition, never as an option the verb does
    /// not take; `--cases` and `--work` set one budget, so either after the other is refused for
    /// that.
    #[test]
    fn a_repeated_option_is_refused_as_given_more_than_once() {
        let twice = ["--cache", "a", "--cache", "b"].map(str::to_owned);
        for verb in Verb::ALL {
            let error = match verb {
                Verb::Check => check_options(&twice).err(),
                Verb::Coverage => coverage_options(&twice).err(),
                Verb::Run => run_options(&twice).err(),
                Verb::Report => report_options(&twice).err(),
                Verb::Query => query_options(&twice).err(),
                Verb::Fuzz => fuzz_options(&twice, &CommandFiles::default()).err(),
                Verb::Compare => compare_options(&twice).err(),
            };
            assert_eq!(
                error.as_deref(),
                Some("--cache specified more than once"),
                "{}",
                verb.as_str()
            );
        }
        let budgets = ["--cases", "5", "--work", "9"].map(str::to_owned);
        assert_eq!(
            fuzz_options(&budgets, &CommandFiles::default())
                .err()
                .as_deref(),
            Some("--cases and --work each set the campaign's one budget: give one of them, once")
        );
    }
}
