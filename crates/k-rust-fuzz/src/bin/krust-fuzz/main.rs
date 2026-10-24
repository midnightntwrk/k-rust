//! `krust-fuzz`: craft concrete input values that make a program reach a target under a K
//! specification, from a compiled directory, a program and a campaign file
//! (ARCHITECTURE 9.4). `krust fuzz …` runs this executable.
//!
//! The campaign is the library's ([`k_rust_fuzz::Campaign`]): the campaign file and the flags
//! map onto its specification. Compiled directories are loaded as `krust krun --definition`
//! loads them, and every backend is built on krun's route. The exit status is 0 when a witness
//! was found and confirmed (or, with `--replay`, when every recorded witness case reproduced), 1
//! when not, and 2 on an error or a refused replay.

mod campaign;
mod replay;

use std::{
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::{Parser, ValueEnum};
use k_rust::backend::{CompiledRuleKind, HaltReasonOutput};
use k_rust_fuzz::{
    Campaign, CampaignError,
    error::TargetProblem,
    exec::UnjudgedReason,
    report::{
        BestScore, CampaignOutcome, DefinitionRole, FuzzReport, HitLabel, KillKind, WitnessCase,
    },
    spec::CompiledDefinition,
    target::RuleMode,
};

use crate::{
    campaign::{Overrides, parse_seed},
    replay::WitnessFile,
};

/// The stack of the thread every campaign runs on, recorded in the report: stack stops depend
/// on it (ARCHITECTURE 5.4).
const STACK_SIZE: usize = 256 << 20;

/// Exit status: a witness was found (or reproduced).
const FOUND: u8 = 0;
/// Exit status: no witness was found (or a recorded case did not reproduce).
const NOT_FOUND: u8 = 1;
/// Exit status: an error, or a refused replay.
const ERROR: u8 = 2;

#[derive(Debug, Parser)]
#[command(
    name = "krust-fuzz",
    about = "Craft input values that make a program reach a target under a K specification",
    long_about = "Craft input values that make a program reach a target under a K specification.\n\n\
                  The holes (typed literals of the unmodified program, or configuration \
                  variables) and, optionally, the target and options come from a campaign file \
                  in TOML (crates/k-rust-fuzz/README.md, \"Command line\"); flags override it. \
                  Exit status: 0 when a witness was found and confirmed (with --replay: \
                  reproduced), 1 when not, 2 on an error or a refused replay.",
    arg_required_else_help = true
)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "each flag is one independent command-line switch"
)]
struct Args {
    /// Campaign file: `[[hole]]` declarations and, optionally, the target and options.
    #[arg(long, visible_alias = "holes", value_name = "FILE")]
    campaign: Option<PathBuf>,

    /// Compiled directory produced by `krust kcompile` (the baseline of a differential).
    #[arg(long, value_name = "DIR")]
    definition: Option<PathBuf>,

    /// Compiled directory of the mutant; selects the differential target when no other target
    /// is named.
    #[arg(long, value_name = "DIR")]
    mutant: Option<PathBuf>,

    /// Program file; its path as written names the program that span holes address.
    #[arg(long, value_name = "FILE")]
    program: Option<String>,

    /// Start sort of the program parser (defaults to the sort of $PGM).
    #[arg(short = 's', long, value_name = "SORT")]
    sort: Option<String>,

    /// Bind a configuration variable, as `krust krun -c` does (after the campaign file's).
    #[arg(short = 'c', long = "config-var", value_name = "NAME=VALUE")]
    config_vars: Vec<String>,

    /// Target: this rule fires (or see `--rule-mode`); the help text says how `RULE` is read.
    #[arg(
        long,
        value_name = "RULE",
        conflicts_with_all = ["pattern", "differential"],
        help = "Target: this rule fires (or see --rule-mode). RULE is FILE:LINE (any line of the \
                rule, as kink lists rules) or FILE:FIRST-LAST (as the summary prints it), the \
                rule's unique id (64 hexadecimal digits, as the report names rules), or its label \
                (IMP.overflow, or overflow when no label is that)"
    )]
    reach_rule: Option<String>,

    /// What counts as reaching the rule (only with a rule target).
    #[arg(long, value_enum, value_name = "MODE")]
    rule_mode: Option<RuleModeArg>,

    /// Target: a clean final configuration matches this pattern (`krust krun --pattern` syntax).
    #[arg(long, value_name = "PATTERN", conflicts_with = "differential")]
    pattern: Option<String>,

    /// Target: the mutant reaches an end the baseline cannot (needs --mutant).
    #[arg(long)]
    differential: bool,

    /// A reaching case must also end naturally.
    #[arg(long, overrides_with = "no_run_to_completion")]
    run_to_completion: bool,

    /// A reaching case need not end naturally (overrides the campaign file).
    #[arg(long, overrides_with = "run_to_completion")]
    no_run_to_completion: bool,

    /// The target is a property's violation: report a hit as a property failure.
    #[arg(long, overrides_with = "no_negated_property")]
    negated_property: bool,

    /// The target is not a property's violation (overrides the campaign file).
    #[arg(long, overrides_with = "negated_property")]
    no_negated_property: bool,

    /// With --run-to-completion, a rule or pattern hit's end must also be data, so that the
    /// witness's end can be compared with another definition's (the default).
    #[arg(long, overrides_with = "no_data_end")]
    data_end: bool,

    /// With --run-to-completion, accept a rule or pattern hit whose end is not data.
    #[arg(long, overrides_with = "data_end")]
    no_data_end: bool,

    /// Explore every path of each input instead of k-rust's first-applicable path.
    #[arg(long, overrides_with = "one_path")]
    all_paths: bool,

    /// Explore k-rust's first-applicable path of each input (overrides the campaign file).
    #[arg(long, overrides_with = "all_paths")]
    one_path: bool,

    /// Depth bound of every case.
    #[arg(long, value_name = "N")]
    max_depth: Option<u64>,

    /// Work bound of every case (100000 when neither bound is set).
    #[arg(long, value_name = "N")]
    max_work: Option<u64>,

    /// Normal-termination pattern (defaults to `<k> .K </k>`).
    #[arg(long, value_name = "PATTERN")]
    normal_end: Option<String>,

    /// Budget: at most this many cases (1000 when no budget is set).
    #[arg(long, value_name = "N", conflicts_with = "work")]
    cases: Option<u64>,

    /// Budget: at most this much backend work, over every execution.
    #[arg(long, value_name = "N")]
    work: Option<u64>,

    /// Campaign seed, decimal or 0x hexadecimal (0 when not set).
    #[arg(long, value_name = "SEED", value_parser = parse_seed)]
    seed: Option<u64>,

    /// Rejected cases after which the campaign ends.
    #[arg(long, value_name = "N")]
    rejection_cap: Option<u64>,

    /// Per-case wall-clock safety limit, at least 1 (60 when not set); a case it stops is a
    /// timeout, outside the determinism contract.
    #[arg(long, value_name = "SECONDS", conflicts_with = "no_safety_limit")]
    safety_limit: Option<u64>,

    /// Run cases without a wall-clock safety limit.
    #[arg(long)]
    no_safety_limit: bool,

    /// Report the first confirmed witness without shrinking it.
    #[arg(long, overrides_with = "shrink")]
    no_shrink: bool,

    /// Shrink a confirmed witness (the default; overrides the campaign file).
    #[arg(long, overrides_with = "no_shrink")]
    shrink: bool,

    /// Solver time limit per query, in milliseconds.
    #[arg(long, value_name = "MS")]
    smt_timeout: Option<u32>,

    /// Solver retry limit.
    #[arg(long, value_name = "N")]
    smt_retry_limit: Option<u32>,

    /// Print the report as canonical JSON instead of a summary.
    #[arg(long)]
    json: bool,

    /// Write the report as canonical JSON to FILE.
    #[arg(long, value_name = "FILE")]
    report: Option<PathBuf>,

    /// When a witness is found, write it with the campaign to FILE, for --replay; when none is
    /// found, remove FILE if it exists, so that it never holds an older run's witness.
    #[arg(long, value_name = "FILE")]
    witness: Option<PathBuf>,

    /// Replay a witness file: check its identity and re-run its witness cases. --definition,
    /// --mutant and --program then relocate the recorded inputs.
    #[arg(
        long,
        value_name = "FILE",
        conflicts_with_all = [
            "campaign", "sort", "config_vars", "reach_rule", "rule_mode", "pattern",
            "differential", "run_to_completion", "no_run_to_completion", "negated_property",
            "no_negated_property", "data_end", "no_data_end", "all_paths", "one_path",
            "max_depth", "max_work",
            "normal_end", "cases", "work", "seed", "rejection_cap", "safety_limit",
            "no_safety_limit", "no_shrink", "shrink", "smt_timeout", "smt_retry_limit", "json",
            "report", "witness",
        ]
    )]
    replay: Option<PathBuf>,

    /// Replay despite an identity mismatch.
    #[arg(long, requires = "replay")]
    force: bool,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum RuleModeArg {
    /// A clean leaf's trace contains a rewrite with the rule.
    Fired,
    /// The rule is in the run's coverage `applied`.
    Covered,
    /// The rule is in the run's coverage `matched`.
    ConditionReached,
}

impl From<RuleModeArg> for RuleMode {
    fn from(mode: RuleModeArg) -> Self {
        match mode {
            RuleModeArg::Fired => RuleMode::Fired,
            RuleModeArg::Covered => RuleMode::Covered,
            RuleModeArg::ConditionReached => RuleMode::ConditionReached,
        }
    }
}

fn main() -> ExitCode {
    // Checked before the arguments, so that a krust-fuzz of another build does not even print
    // its help as this krust's.
    let own = k_rust::build_identity();
    if let Some(parent) = std::env::var_os(k_rust::native::FUZZ_PARENT_BUILD_ENV) {
        let parent = parent.to_string_lossy();
        if parent != own.as_str() {
            eprintln!(
                "error: version skew: krust is k-rust {parent}, but this krust-fuzz was built \
                 from k-rust {own}; install krust and krust-fuzz from one build"
            );
            return ExitCode::from(ERROR);
        }
        if !k_rust::is_verified_build(&own) {
            eprintln!(
                "warning: krust and krust-fuzz are both unverified builds of k-rust {own}: \
                 their sources cannot be compared, only their versions"
            );
        }
    }
    // The version names the k-rust build, which the skew check and the reports compare.
    let version: &'static str =
        Box::leak(format!("{} (k-rust {own})", env!("CARGO_PKG_VERSION")).into_boxed_str());
    let matches = <Args as clap::CommandFactory>::command()
        .version(version)
        .get_matches();
    let args = match <Args as clap::FromArgMatches>::from_arg_matches(&matches) {
        Ok(args) => args,
        Err(error) => error.exit(),
    };
    let worker = std::thread::Builder::new()
        .name("krust-fuzz".into())
        .stack_size(STACK_SIZE)
        .spawn(move || run(args));
    let outcome = match worker {
        Ok(worker) => worker
            .join()
            .unwrap_or_else(|_| Err("the campaign thread panicked".into())),
        Err(error) => Err(format!("cannot start the campaign thread: {error}")),
    };
    match outcome {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(ERROR)
        }
    }
}

fn run(args: Args) -> Result<u8, String> {
    if let Some(witness) = &args.replay {
        return replay_command(witness, &args);
    }
    let file = args
        .campaign
        .as_deref()
        .map(|path| campaign::read_campaign_file(path).map(|file| (path, file)))
        .transpose()?;
    let overrides = Overrides {
        definition: args.definition,
        mutant: args.mutant,
        program: args.program,
        sort: args.sort,
        config_vars: args.config_vars,
        reach_rule: args.reach_rule,
        rule_mode: args.rule_mode.map(RuleMode::from),
        pattern: args.pattern,
        differential: args.differential,
        run_to_completion: switch(args.run_to_completion, args.no_run_to_completion),
        negated_property: switch(args.negated_property, args.no_negated_property),
        data_end: switch(args.data_end, args.no_data_end),
        all_paths: switch(args.all_paths, args.one_path),
        max_depth: args.max_depth,
        max_work: args.max_work,
        normal_end: args.normal_end,
        cases: args.cases,
        work: args.work,
        seed: args.seed,
        rejection_cap: args.rejection_cap,
        safety_limit_seconds: args.safety_limit,
        no_safety_limit: args.no_safety_limit,
        shrink: switch(args.shrink, args.no_shrink),
        smt_timeout_ms: args.smt_timeout,
        smt_retry_limit: args.smt_retry_limit,
    };
    // The output paths are checked before the campaign, so that a long campaign's result is not
    // lost to a path that cannot be written.
    for path in [&args.report, &args.witness].into_iter().flatten() {
        check_writable(path)?;
    }
    if let (Some(report), Some(witness)) = (&args.report, &args.witness)
        && same_file(report, witness)
    {
        return Err(format!(
            "--report `{}` and --witness `{}` name the same file; give them different paths",
            report.display(),
            witness.display()
        ));
    }
    // The rule reference as written, for the range check below: the flag's, or else the file's
    // (a flag naming another target kind makes the target no rule, and the check is skipped).
    let rule_text = overrides.reach_rule.clone().or_else(|| {
        file.as_ref()
            .and_then(|(_, file)| file.target.as_ref()?.rule.clone())
    });
    let origins = PatternOrigins::of(
        args.campaign.as_deref(),
        file.as_ref().map(|(_, file)| file),
        &overrides,
    );
    let loaded = campaign::resolve(file, overrides)?;
    let spec = loaded.spec(
        loaded.resolved.proposers.clone(),
        loaded.resolved.options.clone(),
        STACK_SIZE as u64,
    );
    let mut campaign = Campaign::new(spec).map_err(|error| origins.refusal(&error))?;
    if let (Some(text), Some(rule)) = (&rule_text, campaign.target_rule()) {
        campaign::check_rule_range(text, rule)?;
    }
    let report = campaign.run(loaded.resolved.budget, None);
    let json = report.to_canonical_json();
    // The result is printed before any file is written, so that a failed write loses nothing.
    if args.json {
        println!("{json}");
    } else {
        let printers = EndPrinters::of(&loaded.baseline, loaded.mutant.as_deref());
        print!("{}", summary(&report, Some(&printers)));
    }
    if let Some(path) = &args.report {
        std::fs::write(path, format!("{json}\n"))
            .map_err(|error| format!("cannot write the report `{}`: {error}", path.display()))?;
    }
    if let Some(path) = &args.witness {
        if report.witness().is_some() {
            WitnessFile::write(path, &loaded.resolved, &report)?;
        } else if path.exists() {
            std::fs::remove_file(path).map_err(|error| {
                format!(
                    "no witness was found, and the older `{}` cannot be removed: {error}",
                    path.display()
                )
            })?;
            eprintln!(
                "note: no witness was found, so the older `{}` was removed",
                path.display()
            );
        }
    }
    Ok(if report.witness().is_some() {
        FOUND
    } else {
        NOT_FOUND
    })
}

/// Where a campaign's patterns came from, for a refusal that names them (FZ-POLISH S6): the
/// library positions an error in the pattern's own text, and only the command line knows which
/// key or flag gave the text.
struct PatternOrigins {
    /// The target pattern's: `--pattern` or the campaign file's key.
    target: String,
    /// The normal-end pattern's: `--normal-end` or the campaign file's key.
    normal_end: String,
}

impl PatternOrigins {
    /// The origins of the patterns that `overrides` and the campaign file at `path` give, as
    /// `campaign::resolve` chooses them: a flag over the file.
    fn of(
        path: Option<&Path>,
        file: Option<&campaign::CampaignFile>,
        overrides: &Overrides,
    ) -> Self {
        let in_file = |key: &str, table: &str| match path {
            Some(path) => format!("`{key}` of `[{table}]` in {}", path.display()),
            None => format!("`{key}` of `[{table}]`"),
        };
        let target = if overrides.pattern.is_some() {
            "--pattern".to_owned()
        } else {
            in_file("pattern", "target")
        };
        let in_options = file
            .and_then(|file| file.options.as_ref())
            .is_some_and(|options| options.normal_end_pattern.is_some());
        let normal_end = if overrides.normal_end.is_some() {
            "--normal-end".to_owned()
        } else if in_options {
            in_file("normal-end-pattern", "options")
        } else {
            "the default `<k> .K </k>`".to_owned()
        };
        Self { target, normal_end }
    }

    /// The command line's message for `error`, naming the origin of a refused pattern.
    fn refusal(&self, error: &CampaignError) -> String {
        match error {
            CampaignError::Target(TargetProblem::Pattern(message)) => format!(
                "campaign refused: the target pattern ({}) is refused: {message}",
                self.target
            ),
            CampaignError::NormalEndPattern { message } => format!(
                "campaign refused: the normal-end pattern ({}) is refused: {message}",
                self.normal_end
            ),
            other => format!("campaign refused: {other}"),
        }
    }
}

/// `Some(true)` for the switch, `Some(false)` for its negation (clap keeps only the last one
/// given), `None` for neither.
fn switch(on: bool, off: bool) -> Option<bool> {
    match (on, off) {
        (true, _) => Some(true),
        (false, true) => Some(false),
        (false, false) => None,
    }
}

/// Whether `left` and `right` name one file: equal after resolving the directory part (the
/// files need not exist yet).
fn same_file(left: &Path, right: &Path) -> bool {
    let resolve = |path: &Path| {
        let directory = match path.parent() {
            Some(parent) if !parent.as_os_str().is_empty() => parent.to_path_buf(),
            _ => PathBuf::from("."),
        };
        std::fs::canonicalize(directory)
            .ok()
            .zip(path.file_name().map(std::ffi::OsStr::to_os_string))
    };
    match (resolve(left), resolve(right)) {
        (Some(left), Some(right)) => left == right,
        _ => left == right,
    }
}

/// Refuse an output path that cannot be written, without changing an existing file.
fn check_writable(path: &Path) -> Result<(), String> {
    let existed = path.exists();
    std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)
        .map_err(|error| format!("cannot write `{}`: {error}", path.display()))?;
    if !existed {
        let _ = std::fs::remove_file(path);
    }
    Ok(())
}

fn replay_command(path: &Path, args: &Args) -> Result<u8, String> {
    let file = WitnessFile::read(path)?;
    let mut resolved = file.campaign.clone();
    // The replay's revision is this build's, which the identity check compares with the one
    // that found the witness; nothing can name another.
    resolved.k_rust_revision = k_rust::build_identity();
    let current = std::env::current_dir()
        .map_err(|error| format!("cannot read the working directory: {error}"))?;
    let relocate = |path: &Path| current.join(path);
    if let Some(definition) = &args.definition {
        resolved.definition = relocate(definition);
    }
    if let Some(mutant) = &args.mutant {
        if resolved.mutant.is_none() {
            return Err("--mutant relocates the mutant, but the witness has none".into());
        }
        resolved.mutant = Some(relocate(mutant));
    }
    if let Some(program) = &args.program {
        let recorded = resolved
            .program
            .as_mut()
            .ok_or("--program relocates the program, but the witness has none")?;
        recorded.path = relocate(Path::new(program));
    }
    let loaded = campaign::reload(resolved).map_err(|error| {
        format!(
            "{error}\nif the witness's inputs moved, relocate them with --definition, --mutant or \
             --program"
        )
    })?;
    let replay = replay::replay(&file, &loaded, args.force, STACK_SIZE as u64)?;
    let unverified = [
        &file.report.identity.k_rust_revision,
        &loaded.resolved.k_rust_revision,
    ]
    .into_iter()
    .filter(|revision| !k_rust::is_verified_build(revision))
    .map(|revision| format!("`{revision}`"))
    .collect::<Vec<_>>();
    if !unverified.is_empty() {
        eprintln!(
            "note: the k-rust revision {} names no source digest, so builds of one version \
             cannot be told apart by it",
            unverified.join(" and ")
        );
    }
    if replay.cases.is_empty() {
        let mut message = String::from("the witness's identity is not the replay's:");
        for mismatch in &replay.mismatches {
            message.push_str("\n  identity mismatch: ");
            message.push_str(mismatch);
        }
        message.push_str("\npass --force to replay it anyway");
        return Err(message);
    }
    for mismatch in &replay.mismatches {
        println!("identity mismatch (forced): {mismatch}");
    }
    if !replay.mismatches.is_empty() {
        let count = replay.mismatches.len();
        println!(
            "forced: replayed despite {count} identity {}",
            if count == 1 { "mismatch" } else { "mismatches" }
        );
    }
    let mut reproduced = true;
    for case in &replay.cases {
        if case.differences.is_empty() {
            println!("{} witness: reproduced", case.which);
        } else {
            reproduced = false;
            println!("{} witness: not reproduced", case.which);
            for difference in &case.differences {
                println!("  {difference}");
            }
            for defect in &case.report.engine_defects {
                println!("  engine defect: {}", defect.description);
            }
        }
    }
    Ok(if reproduced { FOUND } else { NOT_FOUND })
}

/// A human-readable summary of `report`; a differential witness's ends are printed as K text
/// with `printers`, as KORE without them.
fn summary(report: &FuzzReport, printers: Option<&EndPrinters>) -> String {
    use std::fmt::Write as _;
    let mut text = String::new();
    let status = match &report.outcome {
        CampaignOutcome::WitnessFound { witness } => match witness.label {
            HitLabel::Hit => "witness found",
            HitLabel::PropertyFailure => "witness found: property failure",
        },
        CampaignOutcome::NoWitnessFound { .. } => "no witness found",
        CampaignOutcome::Equivalent => "equivalent: the definitions denote the same theory",
        CampaignOutcome::RejectedOut { .. } => "no witness found: rejection cap reached",
        CampaignOutcome::Cancelled { .. } => "no witness found: cancelled",
        CampaignOutcome::Aborted { .. } => "no witness found: aborted",
    };
    let _ = writeln!(text, "{status}");
    if let Some(rule) = &report.identity.target_rule {
        let _ = writeln!(text, "target rule: {}", rule.name.describe(&rule.id));
    }
    let classes = report
        .totals
        .classes
        .iter()
        .map(|(class, count)| format!("{} {count}", serde_name(class)))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        text,
        "cases: {}, work: {}{}",
        report.totals.cases,
        report.totals.work,
        if classes.is_empty() {
            String::new()
        } else {
            format!(" ({classes})")
        }
    );
    if let Some(count) = report.totals.pattern_body_matches {
        let _ = writeln!(
            text,
            "pattern body: {count} {} matched the pattern's configuration without its \
             `requires`, whatever the `requires` gave",
            if count == 1 { "end" } else { "ends" }
        );
    }
    if let Some(best) = &report.totals.best_score {
        let _ = writeln!(text, "{}", best_score_line(best));
    }
    if let CampaignOutcome::Aborted { reason, .. } = &report.outcome {
        let _ = writeln!(text, "reason: {reason}");
    }
    if let Some(witness) = report.witness() {
        let case = witness.shrunk.as_ref().unwrap_or(&witness.first);
        let which = if witness.shrunk.is_some() {
            "shrunk witness"
        } else {
            "witness"
        };
        let _ = writeln!(text, "{which}:");
        write_case(&mut text, case);
        if let Some(kind) = case.kill {
            write_differential(&mut text, case, kind, printers);
            for (side, command) in [
                ("baseline", &witness.krun_command),
                ("mutant", &witness.mutant_krun_command),
            ] {
                if let Some(command) = command {
                    let _ = writeln!(text, "krun ({side}): {command}");
                }
            }
        } else if let Some(command) = &witness.krun_command {
            let _ = writeln!(text, "krun: {command}");
        }
    }
    if let Some(no_witness) = report.no_witness() {
        let _ = writeln!(text, "{}", no_witness.statement);
    }
    write_unjudged(&mut text, report);
    write_coverage(&mut text, report);
    // The first `stuck` and `undefined` cases, one line each, worded as information.
    for line in report.incidental.lines() {
        let _ = writeln!(text, "{line}");
    }
    for warning in &report.warnings {
        let _ = writeln!(text, "warning: {warning}");
    }
    for defect in &report.engine_defects {
        let _ = writeln!(text, "engine defect: {}", defect.description);
    }
    text
}

/// The summary's line for the best score of the scored cases (`totals.best-score`).
fn best_score_line(best: &BestScore) -> String {
    let Some(value) = &best.best else {
        return "best score: none (no miss case was scored)".to_owned();
    };
    let level = value.level.map_or_else(
        || "no rule-graph path to the target".to_owned(),
        |level| format!("level {level}"),
    );
    let guard = value.guard_distance.as_deref().map_or_else(
        || "no guard distance".to_owned(),
        |distance| format!("guard distance {distance}"),
    );
    format!(
        "best score: {level}, {guard} (case {}; {} miss cases scored; smaller is nearer the \
         target)",
        value.case, best.scored_cases
    )
}

/// For a report with a witness, its `unsupported` and `baseline-incomplete` cases per reason,
/// largest first, with the largest one's remedy (a report without a witness says the same in
/// its no-witness statement). The every-`<k>` default is named by a report warning
/// (`every-k: …`), which the summary prints with the others.
fn write_unjudged(text: &mut String, report: &FuzzReport) {
    use std::fmt::Write as _;
    if report.witness().is_some() {
        for (label, reasons) in [
            ("unsupported", &report.totals.unsupported_reasons),
            (
                "baseline-incomplete",
                &report.totals.baseline_incomplete_reasons,
            ),
        ] {
            let mut ranked: Vec<(UnjudgedReason, u64)> = reasons
                .iter()
                .map(|(reason, count)| (*reason, *count))
                .collect();
            ranked.sort_by(|(left, left_count), (right, right_count)| {
                right_count.cmp(left_count).then(left.cmp(right))
            });
            let Some((top, _)) = ranked.first() else {
                continue;
            };
            let counts: Vec<String> = ranked
                .iter()
                .map(|(reason, count)| format!("{count} {}", reason.name()))
                .collect();
            let _ = writeln!(text, "{label} cases by reason: {}", counts.join(", "));
            if let Some(remedy) = top.remedy() {
                let _ = writeln!(text, "  for {}: {remedy}", top.name());
            }
        }
    }
}

/// The rules the cases reached, by source location, label and unique id (`totals.coverage`):
/// the rewrite rules applied, then those whose condition was entered but which never applied;
/// equations are only counted. Each list stops after [`LISTED_RULES`] rules, in source order.
fn write_coverage(text: &mut String, report: &FuzzReport) {
    use std::fmt::Write as _;
    let coverage = &report.totals.coverage;
    let rule = |id: &&String| {
        coverage
            .names
            .get(id.as_str())
            .is_none_or(|name| name.kind == CompiledRuleKind::Rewrite)
    };
    let applied: Vec<&String> = coverage.applied.iter().filter(rule).collect();
    let blocked: Vec<&String> = coverage
        .matched
        .iter()
        .filter(rule)
        .filter(|id| !coverage.applied.contains(id.as_str()))
        .collect();
    let equations = coverage.applied.len() - applied.len();
    let list = |text: &mut String, heading: String, mut ids: Vec<&String>| {
        let _ = writeln!(text, "{heading}");
        ids.sort_by_key(|id| {
            let location = coverage
                .names
                .get(id.as_str())
                .and_then(|name| name.locations.first());
            (location.is_none(), location.cloned(), (*id).clone())
        });
        for id in ids.iter().take(LISTED_RULES) {
            match coverage.names.get(id.as_str()) {
                Some(name) => {
                    let _ = writeln!(text, "  {}", name.describe(id));
                }
                None => {
                    let _ = writeln!(text, "  (not in the catalog) unique id {id}");
                }
            }
        }
        if ids.len() > LISTED_RULES {
            let _ = writeln!(
                text,
                "  ... and {} more in the report's totals.coverage (--json, --report)",
                ids.len() - LISTED_RULES
            );
        }
    };
    if !applied.is_empty() || equations > 0 {
        let heading = format!(
            "rules applied: {}{}",
            applied.len(),
            match equations {
                0 => String::new(),
                1 => " (and 1 equation)".to_owned(),
                _ => format!(" (and {equations} equations)"),
            }
        );
        list(text, heading, applied);
    }
    if !blocked.is_empty() {
        let heading = format!(
            "rules whose condition was reached but which never applied: {}",
            blocked.len()
        );
        list(text, heading, blocked);
    }
}

/// How many rules each list of [`write_coverage`] names.
const LISTED_RULES: usize = 30;

/// How many ends of each side [`write_differential`] prints.
const LISTED_ENDS: usize = 4;

/// The K-text printers of a campaign's definitions (krs-unparse's pretty form; `krust krun`
/// itself prints KORE),
/// for a differential witness's ends.
struct EndPrinters {
    baseline: Option<krs_unparse::Unparser>,
    mutant: Option<krs_unparse::Unparser>,
}

impl EndPrinters {
    fn of(baseline: &CompiledDefinition, mutant: Option<&CompiledDefinition>) -> Self {
        let printer = |definition: &CompiledDefinition| {
            krs_unparse::Unparser::from_kore(
                &definition.syntax_definition_kore,
                &definition.macros_kore,
            )
            .ok()
            .map(|printer| printer.with_program_grammar(&definition.frontend_definition))
        };
        Self {
            baseline: printer(baseline),
            mutant: mutant.and_then(printer),
        }
    }

    /// `kore`, a configuration of `role`'s definition, as K text when it prints without a
    /// warning, else as it is.
    fn show(printers: Option<&Self>, role: DefinitionRole, kore: &str) -> String {
        let printer = printers.and_then(|printers| match role {
            DefinitionRole::Baseline => printers.baseline.as_ref(),
            DefinitionRole::Mutant => printers.mutant.as_ref(),
        });
        printer
            .and_then(|printer| {
                let pattern = k_rust::kore::parser::parse_pattern(kore).ok()?;
                let output = printer.print_kore(&pattern, &krs_unparse::Options::default());
                output.warnings.is_empty().then_some(output.text)
            })
            .unwrap_or_else(|| kore.to_owned())
    }
}

/// A differential witness case beyond its hole values (FZ-POLISH S10, S-T7): the kind of kill,
/// the instantiated program, and each side's ends (its `stuck` leaves), the killing one marked,
/// with the count of leaves at an undefined step, which are no ends.
fn write_differential(
    text: &mut String,
    case: &WitnessCase,
    kind: KillKind,
    printers: Option<&EndPrinters>,
) {
    use std::fmt::Write as _;
    let _ = writeln!(
        text,
        "kill: {}",
        match kind {
            KillKind::AddedEnd => "added end (the mutant reaches an end the baseline cannot)",
            KillKind::RemovedEnd => "removed end (the baseline reaches an end the mutant cannot)",
        }
    );
    if let Some(program) = &case.program {
        let _ = writeln!(text, "program:");
        for line in program.lines() {
            let _ = writeln!(text, "  {line}");
        }
    }
    for side in &case.sides {
        let ends: Vec<(usize, &String)> = side
            .final_configurations
            .iter()
            .enumerate()
            .filter(|(index, _)| side.halts.get(*index) == Some(&HaltReasonOutput::Stuck))
            .collect();
        let undefined = side
            .halts
            .iter()
            .filter(|halt| **halt == HaltReasonOutput::Trivial)
            .count();
        let role = serde_name(&side.role);
        let _ = writeln!(
            text,
            "{role} ends: {}{}",
            ends.len(),
            match undefined {
                0 => String::new(),
                1 => " (and 1 leaf at an undefined step, which is no end)".to_owned(),
                _ => format!(" (and {undefined} leaves at an undefined step, which are no ends)"),
            }
        );
        let killing = (case.reaching.role == side.role)
            .then_some(case.reaching.leaf)
            .flatten();
        // The first ends, and the killing end wherever it lies.
        let is_killing = |index: usize| killing == u64::try_from(index).ok();
        let listed: Vec<&(usize, &String)> = ends
            .iter()
            .enumerate()
            .filter(|(position, (index, _))| *position < LISTED_ENDS || is_killing(*index))
            .map(|(_, end)| end)
            .collect();
        for (index, end) in &listed {
            let mark = if is_killing(*index) {
                " (the killing end)"
            } else {
                ""
            };
            let _ = writeln!(text, "  end {index}{mark}:");
            for line in EndPrinters::show(printers, side.role, end).lines() {
                let _ = writeln!(text, "    {line}");
            }
        }
        if ends.len() > listed.len() {
            let _ = writeln!(
                text,
                "  ... and {} more in the witness's sides (--json, --report)",
                ends.len() - listed.len()
            );
        }
    }
}

fn write_case(text: &mut String, case: &WitnessCase) {
    use std::fmt::Write as _;
    for hole in &case.holes {
        let value = hole.k_text.as_deref().unwrap_or(&hole.kore);
        let _ = writeln!(text, "  {} = {value}", hole.name);
    }
}

/// The serde name of a unit variant of the report's enums (`miss`, `work-bound`).
pub(crate) fn serde_name<T: serde::Serialize>(value: &T) -> String {
    serde_json::to_value(value)
        .ok()
        .and_then(|value| value.as_str().map(str::to_owned))
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::campaign::{CampaignFile, value_from_toml};

    /// Review round 1 nit: the killing end is printed even beyond the first ends of its side.
    #[test]
    fn the_killing_end_is_always_printed() {
        use k_rust_fuzz::report::{Reaching, WitnessSide};
        let side = |role, count: usize| WitnessSide {
            role,
            initial_configuration: "init".into(),
            final_configurations: (0..count).map(|index| format!("end-{index}")).collect(),
            halts: vec![HaltReasonOutput::Stuck; count],
        };
        let case = WitnessCase {
            holes: Vec::new(),
            program: None,
            class: k_rust_fuzz::OutcomeClass::Hit,
            sides: vec![
                side(DefinitionRole::Baseline, 1),
                side(DefinitionRole::Mutant, 7),
            ],
            reaching: Reaching {
                role: DefinitionRole::Mutant,
                leaf: Some(6),
                step: None,
            },
            kill: Some(KillKind::AddedEnd),
            steps: Some(3),
        };
        let mut text = String::new();
        write_differential(&mut text, &case, KillKind::AddedEnd, None);
        assert!(
            text.contains("  end 6 (the killing end):\n    end-6\n"),
            "{text}"
        );
        assert!(
            text.contains("  end 3:\n") && !text.contains("  end 4:"),
            "{text}"
        );
        assert!(text.contains("... and 2 more"), "{text}");
    }
    use k_rust_fuzz::Value;
    use num_bigint::BigInt;

    #[test]
    fn the_hole_shape_of_architecture_2_2_parses() {
        let file: CampaignFile = toml::from_str(
            r#"
            [[hole]]
            name = "AMOUNT"
            sort = "Int"
            program = "transfer.imp"
            line = 4
            find = "amount = 250;"
            literal = "250"
            range = { min = 0, max = 1000000 }
            "#,
        )
        .expect("the example parses");
        assert_eq!(file.hole.len(), 1);
        assert_eq!(file.hole[0].literal.as_deref(), Some("250"));
        // A column places the literal on its line (FZ-POLISH S8).
        let file: CampaignFile = toml::from_str(
            r#"
            [[hole]]
            name = "C"
            sort = "Int"
            program = "t.wat"
            line = 3
            column = 17
            literal = "3"
            "#,
        )
        .expect("a hole with a column parses");
        assert_eq!(file.hole[0].column, Some(17));
    }

    #[test]
    fn toml_values_follow_the_hole_sort() {
        let integer = toml::Value::Integer(7);
        assert_eq!(
            value_from_toml(&integer, "Int").unwrap(),
            Value::Int(BigInt::from(7))
        );
        assert!(matches!(
            value_from_toml(&integer, "MInt{8}").unwrap(),
            Value::MInt { width: 8, .. }
        ));
        assert!(value_from_toml(&toml::Value::Integer(-1), "MInt{8}").is_err());
        let table: toml::Value =
            toml::from_str(r#"int = "123456789012345678901234567890""#).expect("a table");
        assert_eq!(
            value_from_toml(&table, "Int").unwrap(),
            Value::Int("123456789012345678901234567890".parse().unwrap())
        );
    }

    #[test]
    fn seeds_are_decimal_or_hexadecimal() {
        assert_eq!(parse_seed("24301"), Ok(24301));
        assert_eq!(parse_seed("0x5eed"), Ok(0x5eed));
        assert!(parse_seed("seed").is_err());
    }

    #[test]
    fn a_rule_reference_is_read_by_its_shape() {
        use crate::campaign::rule_ref;
        use k_rust_fuzz::target::RuleRef;
        let source = |source: &str, line| RuleRef::Source {
            source: source.to_owned(),
            line,
        };
        assert_eq!(rule_ref("imp.k:47"), Ok(source("imp.k", 47)));
        assert_eq!(rule_ref("./lib/imp.k:5"), Ok(source("lib/imp.k", 5)));
        assert_eq!(rule_ref("/abs/imp.k:52"), Ok(source("/abs/imp.k", 52)));
        assert!(rule_ref("imp.k:0").is_err());
        assert!(rule_ref("imp.k:99999999999").is_err());
        // The range a multi-line rule is printed with names that rule (FZ-RULEREF review I1).
        assert_eq!(rule_ref("calc.k:28-30"), Ok(source("calc.k", 28)));
        assert_eq!(rule_ref("./calc.k:28-28"), Ok(source("calc.k", 28)));
        assert!(rule_ref("calc.k:30-28").is_err());
        assert!(rule_ref("calc.k:0-3").is_err());
        let id = "5AC0F147".repeat(8);
        assert_eq!(
            rule_ref(&id),
            Ok(RuleRef::UniqueId(id.to_ascii_lowercase()))
        );
        for label in [
            "IMP.neg", "neg", "5ac0f147", "imp.k:", ":12", "a:b", "imp.k:3-", "imp.k:-3", "a:1-2-3",
        ] {
            assert_eq!(
                rule_ref(label),
                Ok(RuleRef::Label(label.to_owned())),
                "{label}"
            );
        }
    }

    #[test]
    fn the_arguments_are_consistent() {
        use clap::CommandFactory as _;
        Args::command().debug_assert();
    }

    #[test]
    fn replay_takes_no_campaign_flag() {
        let refused = Args::try_parse_from(["krust-fuzz", "--replay", "w.json", "--seed", "1"]);
        assert!(refused.is_err());
        let relocated = Args::try_parse_from([
            "krust-fuzz",
            "--replay",
            "w.json",
            "--definition",
            "d",
            "--force",
        ]);
        assert!(relocated.is_ok());
    }
}
