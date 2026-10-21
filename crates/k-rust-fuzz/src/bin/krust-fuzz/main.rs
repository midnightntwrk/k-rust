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
use k_rust_fuzz::{
    Campaign,
    report::{CampaignOutcome, FuzzReport, HitLabel, WitnessCase},
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
    version,
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

    /// Compiled directory of the mutant; selects the differential target.
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

    /// Target: the rule with this label fires (or see --rule-mode).
    #[arg(long, value_name = "LABEL", conflicts_with_all = ["pattern", "differential"])]
    reach_rule: Option<String>,

    /// What counts as reaching the rule.
    #[arg(long, value_enum, value_name = "MODE")]
    rule_mode: Option<RuleModeArg>,

    /// Target: a clean final configuration matches this pattern (`krust krun --pattern` syntax).
    #[arg(long, value_name = "PATTERN", conflicts_with = "differential")]
    pattern: Option<String>,

    /// Target: the mutant reaches an end the baseline cannot (needs --mutant).
    #[arg(long)]
    differential: bool,

    /// A reaching case must also end naturally.
    #[arg(long)]
    run_to_completion: bool,

    /// The target is a property's violation: report a hit as a property failure.
    #[arg(long)]
    negated_property: bool,

    /// Explore every path of each input instead of k-rust's first-applicable path.
    #[arg(long)]
    all_paths: bool,

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

    /// Per-case wall-clock safety limit (60 when not set); a case it stops is a timeout,
    /// outside the determinism contract.
    #[arg(long, value_name = "SECONDS", conflicts_with = "no_safety_limit")]
    safety_limit: Option<u64>,

    /// Run cases without a wall-clock safety limit.
    #[arg(long)]
    no_safety_limit: bool,

    /// Report the first confirmed witness without shrinking it.
    #[arg(long)]
    no_shrink: bool,

    /// Solver time limit per query, in milliseconds.
    #[arg(long, value_name = "MS")]
    smt_timeout: Option<u32>,

    /// Solver retry limit.
    #[arg(long, value_name = "N")]
    smt_retry_limit: Option<u32>,

    /// The k-rust revision the report records (defaults to this build's identity).
    #[arg(long, value_name = "REVISION")]
    k_rust_revision: Option<String>,

    /// Print the report as canonical JSON instead of a summary.
    #[arg(long)]
    json: bool,

    /// Write the report as canonical JSON to FILE.
    #[arg(long, value_name = "FILE")]
    report: Option<PathBuf>,

    /// When a witness is found, write it with the campaign to FILE, for --replay.
    #[arg(long, value_name = "FILE")]
    witness: Option<PathBuf>,

    /// Replay a witness file: check its identity and re-run its witness cases. --definition,
    /// --mutant and --program then relocate the recorded inputs, and --k-rust-revision names
    /// this build's revision.
    #[arg(
        long,
        value_name = "FILE",
        conflicts_with_all = [
            "campaign", "sort", "config_vars", "reach_rule", "rule_mode", "pattern",
            "differential", "run_to_completion", "negated_property", "all_paths", "max_depth",
            "max_work", "normal_end", "cases", "work", "seed", "rejection_cap", "safety_limit",
            "no_safety_limit", "no_shrink", "smt_timeout", "smt_retry_limit", "json", "report",
            "witness",
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
    if let Some(parent) = std::env::var_os(k_rust::native::FUZZ_PARENT_BUILD_ENV) {
        let own = k_rust::native::build_identity();
        if parent.to_string_lossy() != own.as_str() {
            eprintln!(
                "error: version skew: krust is k-rust {}, but this krust-fuzz was built against \
                 k-rust {own}; install krust and krust-fuzz from one build",
                parent.to_string_lossy()
            );
            return ExitCode::from(ERROR);
        }
    }
    let args = Args::parse();
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
        run_to_completion: args.run_to_completion,
        negated_property: args.negated_property,
        all_paths: args.all_paths,
        max_depth: args.max_depth,
        max_work: args.max_work,
        normal_end: args.normal_end,
        cases: args.cases,
        work: args.work,
        seed: args.seed,
        rejection_cap: args.rejection_cap,
        safety_limit_seconds: args.safety_limit,
        no_safety_limit: args.no_safety_limit,
        no_shrink: args.no_shrink,
        smt_timeout_ms: args.smt_timeout,
        smt_retry_limit: args.smt_retry_limit,
        k_rust_revision: args.k_rust_revision,
    };
    let loaded = campaign::resolve(file, overrides, k_rust::native::build_identity())?;
    let spec = loaded.spec(
        loaded.resolved.proposers.clone(),
        loaded.resolved.options.clone(),
        STACK_SIZE as u64,
    );
    let mut campaign = Campaign::new(spec).map_err(|error| format!("campaign refused: {error}"))?;
    let report = campaign.run(loaded.resolved.budget, None);
    let json = report.to_canonical_json();
    if let Some(path) = &args.report {
        std::fs::write(path, format!("{json}\n"))
            .map_err(|error| format!("cannot write the report `{}`: {error}", path.display()))?;
    }
    if let Some(path) = &args.witness {
        if report.witness().is_some() {
            WitnessFile::write(path, &loaded.resolved, &report)?;
        } else {
            eprintln!(
                "note: no witness was found, so `{}` was not written",
                path.display()
            );
        }
    }
    if args.json {
        println!("{json}");
    } else {
        print!("{}", summary(&report));
    }
    Ok(if report.witness().is_some() {
        FOUND
    } else {
        NOT_FOUND
    })
}

fn replay_command(path: &Path, args: &Args) -> Result<u8, String> {
    let file = WitnessFile::read(path)?;
    let mut resolved = file.campaign.clone();
    // The replay's revision is this build's, which the identity check compares with the one
    // that found the witness.
    resolved.k_rust_revision = args
        .k_rust_revision
        .clone()
        .unwrap_or_else(k_rust::native::build_identity);
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
    let loaded = campaign::reload(resolved)?;
    let replay = replay::replay(&file, &loaded, args.force, STACK_SIZE as u64)?;
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

/// A human-readable summary of `report`.
fn summary(report: &FuzzReport) -> String {
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
        if let Some(command) = &witness.krun_command {
            let _ = writeln!(text, "krun: {command}");
        }
    }
    if let Some(no_witness) = report.no_witness() {
        let _ = writeln!(text, "{}", no_witness.statement);
    }
    for warning in &report.warnings {
        let _ = writeln!(text, "warning: {warning}");
    }
    for defect in &report.engine_defects {
        let _ = writeln!(text, "engine defect: {}", defect.description);
    }
    text
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
