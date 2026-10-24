//! The campaign the command line describes: the campaign file (ARCHITECTURE 2.2, 9.4), the flags
//! that override it, the resolved campaign a witness file records, and the library
//! [`CampaignSpec`] built from it. Every option maps onto a field of the library's
//! specification; the command line adds input conveniences and the per-case safety limit's
//! default (D24), no semantics of its own.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    sync::Arc,
};

use k_rust_fuzz::{
    Budget, CallerIdentity, CampaignSpec, CaseOptions, CompiledDefinition, Definitions, HoleDecl,
    HoleLocation, PathMode, ProgramInput, ProgramSource, ProposerConfig, SpanAddress, Target,
    TargetKind, Value,
    report::TargetRule,
    spec::{BackendRoute, DEFAULT_REJECTION_CAP, ProgramText, ProposerKind},
    target::{DifferentialTarget, PatternAt, PatternTarget, RuleMode, RuleRef, RuleTarget},
    values::{Constraints, ElementSorts, GenerationBounds, IntRange, LengthRange},
};
use num_bigint::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

/// The per-case wall-clock safety limit the command line sets unless told otherwise (D24): a
/// step whose ground function evaluation does not terminate would otherwise hang the campaign.
/// A case it stops is `timeout` and lies outside the determinism contract (ARCHITECTURE 5.4).
pub const DEFAULT_SAFETY_LIMIT_SECONDS: u64 = 60;

/// The budget of a campaign that names none.
pub const DEFAULT_CASES: u64 = 1000;

/// The campaign file: the hole declarations of ARCHITECTURE 2.2 and, optionally, everything
/// else a campaign takes. Relative paths are relative to the file's directory.
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CampaignFile {
    /// The compiled directory of the definition (the baseline of a differential campaign).
    pub definition: Option<PathBuf>,
    /// The compiled directory of the mutant; implies the differential target.
    pub mutant: Option<PathBuf>,
    /// The program file. Its text as written here is the program's name, which span holes
    /// address and the program's locations carry, as `krust krun` names a program by its path.
    pub program: Option<String>,
    /// The program parser's start sort (`krust krun --sort`).
    pub sort: Option<String>,
    /// Configuration-variable bindings, `NAME=VALUE`, as `krust krun -c` takes them.
    #[serde(default)]
    pub config_vars: Vec<String>,
    /// The campaign seed: an integer, or a string in decimal or `0x` hexadecimal.
    pub seed: Option<SeedText>,
    /// Budget: at most this many cases.
    pub cases: Option<u64>,
    /// Budget: at most this much backend work.
    pub work: Option<u64>,
    /// Rejected cases after which the campaign ends with `rejected-out`.
    pub rejection_cap: Option<u64>,
    /// The target.
    pub target: Option<TargetFile>,
    /// The case options.
    pub options: Option<OptionsFile>,
    /// The generation bounds.
    pub bounds: Option<BoundsFile>,
    /// The proposers.
    pub proposers: Option<ProposersFile>,
    /// The hole declarations (ARCHITECTURE 2.2).
    #[serde(default)]
    pub hole: Vec<HoleFile>,
}

/// A seed as written: an integer, or a string in decimal or `0x` hexadecimal.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum SeedText {
    /// A TOML integer.
    Integer(i64),
    /// A decimal or `0x` hexadecimal string.
    Text(String),
}

/// The `[target]` table: exactly one of `rule`, `pattern` and `differential` (OD-2).
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct TargetFile {
    /// A rule: `FILE:LINE` (any line of the rule), its unique id (64 hexadecimal digits), or
    /// its label (`IMP.overflow`, or `overflow` when no label is that); see [`rule_ref`].
    pub rule: Option<String>,
    /// What counts as reaching the rule; `fired` by default.
    pub mode: Option<RuleMode>,
    /// A pattern in `krust krun --pattern` syntax, which may carry `requires`.
    pub pattern: Option<String>,
    /// Where the pattern is matched; `final` by default.
    pub at: Option<PatternAt>,
    /// The differential target, between the definition and the mutant.
    pub differential: Option<bool>,
    /// A reaching case must also end naturally.
    pub run_to_completion: Option<bool>,
    /// The target is the violation of a property; a hit is reported as a property failure.
    pub negated_property: Option<bool>,
    /// Under `run-to-completion`, a rule or pattern hit's end must also be data; `true` by
    /// default.
    pub data_end: Option<bool>,
}

/// The `[options]` table (library `CaseOptions`).
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct OptionsFile {
    /// `one-path` or `all-paths`.
    pub paths: Option<PathMode>,
    /// The depth bound of every case.
    pub max_depth: Option<u64>,
    /// The work bound of every case.
    pub max_work: Option<u64>,
    /// The simplification iteration bound.
    pub max_simplification_iterations: Option<usize>,
    /// The normal-termination pattern, in `krust krun --pattern` syntax.
    pub normal_end_pattern: Option<String>,
    /// The per-case safety limit in seconds.
    pub safety_limit_seconds: Option<u64>,
    /// `true` runs cases without a safety limit.
    pub no_safety_limit: Option<bool>,
    /// Shrink a confirmed witness.
    pub shrink: Option<bool>,
    /// The solver's time limit per query, in milliseconds.
    pub smt_timeout_ms: Option<u32>,
    /// The solver's retry limit.
    pub smt_retry_limit: Option<u32>,
    /// Unjoined pairs of the definitions' critical-pair checks to read as joined, each named
    /// as the report's definition-findings name it (library `CaseOptions::assume_joined`).
    #[serde(default)]
    pub assume_joined: Vec<String>,
}

/// The `[bounds]` table (library `GenerationBounds`); omitted fields keep the defaults.
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct BoundsFile {
    /// The largest bit length of an integer without a range.
    pub int_bits: Option<u32>,
    /// The largest length without a length range.
    pub length: Option<u64>,
    /// The largest depth of a data-sort term.
    pub depth: Option<u32>,
}

/// The `[proposers]` table (library `ProposerConfig`).
#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ProposersFile {
    /// Try every hole's anchor value first.
    pub anchors_first: Option<bool>,
    /// The scheduled proposers and their weights.
    pub weights: Option<BTreeMap<ProposerKind, u32>>,
    /// Assignments tried after the anchors, each a table from hole name to value.
    #[serde(default)]
    pub explicit: Vec<BTreeMap<String, toml::Value>>,
}

/// One `[[hole]]` (ARCHITECTURE 2.2, 2.5): a span of a program text, or a configuration
/// variable.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct HoleFile {
    /// The hole's name.
    pub name: String,
    /// The hole's sort.
    pub sort: String,
    /// The addressed text: the program's name (the default) or `$NAME` for a binding's text.
    pub program: Option<String>,
    /// The one-based line of the span.
    pub line: Option<u32>,
    /// A text occurring once in the line or text and containing the literal; the literal
    /// itself by default.
    pub find: Option<String>,
    /// The hole's literal: its anchor value.
    pub literal: Option<String>,
    /// A configuration variable (without `$`) whose value is the hole, instead of a span.
    pub config_var: Option<String>,
    /// An inclusive integer range; each end an integer or a decimal string.
    pub range: Option<RangeFile>,
    /// An inclusive length range.
    pub length: Option<LengthRange>,
    /// Element sorts of a collection: `{ element = "Int" }` or `{ key = "Id", value = "Int" }`.
    pub elements: Option<ElementsFile>,
    /// The values the hole may take.
    pub choices: Option<Vec<toml::Value>>,
    /// Admit a sort the hole-sort rule refuses (ARCHITECTURE 2.4).
    pub allow_refused_sort: Option<bool>,
}

/// An integer range as written.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RangeFile {
    /// The least value.
    pub min: Option<IntText>,
    /// The greatest value.
    pub max: Option<IntText>,
}

/// An integer as written: a TOML integer, or a decimal string for any size.
#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum IntText {
    /// A TOML integer.
    Integer(i64),
    /// A decimal string.
    Text(String),
}

/// Element sorts as written.
#[derive(Debug, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ElementsFile {
    /// A `List` or `Set` element sort.
    Elements {
        /// The element sort.
        element: String,
    },
    /// A `Map`'s key and value sorts.
    Entries {
        /// The key sort.
        key: String,
        /// The value sort.
        value: String,
    },
}

/// What the flags say about the campaign; each set field overrides the campaign file.
#[derive(Debug, Default)]
pub struct Overrides {
    pub definition: Option<PathBuf>,
    pub mutant: Option<PathBuf>,
    pub program: Option<String>,
    pub sort: Option<String>,
    pub config_vars: Vec<String>,
    pub reach_rule: Option<String>,
    pub rule_mode: Option<RuleMode>,
    pub pattern: Option<String>,
    pub differential: bool,
    pub run_to_completion: Option<bool>,
    pub negated_property: Option<bool>,
    pub data_end: Option<bool>,
    pub assume_joined: Vec<String>,
    pub all_paths: Option<bool>,
    pub max_depth: Option<u64>,
    pub max_work: Option<u64>,
    pub normal_end: Option<String>,
    pub cases: Option<u64>,
    pub work: Option<u64>,
    pub seed: Option<u64>,
    pub rejection_cap: Option<u64>,
    pub safety_limit_seconds: Option<u64>,
    pub no_safety_limit: bool,
    pub shrink: Option<bool>,
    pub smt_timeout_ms: Option<u32>,
    pub smt_retry_limit: Option<u32>,
}

/// The program as the resolved campaign records it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ProgramFile {
    /// The program's name: its path as written, which span holes address.
    pub name: String,
    /// Where its text is read.
    pub path: PathBuf,
    /// The program parser's start sort.
    pub sort: String,
}

/// A campaign with every input resolved: what a witness file records, so that `--replay`
/// rebuilds the same specification. Paths are absolute.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ResolvedCampaign {
    /// The definition's compiled directory.
    pub definition: PathBuf,
    /// The mutant's compiled directory, for a differential campaign.
    pub mutant: Option<PathBuf>,
    /// The program, or `None` for a definition that runs from its configuration variables.
    pub program: Option<ProgramFile>,
    /// Configuration-variable bindings (name without `$`, value text), in order.
    pub config_vars: Vec<(String, String)>,
    /// The holes.
    pub holes: Vec<HoleDecl>,
    /// The target.
    pub target: Target,
    /// The case options.
    pub options: CaseOptions,
    /// The proposers.
    pub proposers: ProposerConfig,
    /// The generation bounds.
    pub bounds: GenerationBounds,
    /// The rejection cap.
    pub rejection_cap: u64,
    /// The seed.
    pub seed: u64,
    /// The budget.
    pub budget: Budget,
    /// The k-rust revision the report records.
    pub k_rust_revision: String,
}

/// A loaded campaign: the resolved campaign, the compiled definitions and the program text.
pub struct LoadedCampaign {
    pub resolved: ResolvedCampaign,
    pub baseline: Arc<CompiledDefinition>,
    pub mutant: Option<Arc<CompiledDefinition>>,
    pub program_text: Option<String>,
}

/// Read a campaign file.
pub fn read_campaign_file(path: &Path) -> Result<CampaignFile, String> {
    let text = std::fs::read_to_string(path).map_err(|error| {
        format!(
            "cannot read the campaign file `{}`: {error}",
            path.display()
        )
    })?;
    toml::from_str(&text)
        .map_err(|error| format!("the campaign file `{}` is invalid: {error}", path.display()))
}

/// Load a compiled directory as `krust krun --definition` loads it, with the KORE files
/// printing and reading values back need, on krun's backend route.
pub fn load_definition(directory: &Path) -> Result<CompiledDefinition, String> {
    let context = |error: Box<dyn std::error::Error>| {
        format!(
            "cannot load the compiled definition `{}`: {error}",
            directory.display()
        )
    };
    let artifact = k_rust::native::load_runnable_artifact(directory).map_err(context)?;
    let companions = k_rust::native::load_kore_companions(directory).map_err(context)?;
    let execution_definition = artifact.execution.decode().map_err(context)?;
    let kore = k_rust::kore::parser::parse_definition(&artifact.definition_kore)
        .map_err(|error| context(format!("definition.kore does not parse: {error}").into()))?;
    Ok(CompiledDefinition {
        main_module: artifact.main_module,
        syntax_module: artifact.syntax_module,
        frontend_definition: artifact.frontend_definition,
        execution_definition,
        source_table: artifact.source_table,
        configuration_variables: artifact.configuration_variables,
        kore,
        syntax_definition_kore: companions.syntax_definition_kore,
        macros_kore: companions.macros_kore,
        route: BackendRoute::SourceExecution {
            execution_rewrite_order: artifact.execution_rewrite_order,
        },
    })
}

/// `path` made absolute against `base`.
fn absolute(base: &Path, path: &Path) -> Result<PathBuf, String> {
    let joined = base.join(path);
    std::path::absolute(&joined)
        .map_err(|error| format!("cannot resolve `{}`: {error}", joined.display()))
}

/// Parse a seed: decimal or `0x` hexadecimal.
pub fn parse_seed(text: &str) -> Result<u64, String> {
    let parsed = match text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => text.parse(),
    };
    parsed.map_err(|error| format!("`{text}` is not a seed (decimal or 0x hexadecimal): {error}"))
}

/// Resolve the campaign file and the flags, and load the definitions and the program
/// (ARCHITECTURE 9.4). Flag paths are relative to the working directory, file paths to the
/// campaign file's directory.
pub fn resolve(
    file: Option<(&Path, CampaignFile)>,
    flags: Overrides,
) -> Result<LoadedCampaign, String> {
    let current = std::env::current_dir()
        .map_err(|error| format!("cannot read the working directory: {error}"))?;
    let (file_base, file) = match file {
        Some((path, file)) => (
            absolute(&current, path)?
                .parent()
                .map_or_else(|| current.clone(), Path::to_path_buf),
            file,
        ),
        None => (current.clone(), CampaignFile::default()),
    };
    let has_mutant = flags.mutant.is_some() || file.mutant.is_some();
    let budget = budget(&flags, &file)?;
    let target = target(file.target.unwrap_or_default(), &flags, has_mutant)?;
    let options = options(file.options.unwrap_or_default(), &flags)?;
    let from = |flag: Option<PathBuf>, written: Option<PathBuf>| -> Result<_, String> {
        match (flag, written) {
            (Some(path), _) => absolute(&current, &path).map(Some),
            (None, Some(path)) => absolute(&file_base, &path).map(Some),
            (None, None) => Ok(None),
        }
    };
    let definition = from(flags.definition, file.definition)?
        .ok_or("no definition: pass --definition DIR or set `definition` in the campaign file")?;
    let mutant = from(flags.mutant, file.mutant)?;
    let program = match (flags.program, file.program) {
        (Some(name), _) => Some((absolute(&current, Path::new(&name))?, name)),
        (None, Some(name)) => Some((absolute(&file_base, Path::new(&name))?, name)),
        (None, None) => None,
    };
    let bounds = bounds(&file.bounds.unwrap_or_default());
    let seed = match (flags.seed, file.seed) {
        (Some(seed), _) => seed,
        (None, Some(SeedText::Integer(seed))) => u64::try_from(seed)
            .map_err(|_| format!("the seed {seed} is negative; seeds are unsigned"))?,
        (None, Some(SeedText::Text(text))) => parse_seed(&text)?,
        (None, None) => 0,
    };
    let config_vars = config_vars(file.config_vars.iter().chain(&flags.config_vars))?;

    let baseline = Arc::new(load_definition(&definition)?);
    let mutant_definition = mutant
        .as_deref()
        .map(load_definition)
        .transpose()?
        .map(Arc::new);
    let sort = match flags.sort.or(file.sort) {
        Some(sort) => Some(sort),
        None => baseline
            .configuration_variables
            .get("PGM")
            .map(ToString::to_string),
    };
    let (program, program_text) = match program {
        Some((path, name)) => {
            let text = std::fs::read_to_string(&path).map_err(|error| {
                format!("cannot read the program `{}`: {error}", path.display())
            })?;
            let sort = sort.ok_or(
                "no start sort for the program: the definition declares no $PGM; pass --sort",
            )?;
            (Some(ProgramFile { name, path, sort }), Some(text))
        }
        None => (None, None),
    };
    let program_name = program.as_ref().map(|program| program.name.as_str());
    let holes = file
        .hole
        .into_iter()
        .map(|hole| hole_decl(hole, program_name))
        .collect::<Result<Vec<_>, String>>()?;
    let proposers = proposers(file.proposers.unwrap_or_default(), &holes)?;
    let resolved = ResolvedCampaign {
        definition,
        mutant,
        program,
        config_vars,
        holes,
        target,
        options,
        proposers,
        bounds,
        rejection_cap: flags
            .rejection_cap
            .or(file.rejection_cap)
            .unwrap_or(DEFAULT_REJECTION_CAP),
        seed,
        budget,
        // This build's identity, which nothing can replace: a hand-named revision could make
        // two builds' reports and witnesses look alike.
        k_rust_revision: k_rust::build_identity(),
    };
    Ok(LoadedCampaign {
        resolved,
        baseline,
        mutant: mutant_definition,
        program_text,
    })
}

/// `NAME=VALUE` bindings as (name without `$`, value) pairs, in order.
fn config_vars<'a>(
    assignments: impl Iterator<Item = &'a String>,
) -> Result<Vec<(String, String)>, String> {
    assignments
        .map(|assignment| {
            let (name, value) = assignment.split_once('=').ok_or_else(|| {
                format!("invalid configuration variable `{assignment}`; expected NAME=VALUE")
            })?;
            Ok((
                name.strip_prefix('$').unwrap_or(name).to_owned(),
                value.to_owned(),
            ))
        })
        .collect()
}

/// The budget: a flag's, else the campaign file's, else [`DEFAULT_CASES`] cases.
fn budget(flags: &Overrides, file: &CampaignFile) -> Result<Budget, String> {
    if let Some(cases) = flags.cases {
        return Ok(Budget::Cases(cases));
    }
    if let Some(work) = flags.work {
        return Ok(Budget::Work(work));
    }
    match (file.cases, file.work) {
        (Some(_), Some(_)) => {
            Err("the campaign file sets both `cases` and `work`; set one budget".into())
        }
        (Some(cases), None) => Ok(Budget::Cases(cases)),
        (None, Some(work)) => Ok(Budget::Work(work)),
        (None, None) => Ok(Budget::Cases(DEFAULT_CASES)),
    }
}

/// Load the definitions and the program a resolved campaign names (for `--replay`).
pub fn reload(resolved: ResolvedCampaign) -> Result<LoadedCampaign, String> {
    let baseline = Arc::new(load_definition(&resolved.definition)?);
    let mutant = resolved
        .mutant
        .as_deref()
        .map(load_definition)
        .transpose()?
        .map(Arc::new);
    let program_text = resolved
        .program
        .as_ref()
        .map(|program| {
            std::fs::read_to_string(&program.path).map_err(|error| {
                format!(
                    "cannot read the program `{}`: {error}",
                    program.path.display()
                )
            })
        })
        .transpose()?;
    Ok(LoadedCampaign {
        resolved,
        baseline,
        mutant,
        program_text,
    })
}

impl LoadedCampaign {
    /// The library specification of this campaign, with `proposers` and `options` as given
    /// (the campaign's own, or a replay's), and the caller identity the report records.
    pub fn spec(
        &self,
        proposers: ProposerConfig,
        options: CaseOptions,
        thread_stack_size: u64,
    ) -> CampaignSpec {
        let resolved = &self.resolved;
        CampaignSpec {
            definitions: Definitions {
                baseline: Arc::clone(&self.baseline),
                mutant: self.mutant.clone(),
            },
            program: ProgramInput::Source(ProgramSource {
                program: resolved
                    .program
                    .as_ref()
                    .zip(self.program_text.as_ref())
                    .map(|(program, text)| ProgramText {
                        name: program.name.clone(),
                        text: text.clone(),
                        start_sort: program.sort.clone(),
                    }),
                config_vars: resolved.config_vars.clone(),
            }),
            holes: resolved.holes.clone(),
            target: resolved.target.clone(),
            options,
            proposers,
            bounds: resolved.bounds,
            rejection_cap: resolved.rejection_cap,
            seed: resolved.seed,
            identity: CallerIdentity {
                k_rust_revision: resolved.k_rust_revision.clone(),
                thread_stack_size: Some(thread_stack_size),
            },
        }
    }
}

/// A rule reference written as text, read by its shape: `FILE:LINE`, where `LINE` is a decimal
/// number, names the rule whose source location in `FILE` spans that line (a leading `./` of
/// `FILE` is dropped); `FILE:FIRST-LAST`, the form the summary and the refusals print for a rule
/// written on several lines, names the rule that spans `FIRST`, as `FILE:FIRST` does, and the
/// command line then refuses it unless that rule spans `LAST` too ([`check_rule_range`]: a range
/// past one rule may name another); 64 hexadecimal digits are a unique id;
/// any other text is a label. Every rule has a source location and a unique id, so a label of
/// any of these shapes is still named by those.
///
/// # Errors
///
/// A `FILE:LINE` whose line is 0 or does not fit 32 bits, or a `FILE:FIRST-LAST` whose last line
/// precedes its first.
pub fn rule_ref(text: &str) -> Result<RuleRef, String> {
    let decimal = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    if let Some((file, lines)) = text.rsplit_once(':')
        && !file.is_empty()
        && (decimal(lines)
            || lines
                .split_once('-')
                .is_some_and(|(first, last)| decimal(first) && decimal(last)))
    {
        let number = |part: &str| {
            part.parse::<u32>()
                .ok()
                .filter(|line| *line > 0)
                .ok_or_else(|| {
                    format!(
                        "the rule `{text}`: a source line is a number from 1, the file's first \
                         line"
                    )
                })
        };
        let line = match lines.split_once('-') {
            None => number(lines)?,
            Some((first, last)) => {
                let (first, last) = (number(first)?, number(last)?);
                if last < first {
                    return Err(format!(
                        "the rule `{text}`: a line range runs from its first line to its last, \
                         which cannot precede it"
                    ));
                }
                first
            }
        };
        let mut source = file;
        while let Some(rest) = source.strip_prefix("./") {
            source = rest;
        }
        return Ok(RuleRef::Source {
            source: source.to_owned(),
            line,
        });
    }
    if text.len() == 64 && text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Ok(RuleRef::UniqueId(text.to_ascii_lowercase()));
    }
    Ok(RuleRef::Label(text.to_owned()))
}

/// For a rule reference written `FILE:FIRST-LAST` ([`rule_ref`]), check that the rule it
/// resolved to (by `FIRST`) spans the whole range: a range that reaches past that rule may name
/// another rule too, and a reference that could name two rules is refused (FZ-RULEREF contract).
/// Other references pass.
///
/// # Errors
///
/// When no source location of `rule` contains `FIRST..=LAST`.
pub fn check_rule_range(text: &str, rule: &TargetRule) -> Result<(), String> {
    let Some((_, lines)) = text.rsplit_once(':') else {
        return Ok(());
    };
    let Some((first, last)) = lines
        .split_once('-')
        .and_then(|(first, last)| Some((first.parse::<u32>().ok()?, last.parse::<u32>().ok()?)))
    else {
        return Ok(());
    };
    if rule
        .name
        .locations
        .iter()
        .any(|location| location.line <= first && last <= location.end_line)
    {
        return Ok(());
    }
    Err(format!(
        "the rule `{text}`: lines {first}-{last} are not inside one rule: line {first} lies in \
         {}, which ends before line {last}, so the range may name another rule too; name one \
         line of the rule, or the range the summary prints for it",
        rule.name.describe(&rule.id)
    ))
}

/// The target of the file's `[target]` table and the flags (OD-2): rules by [`rule_ref`],
/// patterns in `krust krun --pattern` syntax, and the differential target when a mutant is
/// given.
fn target(file: TargetFile, flags: &Overrides, has_mutant: bool) -> Result<Target, String> {
    // A target named by flags replaces the file's whole target kind, with its mode and `at`.
    let flag_kind = flags.reach_rule.is_some() || flags.pattern.is_some() || flags.differential;
    let (rule, pattern, differential, mode, at) = if flag_kind {
        (
            flags.reach_rule.clone(),
            flags.pattern.clone(),
            flags.differential,
            flags.rule_mode,
            None,
        )
    } else {
        (
            file.rule,
            file.pattern,
            file.differential.unwrap_or(false),
            flags.rule_mode.or(file.mode),
            file.at,
        )
    };
    let kind = match (rule, pattern, differential) {
        (Some(rule), None, false) => TargetKind::Rule(RuleTarget {
            rule: rule_ref(&rule)?,
            mode: mode.unwrap_or(RuleMode::Fired),
        }),
        (None, Some(pattern), false) => TargetKind::Pattern(PatternTarget {
            pattern,
            at: at.unwrap_or(PatternAt::Final),
        }),
        (None, None, true) => TargetKind::Differential(DifferentialTarget {}),
        (None, None, false) if has_mutant => TargetKind::Differential(DifferentialTarget {}),
        (None, None, false) => {
            return Err(
                "no target: pass --reach-rule RULE, --pattern PATTERN or --mutant DIR, \
                        or set [target] in the campaign file"
                    .into(),
            );
        }
        _ => return Err("name exactly one target: a rule, a pattern or the differential".into()),
    };
    if mode.is_some() && !matches!(kind, TargetKind::Rule(_)) {
        return Err("--rule-mode (or the file's `mode`) applies only to a rule target".into());
    }
    if at.is_some() && !matches!(kind, TargetKind::Pattern(_)) {
        return Err("the file's `at` applies only to a pattern target".into());
    }
    let data_end = flags.data_end.or(file.data_end);
    if data_end.is_some() && !matches!(kind, TargetKind::Rule(_) | TargetKind::Pattern(_)) {
        return Err(
            "--data-end, --no-data-end (or the file's `data-end`) apply only to a rule or a \
             pattern target"
                .into(),
        );
    }
    match (&kind, has_mutant) {
        (TargetKind::Differential(_), false) => {
            return Err("the differential target needs a mutant: pass --mutant DIR".into());
        }
        (TargetKind::Rule(_) | TargetKind::Pattern(_), true) => {
            return Err(
                "a mutant is given, but the target is a rule or a pattern: the mutant selects \
                 the differential target only when no other target is named"
                    .into(),
            );
        }
        _ => {}
    }
    Ok(Target {
        kind,
        run_to_completion: flags
            .run_to_completion
            .or(file.run_to_completion)
            .unwrap_or(false),
        negated_property: flags
            .negated_property
            .or(file.negated_property)
            .unwrap_or(false),
        data_end: data_end.unwrap_or(true),
    })
}

/// The case options: the library's defaults with the command line's safety limit (D24), then
/// the file's options, then the flags.
fn options(file: OptionsFile, flags: &Overrides) -> Result<CaseOptions, String> {
    let mut options = CaseOptions {
        safety_limit_ms: Some(DEFAULT_SAFETY_LIMIT_SECONDS * 1000),
        ..CaseOptions::default()
    };
    if let Some(paths) = file.paths {
        options.paths = paths;
    }
    match flags.all_paths {
        Some(true) => options.paths = PathMode::AllPaths,
        Some(false) => options.paths = PathMode::OnePath,
        None => {}
    }
    options.max_depth = flags.max_depth.or(file.max_depth);
    options.max_work = flags.max_work.or(file.max_work);
    if let Some(iterations) = file.max_simplification_iterations {
        options.max_simplification_iterations = iterations;
    }
    options.normal_end_pattern = flags.normal_end.clone().or(file.normal_end_pattern);
    if file.safety_limit_seconds.is_some() && file.no_safety_limit == Some(true) {
        return Err(
            "the campaign file sets both `safety-limit-seconds` and `no-safety-limit`".into(),
        );
    }
    // A flag overrides the file in either direction.
    let limit = if flags.no_safety_limit {
        None
    } else if let Some(seconds) = flags.safety_limit_seconds {
        Some(seconds)
    } else if file.no_safety_limit == Some(true) {
        None
    } else {
        Some(
            file.safety_limit_seconds
                .unwrap_or(DEFAULT_SAFETY_LIMIT_SECONDS),
        )
    };
    if limit == Some(0) {
        return Err(
            "a safety limit of 0 seconds would stop every case; give at least 1, or \
             --no-safety-limit"
                .into(),
        );
    }
    options.safety_limit_ms = limit.map(|seconds| seconds.saturating_mul(1000));
    if let Some(shrink) = flags.shrink.or(file.shrink) {
        options.shrink = shrink;
    }
    if let Some(timeout) = flags.smt_timeout_ms.or(file.smt_timeout_ms) {
        options.backend.smt_timeout_ms = timeout;
    }
    if let Some(limit) = flags.smt_retry_limit.or(file.smt_retry_limit) {
        options.backend.smt_retry_limit = limit;
    }
    // The flags add to the file's names; a name given twice is kept once.
    for name in file
        .assume_joined
        .into_iter()
        .chain(flags.assume_joined.iter().cloned())
    {
        if !options.assume_joined.contains(&name) {
            options.assume_joined.push(name);
        }
    }
    Ok(options)
}

fn bounds(file: &BoundsFile) -> GenerationBounds {
    let defaults = GenerationBounds::default();
    GenerationBounds {
        int_bits: file.int_bits.unwrap_or(defaults.int_bits),
        length: file.length.unwrap_or(defaults.length),
        depth: file.depth.unwrap_or(defaults.depth),
    }
}

fn proposers(file: ProposersFile, holes: &[HoleDecl]) -> Result<ProposerConfig, String> {
    let defaults = ProposerConfig::default();
    let explicit = file
        .explicit
        .into_iter()
        .enumerate()
        .map(|(index, assignment)| {
            assignment
                .into_iter()
                .map(|(name, value)| {
                    let sort = holes
                        .iter()
                        .find(|hole| hole.name == name)
                        .map(|hole| hole.sort.as_str())
                        .ok_or_else(|| {
                            format!("explicit assignment {index}: no hole is named `{name}`")
                        })?;
                    let value = value_from_toml(&value, sort).map_err(|message| {
                        format!("explicit assignment {index}, hole `{name}`: {message}")
                    })?;
                    Ok((name, value))
                })
                .collect::<Result<BTreeMap<_, _>, String>>()
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(ProposerConfig {
        anchors_first: file.anchors_first.unwrap_or(defaults.anchors_first),
        explicit,
        weights: file.weights.unwrap_or(defaults.weights),
    })
}

/// The library declaration of a `[[hole]]`.
fn hole_decl(hole: HoleFile, program: Option<&str>) -> Result<HoleDecl, String> {
    let name = hole.name;
    let span = hole.literal.is_some() || hole.find.is_some() || hole.line.is_some();
    let location = match (hole.config_var, span) {
        (Some(variable), false) if hole.program.is_none() => HoleLocation::ConfigVar {
            name: variable.strip_prefix('$').unwrap_or(&variable).to_owned(),
        },
        (Some(_), _) => {
            return Err(format!(
                "hole `{name}`: `config-var` addresses a whole variable; it takes no `program`, \
                 `line`, `find` or `literal`"
            ));
        }
        (None, _) => {
            let literal = hole.literal.ok_or_else(|| {
                format!("hole `{name}`: give its `literal` (and `find`), or a `config-var`")
            })?;
            let program = hole
                .program
                .or_else(|| program.map(str::to_owned))
                .ok_or_else(|| {
                    format!("hole `{name}`: no program to address; give the hole a `program`")
                })?;
            HoleLocation::Span(SpanAddress {
                program,
                line: hole.line,
                find: hole.find.unwrap_or_else(|| literal.clone()),
                literal,
            })
        }
    };
    let range = hole
        .range
        .map(|range| -> Result<IntRange, String> {
            Ok(IntRange {
                min: range.min.map(|end| int_text(&end)).transpose()?,
                max: range.max.map(|end| int_text(&end)).transpose()?,
            })
        })
        .transpose()
        .map_err(|message| format!("hole `{name}`: {message}"))?;
    let choices = hole
        .choices
        .map(|choices| {
            choices
                .iter()
                .map(|choice| value_from_toml(choice, &hole.sort))
                .collect::<Result<Vec<_>, String>>()
        })
        .transpose()
        .map_err(|message| format!("hole `{name}`: {message}"))?;
    Ok(HoleDecl {
        name,
        sort: hole.sort,
        location,
        constraints: Constraints {
            range,
            length: hole.length,
            elements: hole.elements.map(|elements| match elements {
                ElementsFile::Elements { element } => ElementSorts::Elements { element },
                ElementsFile::Entries { key, value } => ElementSorts::Entries { key, value },
            }),
            choices,
        },
        allow_refused_sort: hole.allow_refused_sort.unwrap_or(false),
    })
}

fn int_text(text: &IntText) -> Result<BigInt, String> {
    match text {
        IntText::Integer(value) => Ok(BigInt::from(*value)),
        IntText::Text(text) => text
            .parse()
            .map_err(|error| format!("`{text}` is not a decimal integer: {error}")),
    }
}

/// The width of an `MInt{N}` sort.
fn machine_width(sort: &str) -> Option<u32> {
    sort.strip_prefix("MInt{")?.strip_suffix('}')?.parse().ok()
}

/// A hole value written in TOML: an integer (an `Int`, or an `MInt{N}` for such a hole), a
/// boolean, a string, or a table in the library's value form (`{ int = "123" }`,
/// `{ list = [{ int = "1" }] }`, `{ token = { sort = "Id", text = "x" } }`).
pub fn value_from_toml(value: &toml::Value, sort: &str) -> Result<Value, String> {
    match value {
        toml::Value::Integer(integer) => match machine_width(sort) {
            Some(width) => u64::try_from(*integer)
                .map(|unsigned| Value::MInt {
                    width,
                    value: BigUint::from(unsigned),
                })
                .map_err(|_| format!("{integer} is negative; an {sort} value is unsigned")),
            None => Ok(Value::Int(BigInt::from(*integer))),
        },
        toml::Value::Boolean(boolean) => Ok(Value::Bool(*boolean)),
        toml::Value::String(text) => Ok(Value::String(text.clone())),
        toml::Value::Table(_) => value
            .clone()
            .try_into()
            .map_err(|error| format!("not a value: {error}")),
        other => Err(format!(
            "`{other}` is not a value; write collections and other values as tables, such as \
             {{ list = [{{ int = \"1\" }}] }}"
        )),
    }
}
