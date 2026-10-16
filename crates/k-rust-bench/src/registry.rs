//! The benchmark registry: every `*.toml` file of `benchmarks/registry/` (schema in `SCHEMA.md`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use serde::Deserialize;

pub const SEMANTICS: &[&str] = &[
    "imp", "fun", "simple", "kool", "lambda", "toy", "kevm", "kwasm", "kmir", "krs",
];
pub const OPERATIONS: &[&str] = &[
    "parse",
    "compile",
    "spec-compile",
    "load",
    "execute",
    "search",
    "prove",
    "rpc",
];
pub const REASONS: &[&str] = &[
    "no-counterpart",
    "missing-hook",
    "ref-fails",
    "ref-timeout",
    "no-claims",
];
pub const PINS: &[&str] = &[
    "k",
    "imp",
    "kevm",
    "kevm-plugin",
    "wasm",
    "mir",
    "evm-equivalence",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Tier {
    Quick,
    Standard,
    Heavy,
}

impl Tier {
    pub fn name(self) -> &'static str {
        match self {
            Tier::Quick => "quick",
            Tier::Standard => "standard",
            Tier::Heavy => "heavy",
        }
    }

    pub fn parse(text: &str) -> Option<Tier> {
        match text {
            "quick" => Some(Tier::Quick),
            "standard" => Some(Tier::Standard),
            "heavy" => Some(Tier::Heavy),
            _ => None,
        }
    }
}

impl fmt::Display for Tier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Engine {
    Krust,
    Reference,
    Command,
}

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Check {
    pub exit: Option<i32>,
    #[serde(default)]
    pub stdout: Vec<String>,
    #[serde(default)]
    pub stdout_squeezed: Vec<String>,
    #[serde(default)]
    pub stdout_absent: Vec<String>,
    #[serde(default)]
    pub files: Vec<String>,
    pub expect: Option<String>,
    pub expect_out: Option<String>,
}

impl Check {
    pub fn reads_stdout(&self) -> bool {
        !(self.stdout.is_empty()
            && self.stdout_squeezed.is_empty()
            && self.stdout_absent.is_empty())
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Prepare {
    pub name: String,
    pub engine: Engine,
    pub argv: Vec<String>,
    pub creates: String,
    #[serde(default)]
    pub prepare: Vec<String>,
    #[serde(default)]
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: Option<u64>,
}

/// One side of a workload: a single invocation (`argv`) or a short sequence (`steps`).
#[derive(Clone, Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Side {
    /// The measured side's engine: `krust` (default) or `command`, for a tool built on k-rust
    /// (such as `krs`) whose argv[0] is a path.
    pub engine: Option<Engine>,
    pub argv: Option<Vec<String>>,
    pub steps: Option<Vec<Vec<String>>>,
    #[serde(default)]
    pub prepare: Vec<String>,
    pub stdin: Option<String>,
    #[serde(default)]
    pub env: BTreeMap<String, String>,
    #[serde(default)]
    pub check: Check,
}

impl Side {
    pub fn invocations(&self) -> Vec<Vec<String>> {
        match (&self.argv, &self.steps) {
            (Some(argv), _) => vec![argv.clone()],
            (None, Some(steps)) => steps.clone(),
            (None, None) => Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ReferenceStatus {
    Paired,
    Unsupported,
    Untested,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Reference {
    pub status: ReferenceStatus,
    pub reason: Option<String>,
    pub note: Option<String>,
    pub backend: Option<String>,
    // The fields of `Side`, spelled out: serde does not combine `flatten` with
    // `deny_unknown_fields`.
    argv: Option<Vec<String>>,
    steps: Option<Vec<Vec<String>>>,
    #[serde(default)]
    prepare: Vec<String>,
    stdin: Option<String>,
    #[serde(default)]
    env: BTreeMap<String, String>,
    #[serde(default)]
    check: Check,
}

impl Reference {
    pub fn side(&self) -> Side {
        Side {
            engine: Some(Engine::Reference),
            argv: self.argv.clone(),
            steps: self.steps.clone(),
            prepare: self.prepare.clone(),
            stdin: self.stdin.clone(),
            env: self.env.clone(),
            check: self.check.clone(),
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Ladder {
    pub param: String,
    pub values: Vec<i64>,
    pub stop_seconds: Option<f64>,
    pub input: Option<String>,
    pub generator: Option<Vec<String>>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Workload {
    pub id: String,
    pub semantics: String,
    pub operation: String,
    pub title: String,
    pub stresses: String,
    pub origin: Option<String>,
    pub tier: Tier,
    pub runs: Option<u32>,
    pub warmup: Option<u32>,
    pub timeout_seconds: Option<u64>,
    pub memory_gib: Option<u64>,
    #[serde(default)]
    pub pins: Vec<String>,
    pub krust: Side,
    pub reference: Option<Reference>,
    pub ladder: Option<Ladder>,
    /// The registry file the workload was read from, for messages.
    #[serde(skip)]
    pub file: PathBuf,
}

impl Workload {
    pub fn runs(&self) -> u32 {
        if let Some(runs) = self.runs {
            return runs;
        }
        if self.ladder.is_some() {
            return 1;
        }
        match self.tier {
            Tier::Quick => 5,
            Tier::Standard => 3,
            Tier::Heavy => 1,
        }
    }

    pub fn warmup(&self) -> u32 {
        if let Some(warmup) = self.warmup {
            return warmup;
        }
        let repeated = matches!(
            self.operation.as_str(),
            "parse" | "load" | "execute" | "search" | "prove" | "rpc"
        );
        u32::from(repeated && self.tier == Tier::Quick && self.ladder.is_none())
    }

    pub fn timeout_seconds(&self) -> u64 {
        self.timeout_seconds.unwrap_or(match self.tier {
            Tier::Heavy => 3600,
            _ => 600,
        })
    }

    pub fn memory_gib(&self) -> u64 {
        self.memory_gib.unwrap_or(16)
    }

    pub fn semantics_rank(&self) -> usize {
        SEMANTICS
            .iter()
            .position(|s| *s == self.semantics)
            .unwrap_or(SEMANTICS.len())
    }

    pub fn operation_rank(&self) -> usize {
        OPERATIONS
            .iter()
            .position(|s| *s == self.operation)
            .unwrap_or(OPERATIONS.len())
    }
}

/// A semantics and operation with no workload on either side, and why.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Gap {
    pub semantics: String,
    pub operation: String,
    pub reason: String,
    pub note: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    version: u32,
    #[serde(default)]
    gap: Vec<Gap>,
    #[serde(default)]
    prepare: Vec<Prepare>,
    #[serde(default)]
    workload: Vec<Workload>,
}

pub struct Registry {
    pub prepare: BTreeMap<String, Prepare>,
    pub gaps: Vec<Gap>,
    /// Sorted by semantics, operation, then id: the report's row order.
    pub workloads: Vec<Workload>,
}

impl Registry {
    pub fn load(directory: &Path) -> Result<Registry, String> {
        let mut files: Vec<PathBuf> = std::fs::read_dir(directory)
            .map_err(|error| format!("cannot read {}: {error}", directory.display()))?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "toml"))
            .collect();
        files.sort();
        let mut prepare = BTreeMap::new();
        let mut workloads = Vec::new();
        let mut gaps = Vec::new();
        let mut errors = Vec::new();
        for path in &files {
            let text = std::fs::read_to_string(path)
                .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
            let file: File = match toml::from_str(&text) {
                Ok(file) => file,
                Err(error) => {
                    errors.push(format!("{}: {error}", path.display()));
                    continue;
                }
            };
            if file.version != 1 {
                errors.push(format!(
                    "{}: unsupported version {}",
                    path.display(),
                    file.version
                ));
            }
            for step in file.prepare {
                if prepare.contains_key(&step.name) {
                    errors.push(format!(
                        "{}: duplicate prepare step {}",
                        path.display(),
                        step.name
                    ));
                }
                prepare.insert(step.name.clone(), step);
            }
            gaps.extend(file.gap);
            for mut workload in file.workload {
                workload.file.clone_from(path);
                workloads.push(workload);
            }
        }
        workloads.sort_by(|a, b| {
            (a.semantics_rank(), a.operation_rank(), &a.id).cmp(&(
                b.semantics_rank(),
                b.operation_rank(),
                &b.id,
            ))
        });
        let registry = Registry {
            prepare,
            gaps,
            workloads,
        };
        errors.extend(registry.validate());
        if errors.is_empty() {
            Ok(registry)
        } else {
            Err(errors.join("\n"))
        }
    }

    fn validate(&self) -> Vec<String> {
        let mut errors = Vec::new();
        let mut ids = BTreeSet::new();
        for step in self.prepare.values() {
            if step.argv.is_empty() {
                errors.push(format!("prepare {}: empty argv", step.name));
            }
            for name in &step.prepare {
                if !self.prepare.contains_key(name) {
                    errors.push(format!(
                        "prepare {}: unknown prepare step {name}",
                        step.name
                    ));
                }
            }
        }
        for name in self.prepare.keys() {
            if let Err(cycle) = self.prepare_order(std::slice::from_ref(name)) {
                errors.push(cycle);
            }
        }
        for gap in &self.gaps {
            let at = format!("gap {}/{}", gap.semantics, gap.operation);
            if !SEMANTICS.contains(&gap.semantics.as_str())
                || !OPERATIONS.contains(&gap.operation.as_str())
            {
                errors.push(format!("{at}: unknown semantics or operation"));
            }
            if !REASONS.contains(&gap.reason.as_str()) && gap.reason != "no-workload" {
                errors.push(format!("{at}: unknown reason {}", gap.reason));
            }
            if self
                .workloads
                .iter()
                .any(|w| w.semantics == gap.semantics && w.operation == gap.operation)
            {
                errors.push(format!(
                    "{at}: a workload exists for it, so it is not a gap"
                ));
            }
        }
        for workload in &self.workloads {
            let at = format!("{} ({})", workload.id, workload.file.display());
            if !ids.insert(workload.id.clone()) {
                errors.push(format!("{at}: duplicate workload id"));
            }
            match workload.id.split_once('/') {
                Some((semantics, slug)) if semantics == workload.semantics && !slug.is_empty() => {}
                _ => errors.push(format!("{at}: id must be `<semantics>/<slug>`")),
            }
            if !SEMANTICS.contains(&workload.semantics.as_str()) {
                errors.push(format!("{at}: unknown semantics {}", workload.semantics));
            }
            if !OPERATIONS.contains(&workload.operation.as_str()) {
                errors.push(format!("{at}: unknown operation {}", workload.operation));
            }
            if workload.title.trim().is_empty() || workload.stresses.trim().is_empty() {
                errors.push(format!("{at}: title and stresses are required"));
            }
            for pin in &workload.pins {
                if !PINS.contains(&pin.as_str()) {
                    errors.push(format!("{at}: unknown pin {pin}"));
                }
            }
            errors.extend(self.validate_side(&at, "krust", &workload.krust));
            if workload.krust.engine == Some(Engine::Reference) {
                errors.push(format!(
                    "{at}: the measured side cannot use the reference engine"
                ));
            }
            match &workload.reference {
                None => errors.push(format!(
                    "{at}: [workload.reference] is required (paired, unsupported, or untested)"
                )),
                Some(reference) => match reference.status {
                    ReferenceStatus::Paired => {
                        errors.extend(self.validate_side(&at, "reference", &reference.side()));
                    }
                    ReferenceStatus::Unsupported => match reference.reason.as_deref() {
                        Some(reason) if REASONS.contains(&reason) => {}
                        Some(reason) => errors.push(format!("{at}: unknown reason {reason}")),
                        None => errors.push(format!("{at}: unsupported needs a reason")),
                    },
                    ReferenceStatus::Untested => {}
                },
            }
            if let Some(ladder) = &workload.ladder {
                if ladder.values.is_empty() || ladder.values.windows(2).any(|w| w[0] >= w[1]) {
                    errors.push(format!(
                        "{at}: ladder values must be ascending and non-empty"
                    ));
                }
                const RESERVED: &[&str] = &[
                    "workspace",
                    "k",
                    "imp",
                    "wasm",
                    "evm",
                    "mir",
                    "evm-equivalence",
                    "builtin",
                    "programs",
                    "kbin",
                    "krust",
                    "prepared",
                    "run",
                    "input",
                    "expect",
                ];
                if RESERVED.contains(&ladder.param.as_str()) {
                    errors.push(format!(
                        "{at}: ladder parameter {} shadows a placeholder",
                        ladder.param
                    ));
                }
                if ladder.input.is_some() == ladder.generator.is_some() {
                    errors.push(format!(
                        "{at}: a ladder needs exactly one of input or generator"
                    ));
                }
            }
        }
        errors
    }

    fn validate_side(&self, at: &str, label: &str, side: &Side) -> Vec<String> {
        let mut errors = Vec::new();
        match (&side.argv, &side.steps) {
            (Some(argv), None) if !argv.is_empty() => {}
            (None, Some(steps)) if !steps.is_empty() && steps.iter().all(|s| !s.is_empty()) => {}
            _ => errors.push(format!(
                "{at}: {label} needs exactly one non-empty argv or steps"
            )),
        }
        for name in &side.prepare {
            if !self.prepare.contains_key(name) {
                errors.push(format!("{at}: {label} names unknown prepare step {name}"));
            }
        }
        errors
    }

    /// The transitive prepare steps of `names`, dependencies first.
    pub fn prepare_order(&self, names: &[String]) -> Result<Vec<&Prepare>, String> {
        fn visit<'a>(
            registry: &'a Registry,
            name: &str,
            stack: &mut Vec<String>,
            done: &mut BTreeSet<String>,
            order: &mut Vec<&'a Prepare>,
        ) -> Result<(), String> {
            if done.contains(name) {
                return Ok(());
            }
            if stack.iter().any(|s| s == name) {
                return Err(format!("prepare cycle: {} -> {name}", stack.join(" -> ")));
            }
            let Some(step) = registry.prepare.get(name) else {
                return Err(format!("unknown prepare step {name}"));
            };
            stack.push(name.to_owned());
            for dependency in &step.prepare {
                visit(registry, dependency, stack, done, order)?;
            }
            stack.pop();
            done.insert(name.to_owned());
            order.push(step);
            Ok(())
        }
        let mut order = Vec::new();
        let mut done = BTreeSet::new();
        for name in names {
            visit(self, name, &mut Vec::new(), &mut done, &mut order)?;
        }
        Ok(order)
    }
}
