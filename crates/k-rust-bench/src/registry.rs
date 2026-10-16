//! The benchmark registry: every `*.toml` file of `benchmarks/registry/` (schema in `SCHEMA.md`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use serde::Deserialize;

/// A prefix match where `*` matches any run of characters (`--only` and set patterns).
pub fn matches(pattern: &str, id: &str) -> bool {
    fn go(pattern: &[u8], text: &[u8]) -> bool {
        match pattern.split_first() {
            None => true,
            Some((b'*', rest)) => (0..=text.len()).any(|i| go(rest, &text[i..])),
            Some((c, rest)) => text
                .split_first()
                .is_some_and(|(t, tail)| t == c && go(rest, tail)),
        }
    }
    go(pattern.as_bytes(), id.as_bytes())
}

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
    /// The parts of the measured side's output that `kbench compare` must not require to be
    /// identical, and why.
    pub compare: Option<CompareOptOut>,
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

/// `[workload.compare]`: output that differs between runs of the same binary (timings, for
/// example), so `kbench compare` leaves it out of the output digest.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompareOptOut {
    pub reason: String,
    /// Leave standard output out of the digest.
    #[serde(default)]
    pub ignore_stdout: bool,
    /// Leave these `check.files` entries out of the digest.
    #[serde(default)]
    pub ignore_files: Vec<String>,
}

/// A named selection of workloads (`[[set]]`), for `kbench run --set` and `kbench compare --set`.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Set {
    pub name: String,
    pub description: String,
    /// Workload ids, or patterns containing `*` (a prefix match where `*` matches anything, as
    /// `--only`).
    #[serde(default)]
    pub workloads: Vec<String>,
    /// Other sets whose workloads this one includes.
    #[serde(default)]
    pub sets: Vec<String>,
    /// `kbench compare` only: the largest ladder value to run per workload id, so the set fits
    /// its time budget; `kbench run` and `compare --full-ladders` run every value.
    #[serde(default)]
    pub ladder_max: BTreeMap<String, i64>,
    /// `kbench compare` only: the default timed runs per binary and point for the workloads this
    /// set names itself, where they are noisier than the default allows (`--runs` overrides it).
    pub runs: Option<u32>,
    /// The registry file the set was read from, for messages.
    #[serde(skip)]
    pub file: PathBuf,
}

/// Whether a set entry names a workload: an exact id, or a pattern when it contains `*`.
pub fn set_entry_matches(entry: &str, id: &str) -> bool {
    if entry.contains('*') {
        matches(entry, id)
    } else {
        entry == id
    }
}

/// The workloads a selection names, and the compare ladder caps that apply to them.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Selection {
    pub ids: BTreeSet<String>,
    pub ladder_max: BTreeMap<String, i64>,
    /// Per workload id: the largest `runs` of the sets that select it.
    pub runs: BTreeMap<String, u32>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct File {
    version: u32,
    #[serde(default)]
    set: Vec<Set>,
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
    /// Named workload sets, by name.
    pub sets: BTreeMap<String, Set>,
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
        let mut sets = BTreeMap::new();
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
            for mut set in file.set {
                set.file.clone_from(path);
                if sets.contains_key(&set.name) {
                    errors.push(format!("{}: duplicate set {}", path.display(), set.name));
                }
                sets.insert(set.name.clone(), set);
            }
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
            sets,
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
            if let Some(opt_out) = &workload.compare {
                if opt_out.reason.trim().is_empty() {
                    errors.push(format!("{at}: [workload.compare] needs a reason"));
                }
                if !opt_out.ignore_stdout && opt_out.ignore_files.is_empty() {
                    errors.push(format!(
                        "{at}: [workload.compare] ignores neither stdout nor a file"
                    ));
                }
                for file in &opt_out.ignore_files {
                    if !workload.krust.check.files.contains(file) {
                        errors.push(format!(
                            "{at}: [workload.compare] ignores {file}, which is not a check file"
                        ));
                    }
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
        errors.extend(self.validate_sets());
        errors
    }

    fn validate_sets(&self) -> Vec<String> {
        let mut errors = Vec::new();
        for set in self.sets.values() {
            let at = format!("set {} ({})", set.name, set.file.display());
            if set.description.trim().is_empty() {
                errors.push(format!("{at}: description is required"));
            }
            if set.runs == Some(0) {
                errors.push(format!("{at}: runs must be at least 1"));
            }
            if set.workloads.is_empty() && set.sets.is_empty() {
                errors.push(format!("{at}: names no workloads and no sets"));
            }
            for pattern in &set.workloads {
                if !self
                    .workloads
                    .iter()
                    .any(|w| set_entry_matches(pattern, &w.id))
                {
                    errors.push(format!("{at}: {pattern} matches no workload"));
                }
            }
            for name in &set.sets {
                if !self.sets.contains_key(name) {
                    errors.push(format!("{at}: unknown set {name}"));
                }
            }
            match self.resolve_sets(std::slice::from_ref(&set.name)) {
                Err(error) => errors.push(format!("{at}: {error}")),
                Ok(selection) => {
                    for (id, cap) in &set.ladder_max {
                        if !selection.ids.contains(id) {
                            errors.push(format!(
                                "{at}: ladder_max names {id}, which is not in the set"
                            ));
                            continue;
                        }
                        let ladder = self
                            .workloads
                            .iter()
                            .find(|w| &w.id == id)
                            .and_then(|w| w.ladder.as_ref());
                        match ladder {
                            None => errors.push(format!("{at}: ladder_max names {id}, which has no ladder")),
                            Some(ladder) if !ladder.values.contains(cap) => errors.push(format!(
                                "{at}: ladder_max {id} = {cap} is not one of its ladder values {:?}",
                                ladder.values
                            )),
                            Some(_) => {}
                        }
                    }
                }
            }
        }
        errors
    }

    /// The union of the named sets: their workload ids, and the smallest ladder cap any of them
    /// (or a set they include) gives a workload.
    pub fn resolve_sets(&self, names: &[String]) -> Result<Selection, String> {
        fn visit(
            registry: &Registry,
            name: &str,
            stack: &mut Vec<String>,
            selection: &mut Selection,
        ) -> Result<(), String> {
            if stack.iter().any(|s| s == name) {
                return Err(format!("set cycle: {} -> {name}", stack.join(" -> ")));
            }
            let Some(set) = registry.sets.get(name) else {
                let known: Vec<&str> = registry.sets.keys().map(String::as_str).collect();
                return Err(format!("unknown set {name} (known: {})", known.join(", ")));
            };
            stack.push(name.to_owned());
            for included in &set.sets {
                visit(registry, included, stack, selection)?;
            }
            stack.pop();
            for workload in &registry.workloads {
                if set
                    .workloads
                    .iter()
                    .any(|p| set_entry_matches(p, &workload.id))
                {
                    selection.ids.insert(workload.id.clone());
                    if let Some(runs) = set.runs {
                        let entry = selection.runs.entry(workload.id.clone()).or_insert(runs);
                        *entry = (*entry).max(runs);
                    }
                }
            }
            for (id, cap) in &set.ladder_max {
                let entry = selection.ladder_max.entry(id.clone()).or_insert(*cap);
                *entry = (*entry).min(*cap);
            }
            Ok(())
        }
        let mut selection = Selection::default();
        for name in names {
            visit(self, name, &mut Vec::new(), &mut selection)?;
        }
        Ok(selection)
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

#[cfg(test)]
mod tests {
    use super::*;

    const WORKLOADS: &str = r#"
version = 1

[[workload]]
id = "imp/a"
semantics = "imp"
operation = "execute"
title = "a"
stresses = "a"
tier = "quick"
[workload.ladder]
param = "n"
values = [1, 2, 3, 4]
input = "${n}"
[workload.krust]
argv = ["krun", "${input}"]
[workload.reference]
status = "untested"

[[workload]]
id = "imp/b"
semantics = "imp"
operation = "execute"
title = "b"
stresses = "b"
tier = "heavy"
[workload.krust]
argv = ["krun"]
[workload.reference]
status = "untested"

[[workload]]
id = "fun/c"
semantics = "fun"
operation = "execute"
title = "c"
stresses = "c"
tier = "quick"
[workload.krust]
argv = ["krun"]
[workload.reference]
status = "untested"
"#;

    fn load(sets: &str) -> Result<Registry, String> {
        static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        let dir = std::env::temp_dir().join(format!(
            "kbench-registry-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("w.toml"), WORKLOADS).unwrap();
        std::fs::write(dir.join("sets.toml"), sets).unwrap();
        let registry = Registry::load(&dir);
        std::fs::remove_dir_all(&dir).unwrap();
        registry
    }

    #[test]
    fn sets_resolve_patterns_includes_and_the_smallest_cap() {
        let registry = load(
            r#"
version = 1
[[set]]
name = "imp"
description = "IMP"
workloads = ["imp/*"]
ladder_max = { "imp/a" = 3 }
[[set]]
name = "small"
description = "small"
workloads = ["*/c", "imp/a"]
ladder_max = { "imp/a" = 2 }
runs = 8
[[set]]
name = "all"
description = "all"
sets = ["imp", "small"]
"#,
        )
        .unwrap();
        let all = registry.resolve_sets(&["all".to_owned()]).unwrap();
        assert_eq!(
            all.ids.iter().map(String::as_str).collect::<Vec<_>>(),
            vec!["fun/c", "imp/a", "imp/b"]
        );
        assert_eq!(all.ladder_max["imp/a"], 2);
        assert_eq!(all.runs.get("imp/a"), Some(&8));
        assert_eq!(all.runs.get("fun/c"), Some(&8));
        assert_eq!(all.runs.get("imp/b"), None);
        let imp = registry.resolve_sets(&["imp".to_owned()]).unwrap();
        assert_eq!(imp.ladder_max["imp/a"], 3);
        assert!(imp.runs.is_empty());
        assert!(registry.resolve_sets(&["nope".to_owned()]).is_err());
    }

    #[test]
    fn invalid_sets_are_rejected() {
        let cases = [
            // a pattern that matches nothing
            r#"
version = 1
[[set]]
name = "x"
description = "x"
workloads = ["kevm/*"]
"#,
            // an id is exact, not a prefix
            r#"
version = 1
[[set]]
name = "x"
description = "x"
workloads = ["imp/"]
"#,
            // a cap on a workload without a ladder
            r#"
version = 1
[[set]]
name = "x"
description = "x"
workloads = ["imp/*"]
ladder_max = { "imp/b" = 1 }
"#,
            // a cap that is not a ladder value
            r#"
version = 1
[[set]]
name = "x"
description = "x"
workloads = ["imp/a"]
ladder_max = { "imp/a" = 5 }
"#,
            // a cycle
            r#"
version = 1
[[set]]
name = "x"
description = "x"
sets = ["y"]
[[set]]
name = "y"
description = "y"
sets = ["x"]
"#,
            // an unknown included set
            r#"
version = 1
[[set]]
name = "x"
description = "x"
sets = ["z"]
"#,
        ];
        for case in cases {
            assert!(load(case).is_err(), "accepted: {case}");
        }
    }
}
