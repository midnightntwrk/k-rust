//! Compile a definition and its alpha-variants through the library route `kcompile` and `krun`
//! use, and compare what each gives.

use std::{
    cell::Cell as ThreadFlag,
    collections::BTreeMap,
    fmt::Write as _,
    fs,
    panic::{AssertUnwindSafe, catch_unwind},
    path::{Path, PathBuf},
    sync::{Arc, Once},
};

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    definition::{Definition, Sentence},
    diagnostic::Severity,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition,
    },
    kore::{ast::Pattern, codec},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation},
};

use super::{
    kore_alpha::{
        NormalSentence, first_difference, first_id_difference, normal_definition, normal_pattern,
    },
    rename::{Strategy, rename_sentence},
};

/// Which sentences of a definition a variant renames.
#[derive(Clone, Debug)]
pub enum Scope {
    /// The sentences read from the case's own source file.
    OwnFile,
    /// Every sentence of every module read from a source file, the prelude's included.
    All,
}

/// One program run from the initial configuration, `krun`'s `$PGM` parsed at `sort`.
#[derive(Clone, Debug)]
pub struct Program {
    pub sort: String,
    pub text: String,
}

/// Where a case's definition comes from.
#[derive(Clone, Debug)]
pub enum Text {
    Inline(String),
    File {
        path: PathBuf,
        include: Option<PathBuf>,
    },
}

/// One definition of the harness: a corpus entry, a defect probe or a generated sentence.
#[derive(Clone, Debug)]
pub struct Case {
    pub name: String,
    pub text: Text,
    pub main: String,
    pub syntax: Option<String>,
    pub scope: Scope,
    pub programs: Vec<Program>,
    /// Other configuration variables, each bound to a program text.
    pub bindings: Vec<(String, String)>,
    pub depth: u64,
    pub hook_namespaces: Option<Vec<String>>,
    /// Leave the case out, rather than fail, when it does not load (a corpus file written for
    /// another main module or to test a load error).
    pub skip_unloadable: bool,
}

impl Case {
    pub fn inline(name: impl Into<String>, main: &str, text: impl Into<String>) -> Self {
        Case {
            name: name.into(),
            text: Text::Inline(text.into()),
            main: main.to_owned(),
            syntax: None,
            scope: Scope::OwnFile,
            programs: Vec::new(),
            bindings: Vec::new(),
            depth: 20,
            hook_namespaces: None,
            skip_unloadable: false,
        }
    }

    pub fn syntax(mut self, module: &str) -> Self {
        self.syntax = Some(module.to_owned());
        self
    }

    pub fn programs(mut self, sort: &str, programs: &[&str]) -> Self {
        self.programs = programs
            .iter()
            .map(|text| Program {
                sort: sort.to_owned(),
                text: (*text).to_owned(),
            })
            .collect();
        self
    }

    fn path(&self) -> String {
        match &self.text {
            Text::Inline(_) => format!("alpha_invariance/{}.k", self.name),
            Text::File { path, .. } => path.display().to_string(),
        }
    }
}

/// How a case or one of its variants failed the alpha-invariance check.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Kind {
    /// The base itself panics (a kompile invariant or an assertion), so no variant is compared.
    BasePanic,
    /// The variant panics and the base does not.
    VariantPanic,
    /// The base compiles and the variant is refused.
    VariantRefused,
    /// The base is refused and the variant compiles.
    BaseRefused,
    /// Both are refused, with different diagnostics.
    RefusalDiffers,
    /// Both compile, to KORE that is not alpha-equivalent.
    Kore,
    /// Both compile to alpha-equivalent KORE, and a sentence's `UNIQUE_ID`, a digest of the
    /// sentence, differs.
    Id,
    /// Both compile to alpha-equivalent KORE, and a run gives different leaves (only possible
    /// through a backend that reads spellings).
    Run,
}

/// The failure of one variant: its kind, and a report that holds the first KORE difference
/// and every run that differs.
#[derive(Clone, Debug)]
pub struct Failure {
    pub kind: Kind,
    pub report: String,
}

/// What one compile gives.
enum Compiled {
    Panic(String),
    Refused(Vec<(String, Option<u32>)>, String),
    Kore {
        normal: Vec<NormalSentence>,
        runs: Vec<Result<Vec<String>, String>>,
    },
}

fn one_line(text: &str) -> String {
    text.split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .chars()
        .take(400)
        .collect()
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
        .unwrap_or_default()
}

thread_local! {
    static IN_CASE: ThreadFlag<bool> = const { ThreadFlag::new(false) };
}

/// Panics inside a compile are outcomes, not test failures: keep them off standard error, and
/// report every other panic as the default hook does.
fn quiet_case_panics() {
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        let default = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !IN_CASE.with(ThreadFlag::get) {
                default(info);
            }
        }));
    });
}

fn guarded<T>(work: impl FnOnce() -> T) -> Result<T, String> {
    quiet_case_panics();
    IN_CASE.with(|flag| flag.set(true));
    let result = catch_unwind(AssertUnwindSafe(work)).map_err(panic_message);
    IN_CASE.with(|flag| flag.set(false));
    result
}

fn read_source(path: &Path) -> Result<ResolvedSource, String> {
    let canonical =
        fs::canonicalize(path).map_err(|error| format!("{}: {error}", path.display()))?;
    fs::read_to_string(&canonical)
        .map(|text| ResolvedSource::new(canonical.display().to_string(), text))
        .map_err(|error| format!("{}: {error}", canonical.display()))
}

/// Load `case` as `kcompile` does for the Rust backend: the embedded prelude, the case's
/// requires beside it or in its include directory.
fn load(case: &Case) -> Result<(LoadedDefinition, String, String), String> {
    let (entry, include) = match &case.text {
        Text::Inline(text) => (ResolvedSource::new(case.path(), text.clone()), None),
        Text::File { path, include } => (read_source(path)?, include.clone()),
    };
    let source = entry.source.clone();
    let prelude = embedded("prelude.md").expect("the embedded prelude");
    let mut resolver = |requiring: &str, required: &str| {
        if let Some(builtin) = embedded(required) {
            return Ok(builtin);
        }
        let beside = Path::new(requiring)
            .parent()
            .unwrap_or(Path::new("."))
            .join(required);
        [
            Some(beside),
            include.as_ref().map(|include| include.join(required)),
        ]
        .into_iter()
        .flatten()
        .find(|path| path.is_file())
        .ok_or_else(|| format!("cannot resolve {required} from {requiring}"))
        .and_then(|path| read_source(&path))
    };
    let backend = CompilationBackend::Rust;
    let options = LoadOptions {
        implicit_sources: vec![prelude],
        excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
        ..LoadOptions::default()
    };
    load_for_compilation(
        entry,
        case.main.clone(),
        case.syntax.as_deref(),
        &mut resolver,
        &options,
    )
    .map(|(loaded, syntax)| (loaded, syntax, source))
    .map_err(|error| one_line(&error.to_string()))
}

/// `definition` with `strategy` applied to every sentence in `scope`, and whether any changed.
pub fn variant(
    definition: &Definition,
    scope: &Scope,
    source: &str,
    strategy: Strategy,
) -> (Definition, bool) {
    let mut definition = definition.clone();
    let mut changed = false;
    for module in &mut definition.modules {
        for sentence in &mut module.local_sentences {
            let in_scope = match scope {
                // Every sentence written in a source file; a module the compiler generates
                // (the configuration-value transport) is a fixed protocol, not authored text.
                Scope::All => sentence.attributes().source().is_some(),
                Scope::OwnFile => sentence.attributes().source() == Some(source),
            };
            if !in_scope {
                continue;
            }
            let mut renamed: Sentence = (**sentence).clone();
            if rename_sentence(&mut renamed, strategy) {
                *sentence = Arc::new(renamed);
                changed = true;
            }
        }
    }
    (definition, changed)
}

/// The leaves of a run, each its halt reason and its state in alpha-normal form, sorted.
fn run(kore: &str, case: &Case, initial: &Pattern) -> Result<Vec<String>, String> {
    let mut backend = Backend::new(kore, &case.main, BackendOptions::default())
        .map_err(|error| format!("Backend::new: {}", one_line(&error.to_string())))?;
    let result = backend
        .execute(ExecuteRequest {
            max_depth: Some(case.depth),
            ..ExecuteRequest::new(initial.clone())
        })
        .map_err(|error| format!("execute: {}", one_line(&error.to_string())))?;
    let mut leaves: Vec<String> = result
        .leaves
        .iter()
        .map(|leaf| {
            let state = codec::from_value(&leaf.state).expect("a result state is KORE JSON");
            format!("{:?} {}", leaf.reason, normal_pattern(&state))
        })
        .collect();
    leaves.sort();
    Ok(leaves)
}

/// Compile `loaded`; the artifacts, or what the compile gave instead of them.
fn compile_artifacts(
    loaded: &LoadedDefinition,
    case: &Case,
) -> Result<CompiledKoreArtifacts, Compiled> {
    let options = CompileOptions {
        backend: CompilationBackend::Rust,
        hook_namespaces: case.hook_namespaces.clone(),
        ..CompileOptions::default()
    };
    match guarded(|| compile_loaded_definition(loaded, options)) {
        Err(message) => Err(Compiled::Panic(one_line(&message))),
        Ok(Err(error)) => {
            let codes = error
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .map(|diagnostic| {
                    (
                        diagnostic.code.as_str().to_owned(),
                        diagnostic.location.map(|location| location.start_line),
                    )
                })
                .collect();
            let messages = error
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .map(|diagnostic| diagnostic.message.clone())
                .collect::<Vec<_>>()
                .join("; ");
            Err(Compiled::Refused(
                codes,
                one_line(&format!("{error}: {messages}")),
            ))
        }
        Ok(Ok(artifacts)) => Ok(artifacts),
    }
}

/// The normal form of compiled artifacts and the runs of `initial` on them.
fn finish(artifacts: &CompiledKoreArtifacts, case: &Case, initial: &[Pattern]) -> Compiled {
    // The macros a definition declares are compiled KORE too: a macro no rule applies appears
    // only there.
    let normal = || -> Result<Vec<NormalSentence>, String> {
        let mut normal = normal_definition(&artifacts.definition_kore)?;
        // `macros.kore` is a list of axioms; read it as the one module of a definition.
        if !artifacts.macros_kore.trim().is_empty() {
            normal.extend(normal_definition(&format!(
                "[]\nmodule MACROS\n{}\nendmodule []\n",
                artifacts.macros_kore
            ))?);
        }
        Ok(normal)
    };
    let result = guarded(|| match normal() {
        // Compiled KORE that does not parse is never a refusal both sides could agree on.
        Err(error) => Compiled::Panic(format!("the compiled KORE does not parse: {error}")),
        Ok(normal) => Compiled::Kore {
            runs: initial
                .iter()
                .map(|initial| run(&artifacts.definition_kore, case, initial))
                .collect(),
            normal,
        },
    });
    result.unwrap_or_else(|message| Compiled::Panic(one_line(&message)))
}

fn compile(loaded: &LoadedDefinition, case: &Case, initial: &[Pattern]) -> Compiled {
    match compile_artifacts(loaded, case) {
        Ok(artifacts) => finish(&artifacts, case, initial),
        Err(compiled) => compiled,
    }
}

/// The initial configuration of each program of `case`, assembled as `krun` assembles it.
fn initial_states(
    loaded: &LoadedDefinition,
    syntax: &str,
    case: &Case,
    artifacts: &CompiledKoreArtifacts,
) -> Result<Vec<Pattern>, String> {
    let grammar = ProgramGrammar::new(loaded.definition()).map_err(|error| error.to_string())?;
    case.programs
        .iter()
        .map(|program| {
            let mut assembler = ConfigurationAssembler::new(
                &grammar,
                case.main.clone(),
                syntax.to_owned(),
                &artifacts.configuration_variables,
            );
            assembler
                .program(&Sort::new(program.sort.as_str()), &program.text)
                .map_err(|error| format!("{}: {error}", program.text))?;
            for (name, text) in &case.bindings {
                assembler
                    .bind(name, text)
                    .map_err(|error| format!("{name}: {error}"))?;
            }
            // `krun --io off` with standard input from /dev/null.
            assembler
                .bind_stream_defaults(false, false, || {
                    Ok::<_, k_rust::kompile::ConfigurationError>(Vec::new())
                })
                .map_err(|error| error.to_string())?;
            assembler.finish().map_err(|error| error.to_string())
        })
        .collect()
}

/// What a case gives: a failure of the base, or the result of each strategy that renamed
/// something (`None` for a variant that agrees with the base).
pub struct CaseOutcome {
    pub base: Result<String, Failure>,
    pub variants: BTreeMap<Strategy, Option<Failure>>,
}

/// Compile `case` and each of its variants under `strategies`, and compare.
pub fn check(case: &Case, strategies: &[Strategy]) -> CaseOutcome {
    let failure = |kind, report: String| Failure { kind, report };
    let loaded = match guarded(|| load(case)) {
        Ok(Ok(loaded)) => loaded,
        Ok(Err(_)) if case.skip_unloadable => {
            return CaseOutcome {
                base: Ok("does not load; left out".to_owned()),
                variants: BTreeMap::new(),
            };
        }
        Ok(Err(message)) => {
            return CaseOutcome {
                base: Err(failure(
                    Kind::BaseRefused,
                    format!("load refused: {message}"),
                )),
                variants: BTreeMap::new(),
            };
        }
        Err(message) => {
            return CaseOutcome {
                base: Err(failure(
                    Kind::BasePanic,
                    format!("load panics: {}", one_line(&message)),
                )),
                variants: BTreeMap::new(),
            };
        }
    };
    let (loaded, syntax, source) = loaded;
    let original = loaded.definition().clone();
    // The base is relinked like every variant, so both are compiled from the same addressing.
    let relink = |definition: Definition| {
        loaded
            .with_definition(definition)
            .expect("a renaming keeps the loaded stage")
    };
    let base_loaded = relink(original.clone());
    let (base, initial) = match compile_artifacts(&base_loaded, case) {
        Err(compiled) => (compiled, Vec::new()),
        Ok(artifacts) => {
            let initial = if case.programs.is_empty() {
                Vec::new()
            } else {
                initial_states(&loaded, &syntax, case, &artifacts).unwrap_or_else(|message| {
                    panic!("{}: the programs do not parse: {message}", case.name)
                })
            };
            (finish(&artifacts, case, &initial), initial)
        }
    };
    let summary = match &base {
        Compiled::Panic(message) => {
            return CaseOutcome {
                base: Err(failure(
                    Kind::BasePanic,
                    format!("the base panics: {message}"),
                )),
                variants: BTreeMap::new(),
            };
        }
        Compiled::Refused(codes, _) => format!("refused {codes:?}"),
        Compiled::Kore { runs, .. } => format!("compiles; {} runs", runs.len()),
    };
    let mut variants = BTreeMap::new();
    for &strategy in strategies {
        let (definition, changed) = variant(&original, &case.scope, &source, strategy);
        if !changed {
            continue;
        }
        let compiled = compile(&relink(definition), case, &initial);
        variants.insert(strategy, compare(case, &base, &compiled));
    }
    CaseOutcome {
        base: Ok(summary),
        variants,
    }
}

fn compare(case: &Case, base: &Compiled, variant: &Compiled) -> Option<Failure> {
    let failure = |kind, report: String| Some(Failure { kind, report });
    match (base, variant) {
        (Compiled::Panic(_), _) => unreachable!("a panicking base has no variants"),
        (_, Compiled::Panic(message)) => {
            failure(Kind::VariantPanic, format!("the variant panics: {message}"))
        }
        (Compiled::Kore { .. }, Compiled::Refused(codes, message)) => failure(
            Kind::VariantRefused,
            format!("the base compiles and the variant is refused {codes:?}: {message}"),
        ),
        (Compiled::Refused(codes, message), Compiled::Kore { .. }) => failure(
            Kind::BaseRefused,
            format!("the base is refused {codes:?} and the variant compiles: {message}"),
        ),
        (Compiled::Refused(left, left_message), Compiled::Refused(right, right_message)) => {
            (left != right).then(|| Failure {
                kind: Kind::RefusalDiffers,
                report: format!(
                    "base refused {left:?}: {left_message}\n    variant refused {right:?}: {right_message}"
                ),
            })
        }
        (
            Compiled::Kore {
                normal: base_kore,
                runs: base_runs,
            },
            Compiled::Kore {
                normal: variant_kore,
                runs: variant_runs,
            },
        ) => {
            let kore = first_difference(base_kore, variant_kore);
            let mut runs = String::new();
            for ((program, left), right) in case.programs.iter().zip(base_runs).zip(variant_runs) {
                if left != right {
                    let show = |result: &Result<Vec<String>, String>| match result {
                        Ok(leaves) => leaves
                            .iter()
                            .map(|leaf| k_cell(leaf))
                            .collect::<Vec<_>>()
                            .join(" | "),
                        Err(error) => format!("error {error}"),
                    };
                    let _ = write!(
                        runs,
                        "\n    run {}: base [{}], variant [{}]",
                        program.text,
                        show(left),
                        show(right)
                    );
                }
            }
            match (kore, runs.is_empty()) {
                (Some(kore), _) => failure(Kind::Kore, format!("{kore}{runs}")),
                (None, false) => failure(Kind::Run, runs.trim_start().to_owned()),
                (None, true) => first_id_difference(base_kore, variant_kore)
                    .and_then(|report| failure(Kind::Id, report)),
            }
        }
    }
}

/// The halt reason and the content of the `<k>` cell of a normalised leaf, for reports.
fn k_cell(leaf: &str) -> String {
    let (reason, state) = leaf.split_once(' ').unwrap_or((leaf, ""));
    let marker = "Lbl'-LT-'k'-GT-'{}(";
    let Some(start) = state.find(marker) else {
        return format!("{reason} {}", state.chars().take(160).collect::<String>());
    };
    let rest = &state[start + marker.len()..];
    let mut depth = 1usize;
    let mut end = rest.len();
    for (index, character) in rest.char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = index;
                    break;
                }
            }
            _ => {}
        }
    }
    let constrained = !state.starts_with("Lbl'-LT-'generatedTop'-GT-'");
    format!(
        "{reason} {}{}",
        compact(&rest[..end]),
        if constrained { " (constrained)" } else { "" }
    )
}

/// A K-cell term with the `Lbl` prefixes, injections and the `kseq` unit dropped.
fn compact(text: &str) -> String {
    let text = text.replace("dotk{}()", ".");
    let mut out = String::new();
    let mut rest = text.as_str();
    while !rest.is_empty() {
        if let Some(after) = rest.strip_prefix("inj{") {
            let close = after.find("}(").map_or(0, |close| close + 2);
            rest = &after[close..];
            out.push('(');
            continue;
        }
        if let Some(after) = rest.strip_prefix("Lbl") {
            rest = after;
            continue;
        }
        if let Some(after) = rest.strip_prefix("\\dv{") {
            let close = after.find("}(").map_or(0, |close| close + 2);
            rest = &after[close..];
            out.push('(');
            continue;
        }
        let character = rest.chars().next().unwrap();
        out.push(character);
        rest = &rest[character.len_utf8()..];
    }
    out.replace("{}", "")
}

/// Every case outcome in report form: one line per base failure or variant result.
pub fn describe(case: &str, outcome: &CaseOutcome) -> Vec<(String, Option<Failure>)> {
    let mut lines = Vec::new();
    match &outcome.base {
        Err(failure) => lines.push((format!("{case} *"), Some(failure.clone()))),
        Ok(_) => {
            for (strategy, failure) in &outcome.variants {
                lines.push((format!("{case} {}", strategy.name()), failure.clone()));
            }
        }
    }
    lines
}
