//! Compile a definition and its alpha-variants through the library route `kcompile` and `krun`
//! use, and compare what each gives.

use std::{
    cell::Cell as ThreadFlag,
    collections::{BTreeMap, BTreeSet},
    env,
    fmt::Write as _,
    fs,
    panic::{AssertUnwindSafe, catch_unwind},
    path::{Path, PathBuf},
    sync::{Arc, Once, OnceLock},
};

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ExecutionStrategy},
    builtin::embedded,
    definition::{
        Attributes, CheckMode, Definition, LOCATION_ATTRIBUTE, ResolvedDefinition,
        SOURCE_ATTRIBUTE, Sentence,
    },
    diagnostic::Severity,
    inner::parse_rule_content,
    kast::{Sort, Term},
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, ConfigurationAssembler,
        ProgramGrammar, compile_loaded_definition, compile_search_pattern,
    },
    kore::{ast::Pattern, codec, parser::parse_definition},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation},
};

use super::{
    corpus::workspace,
    kore_alpha::{
        NormalSentence, difference_signature, first_difference, first_id_difference,
        id_differences, normal_definition, normal_pattern,
    },
    rename::{
        Strategy, rename_binders, rename_sentence, rename_variable, renamed_occurrences,
        sentence_terms, variable_names,
    },
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

/// An alpha-variant of an inline case written as source text, so that it goes through the
/// parser (and its sort inference) on its own. It keeps the length of every line of the base,
/// so every location attribute agrees.
///
/// A twin gives two results: `<name>`, the twin compiled and run against the base, and
/// `<name>-parse`, the parse stage alone: the twin's loaded definition against the base's
/// loaded definition with the twin's binder renamed in its scope ([`Twin::binder`]).
#[derive(Clone, Debug)]
pub struct Twin {
    /// The result name: `text-<what the twin renames>`.
    pub name: String,
    pub text: String,
    /// The bound name the twin renames and the name it gives it: the one pair of names in which
    /// the replaced text and its replacement differ.
    pub binder: (String, String),
    /// How the base's parse is renamed for the parse stage: the quantifiers over the name, each
    /// in its scope ([`Case::twin`]), or every occurrence of a name that is one variable of its
    /// sentence, a local function's parameter or a free variable ([`Case::twin_variable`]).
    pub renames: TwinRenaming,
}

/// What the parse stage of a twin renames in the base's parse.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TwinRenaming {
    Binders,
    Variable,
}

/// A search pattern and an alpha-variant of it, both compiled against the case's compiled
/// definition through the library route of `krun --pattern`.
#[derive(Clone, Debug)]
pub struct SearchTwin {
    /// The result name: `search-<what the variant renames>`.
    pub name: String,
    pub base: String,
    pub variant: String,
}

/// The strategies every program runs under, with the names `krust krun --strategy` gives them.
pub const RUN_STRATEGIES: [(ExecutionStrategy, &str); 2] = [
    (ExecutionStrategy::All, "all"),
    (ExecutionStrategy::Any, "any"),
];

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
    /// Other main modules to try, in order, when the case does not load with `main`.
    pub mains: Vec<String>,
    /// Compile as `kcompile --for-proving` does, so the main module's claims are emitted.
    pub for_proving: bool,
    /// The compile target, `kcompile --backend` (the Rust backend by default). A sentence the
    /// Rust target refuses for a reason that names no variable is refused alike in every
    /// variant, so a binding defect of the compiled form of such a sentence is compared on a
    /// target that compiles it.
    pub target: CompilationBackend,
    pub twins: Vec<Twin>,
    pub searches: Vec<SearchTwin>,
    /// Search patterns, each with its result name, to which every strategy is applied: the
    /// pattern is parsed, renamed as a sentence is, written back as text and compiled beside the
    /// base pattern (results `<name>/<strategy>`).
    pub patterns: Vec<(String, String)>,
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
            mains: Vec::new(),
            for_proving: false,
            target: CompilationBackend::Rust,
            twins: Vec::new(),
            searches: Vec::new(),
            patterns: Vec::new(),
        }
    }

    /// The case compiled for `target`, named with the target as its last axis.
    pub fn on_target(mut self, target: CompilationBackend, axis: &str) -> Self {
        self.name = format!("{}-{axis}", self.name);
        self.target = target;
        self
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

    pub fn for_proving(mut self) -> Self {
        self.for_proving = true;
        self
    }

    /// Add the source-text twin `name`: the case's text with `from` replaced by `to`, which must
    /// have the same length and occur in the text.
    pub fn twin(mut self, name: &str, from: &str, to: &str) -> Self {
        let Text::Inline(text) = &self.text else {
            panic!("{}: a twin is written beside an inline text", self.name);
        };
        assert_eq!(
            from.len(),
            to.len(),
            "{}: {name} keeps every location",
            self.name
        );
        assert!(
            text.contains(from),
            "{}: {name} renames {from:?}",
            self.name
        );
        let names = |text: &str| -> Vec<String> {
            text.split(|character: char| !(character.is_alphanumeric() || character == '_'))
                .filter(|token| !token.is_empty())
                .map(str::to_owned)
                .collect()
        };
        let mut pairs: Vec<(String, String)> = names(from)
            .into_iter()
            .zip(names(to))
            .filter(|(left, right)| left != right)
            .collect();
        pairs.sort();
        pairs.dedup();
        assert_eq!(
            pairs.len(),
            1,
            "{}: {name} renames one bound name: {pairs:?}",
            self.name
        );
        self.twins.push(Twin {
            name: name.to_owned(),
            text: text.replace(from, to),
            binder: pairs.remove(0),
            renames: TwinRenaming::Binders,
        });
        self
    }

    /// Add the source-text twin `name`: the case's text with `from` replaced by `to`, of the same
    /// length in bytes and in characters, which renames the variable `renamed.0`, one variable of
    /// its sentence (a free variable or a local function's parameter) named nowhere else, to
    /// `renamed.1`. Its parse stage compares the twin's parse with the base's parse with every
    /// occurrence of `renamed.0` renamed.
    pub fn twin_variable(
        mut self,
        name: &str,
        from: &str,
        to: &str,
        renamed: (&str, &str),
    ) -> Self {
        let Text::Inline(text) = &self.text else {
            panic!("{}: a twin is written beside an inline text", self.name);
        };
        assert!(
            from.len() == to.len() && from.chars().count() == to.chars().count(),
            "{}: {name} keeps every location",
            self.name
        );
        assert!(
            text.contains(from),
            "{}: {name} renames {from:?}",
            self.name
        );
        assert_eq!(
            from.replace(renamed.0, renamed.1),
            to,
            "{}: {name} renames {renamed:?} only",
            self.name
        );
        self.twins.push(Twin {
            name: name.to_owned(),
            text: text.replace(from, to),
            binder: (renamed.0.to_owned(), renamed.1.to_owned()),
            renames: TwinRenaming::Variable,
        });
        self
    }

    pub fn search(mut self, name: &str, base: &str, variant: &str) -> Self {
        self.searches.push(SearchTwin {
            name: name.to_owned(),
            base: base.to_owned(),
            variant: variant.to_owned(),
        });
        self
    }

    /// Add the search pattern `name`, to which every strategy is applied.
    pub fn pattern(mut self, name: &str, text: &str) -> Self {
        self.patterns.push((name.to_owned(), text.to_owned()));
        self
    }

    /// The names of the results this case can give besides the strategies'.
    pub fn route_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for twin in &self.twins {
            names.push(twin.name.clone());
            names.push(format!("{}-parse", twin.name));
        }
        names.extend(self.searches.iter().map(|search| search.name.clone()));
        for (name, _) in &self.patterns {
            names.push(format!("{name}/*"));
            names.extend(
                Strategy::ALL
                    .iter()
                    .map(|strategy| format!("{name}/{}", strategy.name())),
            );
        }
        names
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
    /// Both compile to alpha-equivalent KORE, and a rule's `UNIQUE_ID`, a digest of the rule,
    /// differs. A claim's `UNIQUE_ID` is not compared (FU-44).
    Id,
    /// Both compile to alpha-equivalent KORE, and a run gives different leaves (only possible
    /// through a backend that reads spellings).
    Run,
    /// The parse stage of a source twin: both load, and the twin's parse is not the base's parse
    /// with the twin's binder renamed in its scope.
    Parse,
}

/// The failure of one variant: its kind, a report that holds the first KORE difference and
/// every run that differs, and a signature, the short text of the report that distinguishes
/// this failure (the differing sentence and the first differing text of each side, the first
/// diagnostic, the panic or the first differing run). The report ends with the signature.
#[derive(Clone, Debug)]
pub struct Failure {
    pub kind: Kind,
    pub report: String,
    pub signature: String,
}

impl Failure {
    fn new(kind: Kind, report: String, signature: String) -> Self {
        let signature = strip_roots(&signature);
        Failure {
            kind,
            report: format!("{}\n    at: {signature}", strip_roots(&report)),
            signature,
        }
    }
}

/// One error diagnostic of a refused compile: its code, start line and message.
type Refusal = (String, Option<u32>, String);

/// What one compile gives.
enum Compiled {
    Panic(String),
    Refused(Vec<Refusal>, String),
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

fn prefix_chars(text: &str, count: usize) -> String {
    text.chars().take(count).collect()
}

/// The checkout roots a report may name, longest first, each with the placeholder that replaces
/// it, so that a report and its signature do not depend on where the workspace lies.
fn roots() -> &'static [(String, &'static str)] {
    static ROOTS: OnceLock<Vec<(String, &'static str)>> = OnceLock::new();
    ROOTS.get_or_init(|| {
        let workspace = workspace();
        let mut roots: Vec<(String, &'static str)> = [
            (env::var_os("K_CHECKOUT").map(PathBuf::from), "${k}"),
            (Some(workspace.join("k")), "${k}"),
            (
                env::var_os("IMP_SEMANTICS_CHECKOUT").map(PathBuf::from),
                "${imp}",
            ),
            (Some(workspace.join("imp-semantics")), "${imp}"),
            (Some(workspace.clone()), "${workspace}"),
        ]
        .into_iter()
        .filter_map(|(path, placeholder)| {
            let path = fs::canonicalize(path?).ok()?;
            Some((path.display().to_string(), placeholder))
        })
        .collect();
        roots.sort_by_key(|(root, _)| std::cmp::Reverse(root.len()));
        roots
    })
}

fn strip_roots(text: &str) -> String {
    let mut text = text.to_owned();
    for (root, placeholder) in roots() {
        if text.contains(root.as_str()) {
            text = text.replace(root.as_str(), placeholder);
        }
    }
    text
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

type Loaded = (LoadedDefinition, String, String);

/// Load `case` (with `text` in place of an inline case's own text) as `kcompile` does for its
/// target: the embedded prelude, the case's requires beside it or in its include
/// directory.
fn load_text(case: &Case, text: Option<&str>) -> Result<Loaded, String> {
    let (entry, include) = match (&case.text, text) {
        (Text::Inline(_), Some(text)) => (ResolvedSource::new(case.path(), text.to_owned()), None),
        (Text::Inline(text), None) => (ResolvedSource::new(case.path(), text.clone()), None),
        (Text::File { path, include }, _) => (read_source(path)?, include.clone()),
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
    let backend = case.target;
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
            if !in_scope(sentence, scope, source) {
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

fn in_scope(sentence: &Sentence, scope: &Scope, source: &str) -> bool {
    match scope {
        // Every sentence written in a source file; a module the compiler generates (the
        // configuration-value transport) is a fixed protocol, not authored text.
        Scope::All => sentence.attributes().source().is_some(),
        Scope::OwnFile => sentence.attributes().source() == Some(source),
    }
}

/// The variable names of the sentences in `scope`, each also without its sigil: the names a
/// refusal message may spell, alone or behind another sigil (`Did you mean "?Y"?`).
fn scope_names(definition: &Definition, scope: &Scope, source: &str) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for name in definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter(|sentence| in_scope(sentence, scope, source))
        .flat_map(|sentence| variable_names(sentence))
    {
        names.insert(name.trim_start_matches(['?', '!', '@']).to_owned());
        names.insert(name);
    }
    names
}

/// The leaves of every run of `case` on the compiled `artifacts`, through `krun`'s route: the
/// definition internalized with the compiler's rewrite order (`internalize_source_definition`,
/// which joins the order to the axioms by `UNIQUE_ID`), then each program executed under each of
/// [`RUN_STRATEGIES`]. Each result is the leaves' halt reasons and states in alpha-normal form,
/// sorted, in the order program by program, then strategy by strategy.
fn runs(
    artifacts: &CompiledKoreArtifacts,
    case: &Case,
    initial: &[Pattern],
) -> Vec<Result<Vec<String>, String>> {
    if initial.is_empty() {
        return Vec::new();
    }
    let definition = parse_definition(&artifacts.definition_kore)
        .map_err(|error| format!("parse: {}", one_line(&error.to_string())))
        .and_then(|syntax| {
            Backend::internalize_source_definition(
                &syntax,
                &case.main,
                &artifacts.execution_rewrite_order,
            )
            .map_err(|error| {
                format!(
                    "internalize_source_definition: {}",
                    one_line(&error.to_string())
                )
            })
        });
    let mut results = Vec::new();
    for initial in initial {
        for (strategy, _) in RUN_STRATEGIES {
            results.push(definition.clone().and_then(|definition| {
                let mut backend = Backend::from_internalized(definition, BackendOptions::default())
                    .map_err(|error| {
                        format!("from_internalized: {}", one_line(&error.to_string()))
                    })?;
                let result = backend
                    .execute(ExecuteRequest {
                        max_depth: Some(case.depth),
                        strategy,
                        ..ExecuteRequest::new(initial.clone())
                    })
                    .map_err(|error| format!("execute: {}", one_line(&error.to_string())))?;
                let mut leaves: Vec<String> = result
                    .leaves
                    .iter()
                    .map(|leaf| {
                        let state =
                            codec::from_value(&leaf.state).expect("a result state is KORE JSON");
                        format!("{:?} {}", leaf.reason, normal_pattern(&state))
                    })
                    .collect();
                leaves.sort();
                Ok(leaves)
            }));
        }
    }
    results
}

fn compile_options(case: &Case) -> CompileOptions {
    CompileOptions {
        backend: case.target,
        hook_namespaces: case.hook_namespaces.clone(),
        // `kcompile --for-proving`: bare claims are all-path, and the checks are the proof
        // module's.
        default_claims_to_all_path: case.for_proving,
        check_mode: if case.for_proving {
            CheckMode::Proof {
                definition_module: case.main.clone(),
            }
        } else {
            CheckMode::Definition
        },
        ..CompileOptions::default()
    }
}

/// Compile `loaded`; the artifacts, or what the compile gave instead of them.
fn compile_artifacts(
    loaded: &LoadedDefinition,
    case: &Case,
) -> Result<CompiledKoreArtifacts, Compiled> {
    match guarded(|| compile_loaded_definition(loaded, compile_options(case))) {
        Err(message) => Err(Compiled::Panic(one_line(&message))),
        Ok(Err(error)) => {
            let errors: Vec<_> = error
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .collect();
            let refusals = errors
                .iter()
                .map(|diagnostic| {
                    (
                        diagnostic.code.as_str().to_owned(),
                        diagnostic.location.map(|location| location.start_line),
                        one_line(&diagnostic.message),
                    )
                })
                .collect();
            let messages = errors
                .iter()
                .map(|diagnostic| diagnostic.message.clone())
                .collect::<Vec<_>>()
                .join("; ");
            Err(Compiled::Refused(
                refusals,
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
            runs: runs(artifacts, case, initial),
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

/// The initial configuration of each program of `case`, assembled as `krun` assembles it, with
/// the program grammar of the compiled frontend definition.
fn initial_states(
    grammar: &ProgramGrammar,
    syntax: &str,
    case: &Case,
    artifacts: &CompiledKoreArtifacts,
) -> Result<Vec<Pattern>, String> {
    case.programs
        .iter()
        .map(|program| {
            let mut assembler = ConfigurationAssembler::new(
                grammar,
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
/// something (`None` for a variant that agrees with the base), and of each source twin and
/// search-pattern twin.
pub struct CaseOutcome {
    pub base: Result<String, Failure>,
    pub variants: BTreeMap<Strategy, Option<Failure>>,
    /// The results of the case's twins ([`Case::twins`], [`Case::searches`]), by name.
    pub twins: BTreeMap<String, Option<Failure>>,
}

/// Load `case`, or, for a case with other main modules, the first of them that loads; the
/// case with the main module it loaded with.
fn load_any(case: &Case) -> (Case, Result<Result<Loaded, String>, String>) {
    let first = guarded(|| load_text(case, None));
    if matches!(first, Ok(Ok(_))) || case.mains.is_empty() {
        return (case.clone(), first);
    }
    for main in &case.mains {
        let mut other = case.clone();
        other.main = main.clone();
        let loaded = guarded(|| load_text(&other, None));
        if matches!(loaded, Ok(Ok(_))) {
            return (other, loaded);
        }
    }
    (case.clone(), first)
}

/// Compile `case` and each of its variants under `strategies`, and its twins, and compare.
pub fn check(case: &Case, strategies: &[Strategy]) -> CaseOutcome {
    let base_failure = |kind, report: String, signature: String| CaseOutcome {
        base: Err(Failure::new(kind, report, signature)),
        variants: BTreeMap::new(),
        twins: BTreeMap::new(),
    };
    let (case, loaded) = load_any(case);
    let case = &case;
    let loaded = match loaded {
        Ok(Ok(loaded)) => loaded,
        Ok(Err(_)) if case.skip_unloadable => {
            return CaseOutcome {
                base: Ok("does not load; left out".to_owned()),
                variants: BTreeMap::new(),
                twins: BTreeMap::new(),
            };
        }
        Ok(Err(message)) => {
            return base_failure(
                Kind::BaseRefused,
                format!("load refused: {message}"),
                format!("load refused: {}", prefix_chars(&message, 160)),
            );
        }
        Err(message) => {
            return base_failure(
                Kind::BasePanic,
                format!("load panics: {}", one_line(&message)),
                format!("load panics: {}", prefix_chars(&one_line(&message), 160)),
            );
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
    let base_names = scope_names(&original, &case.scope, &source);
    // `krun`'s program grammar: the frontend definition the base was compiled from, resolved once
    // for the programs and the search patterns.
    let needs_grammar =
        !case.programs.is_empty() || !case.searches.is_empty() || !case.patterns.is_empty();
    let (base, initial, base_artifacts, grammar) = match compile_artifacts(&base_loaded, case) {
        Err(compiled) => (compiled, Vec::new(), None, None),
        Ok(artifacts) => {
            let grammar = needs_grammar.then(|| {
                ProgramGrammar::new(base_loaded.definition()).unwrap_or_else(|error| {
                    panic!("{}: the program grammar resolves: {error}", case.name)
                })
            });
            let initial = match &grammar {
                Some(grammar) if !case.programs.is_empty() => {
                    initial_states(grammar, &syntax, case, &artifacts).unwrap_or_else(|message| {
                        panic!("{}: the programs do not parse: {message}", case.name)
                    })
                }
                _ => Vec::new(),
            };
            (
                finish(&artifacts, case, &initial),
                initial,
                Some(artifacts),
                grammar,
            )
        }
    };
    let summary = match &base {
        Compiled::Panic(message) => {
            return base_failure(
                Kind::BasePanic,
                format!("the base panics: {message}"),
                format!("the base panics: {}", prefix_chars(message, 160)),
            );
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
        let mut names = base_names.clone();
        names.extend(scope_names(&definition, &case.scope, &source));
        let compiled = compile(&relink(definition), case, &initial);
        variants.insert(strategy, compare(case, &base, &compiled, &names));
    }
    let mut twins = BTreeMap::new();
    for twin in &case.twins {
        let mut names = base_names.clone();
        let loaded_twin = guarded(|| load_text(case, Some(&twin.text)));
        let compiled = match &loaded_twin {
            Err(message) => Compiled::Panic(format!("load panics: {}", one_line(message))),
            Ok(Err(message)) => Compiled::Refused(
                vec![("load".to_owned(), None, message.clone())],
                format!("load refused: {message}"),
            ),
            Ok(Ok((loaded, _, source))) => {
                names.extend(scope_names(loaded.definition(), &case.scope, source));
                // Relinked as the base is, so both are compiled from the same addressing.
                let relinked = loaded
                    .with_definition(loaded.definition().clone())
                    .expect("a loaded definition relinks");
                compile(&relinked, case, &initial)
            }
        };
        let parse = parse_stage(case, &original, &source, twin, &loaded_twin, &compiled);
        twins.insert(twin.name.clone(), compare(case, &base, &compiled, &names));
        twins.insert(format!("{}-parse", twin.name), parse);
    }
    if !case.searches.is_empty() || !case.patterns.is_empty() {
        let (Some(artifacts), Some(grammar)) = (&base_artifacts, &grammar) else {
            panic!("{}: a search case compiles", case.name)
        };
        twins.extend(search_results(case, grammar, artifacts));
    }
    CaseOutcome {
        base: Ok(summary),
        variants,
        twins,
    }
}

/// A loaded sentence's name for reports: its `label`, else its file's name and start position.
fn loaded_name(sentence: &Sentence, file: &str) -> String {
    if let Some(label) = sentence.attributes().get_str("label") {
        return label.to_owned();
    }
    sentence.attributes().location().map_or_else(
        || "<unlocated>".to_owned(),
        |location| format!("{file}:{}:{}", location.start_line, location.start_column),
    )
}

/// The text of a loaded sentence's terms, in textual KAST (which ignores the parser's metadata).
fn loaded_text(sentence: &Sentence) -> String {
    let mut sentence = sentence.clone();
    let Some(parts) = sentence_terms(&mut sentence) else {
        return String::new();
    };
    parts
        .terms
        .iter()
        .map(|term| one_line(&Term::to_string(term)))
        .collect::<Vec<_>>()
        .join(" | ")
}

/// The parse stage of a source twin: the twin's loaded definition against the base's loaded
/// definition with the twin's binder renamed in its scope, sentence by sentence over the case's
/// own file, compared as terms (the parser's metadata, locations included, is not compared).
/// After the parse the two are alpha-variants exactly when they are equal, since the twin renames
/// one binder and the renamed base renames the same binder the same way.
fn parse_stage(
    case: &Case,
    original: &Definition,
    source: &str,
    twin: &Twin,
    loaded_twin: &Result<Result<Loaded, String>, String>,
    compiled: &Compiled,
) -> Option<Failure> {
    let (from, to) = &twin.binder;
    let twin_loaded = match (loaded_twin, compiled) {
        (Ok(Ok((loaded, _, _))), _) => loaded,
        (Err(_), Compiled::Panic(message)) => {
            return Some(Failure::new(
                Kind::VariantPanic,
                format!("the twin {message}"),
                format!("the variant panics: {}", prefix_chars(message, 160)),
            ));
        }
        (Ok(Err(_)), Compiled::Refused(refusals, message)) => {
            return Some(Failure::new(
                Kind::VariantRefused,
                format!("the base loads and the twin is refused: {message}"),
                format!("variant refused {}", refusal_signature(refusals, message)),
            ));
        }
        _ => unreachable!("a twin's compile follows its load"),
    };
    let own = |definition: &Definition, source: &str| -> Vec<(String, Sentence)> {
        definition
            .modules
            .iter()
            .flat_map(|module| {
                module
                    .local_sentences
                    .iter()
                    .map(move |sentence| (module.name.clone(), sentence))
            })
            .filter(|(_, sentence)| in_scope(sentence, &Scope::OwnFile, source))
            .map(|(module, sentence)| (module, (**sentence).clone()))
            .collect()
    };
    let renamed: Vec<(String, Sentence)> = own(original, source)
        .into_iter()
        .map(|(module, mut sentence)| {
            match twin.renames {
                TwinRenaming::Binders => rename_binders(&mut sentence, from, to),
                TwinRenaming::Variable => rename_variable(&mut sentence, from, to),
            };
            (module, sentence)
        })
        .collect();
    let parsed = own(twin_loaded.definition(), source);
    let file = case
        .path()
        .rsplit('/')
        .next()
        .unwrap_or_default()
        .to_owned();
    let mut report = String::new();
    let mut parts = Vec::new();
    for ((module, left), (_, right)) in renamed.iter().zip(&parsed) {
        if left == right {
            continue;
        }
        let (left_text, right_text) = (loaded_text(left), loaded_text(right));
        let (left_text, right_text) = if left_text == right_text {
            (format!("{left:?}"), format!("{right:?}"))
        } else {
            (left_text, right_text)
        };
        let at = first_differing_byte(&left_text, &right_text);
        let name = loaded_name(left, &file);
        let _ = write!(
            report,
            "\n    {module}.{name}: base renamed: {left_text}\n    {module}.{name}: twin: {right_text}"
        );
        parts.push(format!(
            "{module}.{name}: base «{}» variant «{}»",
            window_at(&left_text, at),
            window_at(&right_text, at)
        ));
    }
    if renamed.len() != parsed.len() {
        parts.push(format!(
            "the twin has {} more sentences than the base",
            parsed.len() as i64 - renamed.len() as i64
        ));
    }
    (!parts.is_empty()).then(|| {
        Failure::new(
            Kind::Parse,
            format!(
                "the twin's parse is not the base's parse with {from} renamed {to} in its scope:{report}"
            ),
            parts.join("; "),
        )
    })
}

/// The window of `text` around byte `at`, from 24 characters before it, 64 characters long.
fn window_at(text: &str, at: usize) -> String {
    let start = text[..at.min(text.len())]
        .char_indices()
        .rev()
        .nth(23)
        .map_or(0, |(start, _)| start);
    prefix_chars(&text[start..], 64)
}

/// The byte at which `left` and `right` first differ.
fn first_differing_byte(left: &str, right: &str) -> usize {
    left.char_indices()
        .zip(right.chars())
        .find(|((_, a), b)| a != b)
        .map_or(left.len().min(right.len()), |((at, _), _)| at)
}

/// What compiling one search pattern gives.
enum SearchCompiled {
    Panic(String),
    Refused(Refusal),
    Pattern(String),
}

/// The attributes `krun --pattern` gives a pattern written on the command line.
fn pattern_attributes(contents: &str) -> Attributes {
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, serde_json::json!("<command line>"));
    let width = contents.chars().count();
    attributes.insert(LOCATION_ATTRIBUTE, serde_json::json!([1, 1, 1, width]));
    attributes
}

/// `text` with every `<command line>:<line>:<column>` position reduced to `<command line>`: a
/// renaming moves the columns of a one-line pattern.
fn without_positions(text: &str) -> String {
    let marker = "<command line>";
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(marker) {
        out.push_str(&rest[..at + marker.len()]);
        rest = &rest[at + marker.len()..];
        while let Some(after) = rest.strip_prefix(':')
            && after.starts_with(|character: char| character.is_ascii_digit())
        {
            rest = after.trim_start_matches(|character: char| character.is_ascii_digit());
        }
    }
    out.push_str(rest);
    out
}

/// Each search twin and each strategy's variant of each search pattern of `case`, compiled
/// against the case's compiled definition as `krun --pattern` compiles a pattern (the program
/// grammar of the compiled frontend definition and the compiled execution definition), and
/// compared with the base pattern in alpha-normal form.
fn search_results(
    case: &Case,
    grammar: &ProgramGrammar,
    artifacts: &CompiledKoreArtifacts,
) -> Vec<(String, Option<Failure>)> {
    let parsing = grammar.resolved();
    let execution = ResolvedDefinition::resolve(&artifacts.execution_definition)
        .expect("the execution definition resolves");
    let compile = |contents: &str| -> SearchCompiled {
        match guarded(|| {
            compile_search_pattern(
                parsing,
                &execution,
                &case.main,
                contents,
                pattern_attributes(contents),
            )
        }) {
            Err(message) => SearchCompiled::Panic(one_line(&message)),
            Ok(Err(error)) => {
                let debug = format!("{error:?}");
                let code = debug
                    .split(|character: char| !character.is_alphanumeric())
                    .next()
                    .unwrap_or_default()
                    .to_owned();
                SearchCompiled::Refused((
                    code,
                    None,
                    without_positions(&one_line(&error.to_string())),
                ))
            }
            Ok(Ok(compiled)) => SearchCompiled::Pattern(normal_pattern(&compiled.pattern)),
        }
    };
    let parse = |contents: &str| {
        guarded(|| parse_rule_content(parsing, &case.main, contents, pattern_attributes(contents)))
    };
    let names_of = |contents: &str| -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        if let Ok(Ok(sentence)) = parse(contents) {
            for name in variable_names(&sentence) {
                names.insert(name.trim_start_matches(['?', '!', '@']).to_owned());
                names.insert(name);
            }
        }
        names
    };
    let mut results = Vec::new();
    for search in &case.searches {
        let mut names = names_of(&search.base);
        names.extend(names_of(&search.variant));
        results.push((
            search.name.clone(),
            compare_patterns(&compile(&search.base), &compile(&search.variant), &names),
        ));
    }
    for (name, text) in &case.patterns {
        let base = compile(text);
        let parsed = match parse(text) {
            Ok(Ok(parsed)) => parsed,
            Ok(Err(error)) => {
                let message = one_line(&error.to_string());
                results.push((
                    format!("{name}/*"),
                    Some(Failure::new(
                        Kind::BaseRefused,
                        format!("the base pattern does not parse: {message}"),
                        format!(
                            "base pattern does not parse: {}",
                            prefix_chars(&message, 160)
                        ),
                    )),
                ));
                continue;
            }
            Err(message) => {
                let message = one_line(&message);
                results.push((
                    format!("{name}/*"),
                    Some(Failure::new(
                        Kind::BasePanic,
                        format!("the base pattern's parse panics: {message}"),
                        format!("base pattern parse panics: {}", prefix_chars(&message, 160)),
                    )),
                ));
                continue;
            }
        };
        if let SearchCompiled::Panic(message) = &base {
            results.push((
                format!("{name}/*"),
                Some(Failure::new(
                    Kind::BasePanic,
                    format!("the base pattern panics: {message}"),
                    format!("base pattern panics: {}", prefix_chars(message, 160)),
                )),
            ));
            continue;
        }
        for strategy in Strategy::ALL {
            let mut renamed = parsed.clone();
            if !rename_sentence(&mut renamed, strategy) {
                continue;
            }
            let mut edits = renamed_occurrences(&parsed, &renamed)
                .unwrap_or_else(|error| panic!("{}: {name}: {error}", case.name));
            edits.sort();
            let mut variant = text.clone();
            for (at, from, to) in edits.iter().rev() {
                assert_eq!(
                    variant.get(*at..at + from.len()),
                    Some(from.as_str()),
                    "{}: {name}: the occurrence of {from} lies at byte {at} of {text:?}",
                    case.name
                );
                variant.replace_range(*at..at + from.len(), to);
            }
            let mut names = names_of(text);
            names.extend(names_of(&variant));
            let failure = compare_patterns(&base, &compile(&variant), &names).map(|failure| {
                Failure::new(
                    failure.kind,
                    format!(
                        "pattern {text:?}, variant {variant:?}: {}",
                        failure
                            .report
                            .rsplit_once("\n    at: ")
                            .map_or(failure.report.as_str(), |(report, _)| report)
                    ),
                    failure.signature,
                )
            });
            results.push((format!("{name}/{}", strategy.name()), failure));
        }
    }
    results
}

/// Compare two compiled search patterns: a panic never passes; two patterns pass when their
/// alpha-normal forms are equal; two refusals pass when they have the same code and the same
/// message up to the variable names in `names`.
fn compare_patterns(
    base: &SearchCompiled,
    variant: &SearchCompiled,
    names: &BTreeSet<String>,
) -> Option<Failure> {
    let refused = |(code, _, message): &Refusal| format!("{code}: {message}");
    match (base, variant) {
        (SearchCompiled::Panic(message), _) => Some(Failure::new(
            Kind::BasePanic,
            format!("the base pattern panics: {message}"),
            format!("base pattern panics: {}", prefix_chars(message, 160)),
        )),
        (_, SearchCompiled::Panic(message)) => Some(Failure::new(
            Kind::VariantPanic,
            format!("the variant pattern panics: {message}"),
            format!("variant pattern panics: {}", prefix_chars(message, 160)),
        )),
        (SearchCompiled::Pattern(left), SearchCompiled::Pattern(right)) if left == right => None,
        (SearchCompiled::Pattern(left), SearchCompiled::Pattern(right)) => {
            let at = first_differing_byte(left, right);
            Some(Failure::new(
                Kind::Kore,
                format!(
                    "the compiled search patterns differ:\n    base:    {left}\n    variant: {right}"
                ),
                format!(
                    "pattern: base «{}» variant «{}»",
                    window_at(left, at),
                    window_at(right, at)
                ),
            ))
        }
        (SearchCompiled::Pattern(_), SearchCompiled::Refused(refusal)) => Some(Failure::new(
            Kind::VariantRefused,
            format!(
                "the base pattern compiles and the variant is refused: {}",
                refused(refusal)
            ),
            format!(
                "variant pattern refused {}",
                prefix_chars(&refused(refusal), 160)
            ),
        )),
        (SearchCompiled::Refused(refusal), SearchCompiled::Pattern(_)) => Some(Failure::new(
            Kind::BaseRefused,
            format!(
                "the base pattern is refused, and the variant compiles: {}",
                refused(refusal)
            ),
            format!(
                "base pattern refused {}",
                prefix_chars(&refused(refusal), 160)
            ),
        )),
        (SearchCompiled::Refused(left), SearchCompiled::Refused(right)) => {
            let normal = |(code, line, message): &Refusal| {
                (code.clone(), *line, without_names(message, names))
            };
            (normal(left) != normal(right)).then(|| {
                Failure::new(
                    Kind::RefusalDiffers,
                    format!(
                        "base pattern refused {}\n    variant pattern refused {}",
                        refused(left),
                        refused(right)
                    ),
                    format!(
                        "base pattern refused {} / variant pattern refused {}",
                        prefix_chars(&refused(left), 80),
                        prefix_chars(&refused(right), 80)
                    ),
                )
            })
        }
    }
}

/// `message` with every variable name in `names` replaced by `<var>`, so that two refusals
/// that differ only in the names a renaming changed compare equal. A sigil is kept, and the
/// name behind it is compared as a name.
fn without_names(message: &str, names: &BTreeSet<String>) -> String {
    let is_name = |character: char| character.is_alphanumeric() || character == '_';
    let mut out = String::with_capacity(message.len());
    let mut token = String::new();
    let flush = |token: &mut String, out: &mut String| {
        if names.contains(token.as_str()) {
            out.push_str("<var>");
        } else {
            out.push_str(token);
        }
        token.clear();
    };
    for character in message.chars() {
        if is_name(character) {
            token.push(character);
        } else {
            flush(&mut token, &mut out);
            out.push(character);
        }
    }
    flush(&mut token, &mut out);
    out
}

/// The first error diagnostic of a refusal, or, for a refusal without one, its message.
fn refusal_signature(refusals: &[Refusal], message: &str) -> String {
    refusals.first().map_or_else(
        || prefix_chars(message, 160),
        |(code, line, message)| {
            format!(
                "{code}@{}: {}",
                line.map_or("-".to_owned(), |line| line.to_string()),
                prefix_chars(message, 160)
            )
        },
    )
}

fn codes(refusals: &[Refusal]) -> Vec<(&str, Option<u32>)> {
    refusals
        .iter()
        .map(|(code, line, _)| (code.as_str(), *line))
        .collect()
}

fn compare(
    case: &Case,
    base: &Compiled,
    variant: &Compiled,
    names: &BTreeSet<String>,
) -> Option<Failure> {
    let failure =
        |kind, report: String, signature: String| Some(Failure::new(kind, report, signature));
    match (base, variant) {
        (Compiled::Panic(_), _) => unreachable!("a panicking base has no variants"),
        (_, Compiled::Panic(message)) => failure(
            Kind::VariantPanic,
            format!("the variant panics: {message}"),
            format!("the variant panics: {}", prefix_chars(message, 160)),
        ),
        (Compiled::Kore { .. }, Compiled::Refused(refusals, message)) => failure(
            Kind::VariantRefused,
            format!(
                "the base compiles and the variant is refused {:?}: {message}",
                codes(refusals)
            ),
            format!("variant refused {}", refusal_signature(refusals, message)),
        ),
        (Compiled::Refused(refusals, message), Compiled::Kore { .. }) => failure(
            Kind::BaseRefused,
            format!(
                "the base is refused {:?} and the variant compiles: {message}",
                codes(refusals)
            ),
            format!("base refused {}", refusal_signature(refusals, message)),
        ),
        (Compiled::Refused(left, left_message), Compiled::Refused(right, right_message)) => {
            // The same codes at the same lines, with the same messages up to the variable names.
            let normal = |refusals: &[Refusal]| {
                refusals
                    .iter()
                    .map(|(code, line, message)| {
                        (code.clone(), *line, without_names(message, names))
                    })
                    .collect::<Vec<_>>()
            };
            let (left_normal, right_normal) = (normal(left), normal(right));
            (left_normal != right_normal).then(|| {
                let first = left_normal
                    .iter()
                    .zip(&right_normal)
                    .position(|(a, b)| a != b)
                    .unwrap_or(left_normal.len().min(right_normal.len()));
                Failure::new(
                    Kind::RefusalDiffers,
                    format!(
                        "base refused {:?}: {left_message}\n    variant refused {:?}: {right_message}",
                        codes(left),
                        codes(right)
                    ),
                    format!(
                        "base refused {} / variant refused {}",
                        refusal_signature(&left[first.min(left.len())..], left_message),
                        refusal_signature(&right[first.min(right.len())..], right_message)
                    ),
                )
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
            let mut first_run = None;
            let labels = case.programs.iter().flat_map(|program| {
                RUN_STRATEGIES
                    .iter()
                    .map(move |(_, strategy)| (program, *strategy))
            });
            for (((program, strategy), left), right) in labels.zip(base_runs).zip(variant_runs) {
                if left != right {
                    let show = |result: &Result<Vec<String>, String>| match result {
                        Ok(leaves) => leaves
                            .iter()
                            .map(|leaf| k_cell(leaf))
                            .collect::<Vec<_>>()
                            .join(" | "),
                        Err(error) => format!("error {error}"),
                    };
                    let line = format!(
                        "run {} under {strategy}: base [{}], variant [{}]",
                        program.text.trim(),
                        show(left),
                        show(right)
                    );
                    first_run.get_or_insert_with(|| prefix_chars(&line, 200));
                    let _ = write!(runs, "\n    {line}");
                }
            }
            let ids = id_differences(base_kore, variant_kore);
            match (kore, first_run) {
                // Every differing sentence, then the first differing run and the first
                // `UNIQUE_ID` difference of a sentence whose text agrees, so that a second
                // defect in the same result changes its signature.
                (Some(kore), first_run) => {
                    let mut signature = difference_signature(base_kore, variant_kore)
                        .unwrap_or_else(|| "no difference".to_owned());
                    if let Some(first_run) = first_run {
                        let _ = write!(signature, " // {first_run}");
                    }
                    if let Some(id) = ids.first() {
                        let _ = write!(signature, " // {id}");
                    }
                    failure(Kind::Kore, format!("{kore}{runs}"), signature)
                }
                (None, Some(mut first_run)) => {
                    if let Some(id) = ids.first() {
                        let _ = write!(first_run, " // {id}");
                    }
                    failure(Kind::Run, runs.trim_start().to_owned(), first_run)
                }
                (None, None) => first_id_difference(base_kore, variant_kore)
                    .and_then(|report| failure(Kind::Id, report, ids.join("; "))),
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

/// A K-cell term with the `Lbl` prefixes, injections, the `kseq` unit and the encoded tail of a
/// `name(...)` label's name (`'LParUndsRParUnds'<module>'Unds'<sorts>`) dropped.
fn compact(text: &str) -> String {
    let text = text.replace("dotk{}()", ".");
    let mut out = String::new();
    let mut rest = text.as_str();
    while !rest.is_empty() {
        if let Some(after) = rest.strip_prefix("'LParUndsRParUnds'") {
            rest = &after[after.find(['{', '(']).unwrap_or(after.len())..];
            continue;
        }
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

/// Every case outcome in report form: one line per base failure, variant or twin result.
pub fn describe(case: &str, outcome: &CaseOutcome) -> Vec<(String, Option<Failure>)> {
    let mut lines = Vec::new();
    match &outcome.base {
        Err(failure) => lines.push((format!("{case} *"), Some(failure.clone()))),
        Ok(_) => {
            for (strategy, failure) in &outcome.variants {
                lines.push((format!("{case} {}", strategy.name()), failure.clone()));
            }
            for (twin, failure) in &outcome.twins {
                lines.push((format!("{case} {twin}"), failure.clone()));
            }
        }
    }
    lines
}
