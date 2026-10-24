//! The campaign specification: everything a campaign's report is a function of, apart from the
//! budget (ARCHITECTURE 5.4, 9.2).

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    backend::{BackendOptions, ExecutionDigest},
    definition::Definition as FrontendDefinition,
    definition::json::to_provenance_string,
    kast::Sort as KastSort,
    kompile::{CompiledKoreArtifacts, retain_pattern_sentences, retain_runtime_frontend_sentences},
    kore::ast::Definition as KoreDefinition,
    kore::ast::Pattern as KorePattern,
    provenance::SourceTable,
};
use serde::{Deserialize, Serialize};

use crate::{
    error::CampaignError,
    holes::HoleDecl,
    source_names::SourceNames,
    target::Target,
    values::{GenerationBounds, Value},
};

/// The `max_work` a campaign uses when its [`CaseOptions`] set neither `max_depth` nor
/// `max_work` (ARCHITECTURE 5.1, R-7): every case is bounded, and the bound is recorded in the
/// report's options.
pub const DEFAULT_MAX_WORK: u64 = 100_000;

/// The number of rejected cases after which a campaign ends with
/// [`crate::report::CampaignOutcome::RejectedOut`] unless the specification sets another cap
/// (ARCHITECTURE 9.2).
pub const DEFAULT_REJECTION_CAP: u64 = 10_000;

/// One campaign: one program, its holes, one target, the options of every case, the proposers
/// and the seed (ARCHITECTURE 1, 9.2).
///
/// [`crate::Campaign::new`] validates it; nothing in it is modified or written to disk.
#[derive(Clone, Debug)]
pub struct CampaignSpec {
    /// The definition, or the baseline and the mutant for a differential target, built by the
    /// caller and passed in memory (ARCHITECTURE 4.3).
    pub definitions: Definitions,
    /// The unmodified program and its configuration-variable bindings, or a KORE template.
    pub program: ProgramInput,
    /// The hole overlay on [`Self::program`] (ARCHITECTURE 2.2).
    pub holes: Vec<HoleDecl>,
    /// What a case must do to be a hit (ARCHITECTURE 4).
    pub target: Target,
    /// The execution options of every case (ARCHITECTURE 5.1).
    pub options: CaseOptions,
    /// Which proposers run and with which weights (ARCHITECTURE 8).
    pub proposers: ProposerConfig,
    /// Default bounds of generated values; the report records them (ARCHITECTURE 2.5).
    pub bounds: GenerationBounds,
    /// Rejected cases after which the campaign ends with `rejected-out` (ARCHITECTURE 9.2).
    pub rejection_cap: u64,
    /// Every random choice of the campaign derives from this seed (ARCHITECTURE 8).
    pub seed: u64,
    /// Identity inputs only the caller knows; the report records them as given (ARCHITECTURE
    /// 5.4, T-6).
    pub identity: CallerIdentity,
}

/// Identity inputs that k-rust offers no API for, supplied by the caller and recorded in the
/// report as given (ARCHITECTURE 5.4, T-6).
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CallerIdentity {
    /// The k-rust revision the caller built against (for example a commit id). No revision
    /// constant exists in k-rust.
    pub k_rust_revision: String,
    /// The stack size, in bytes, of the thread that calls [`crate::Campaign::run`], when the
    /// caller knows it. Stack stops depend on it (ARCHITECTURE 5.4).
    pub thread_stack_size: Option<u64>,
}

/// The definitions a campaign runs on (ARCHITECTURE 9.2).
///
/// A `mutant` is present exactly when the target is differential; [`crate::Campaign::new`]
/// refuses any other combination. The definitions are shared, so that a client running many
/// campaigns over one definition (one per program, target or mutant) does not copy it.
#[derive(Clone, Debug)]
pub struct Definitions {
    /// The definition every case runs on; the baseline of a differential target, whose
    /// signature hole values are generated from (ARCHITECTURE 4.3).
    pub baseline: Arc<CompiledDefinition>,
    /// The mutant of a differential target.
    pub mutant: Option<Arc<CompiledDefinition>>,
}

/// One compiled definition and the route its backend is built on (ARCHITECTURE 5.4, T-6).
///
/// It carries what krun's front half reads: the frontend definition (for the program grammar),
/// the execution definition (for patterns), the source table their provenance indexes, the main
/// and syntax modules, the configuration variable sorts, and the KORE definition the backend
/// runs, with the route used to build the backend. A compiled directory and an in-process
/// compilation of the same source give equal values ([`Self::from_artifacts`]).
#[derive(Clone, Debug)]
pub struct CompiledDefinition {
    /// The main module: the module the backend executes and patterns are compiled in.
    pub main_module: String,
    /// The module whose grammar parses the program and configuration values.
    pub syntax_module: String,
    /// The frontend definition the program grammar is resolved from
    /// (`k_rust::kompile::ProgramGrammar::new`), as a compiled directory stores it
    /// (`k_rust::kompile::retain_runtime_frontend_sentences`).
    pub frontend_definition: FrontendDefinition,
    /// The transformed execution definition that standalone surface patterns are compiled in
    /// (`CompiledKoreArtifacts::execution_definition`, `k_rust::kompile::compile_search_pattern`),
    /// as a compiled directory stores it (`k_rust::kompile::retain_pattern_sentences`).
    pub execution_definition: FrontendDefinition,
    /// The logical sources that the provenance of [`Self::frontend_definition`] and
    /// [`Self::execution_definition`] (source ids, spans, origin links) indexes: the loaded
    /// definition's (`k_rust::outer::LoadedDefinition::source_table`) or a compiled directory's.
    /// Replace it together with the definitions it indexes.
    pub source_table: SourceTable,
    /// The declared configuration variables, without `$`, and their sorts.
    pub configuration_variables: BTreeMap<String, KastSort>,
    /// The parsed KORE definition the backend executes (`definition.kore`).
    pub kore: KoreDefinition,
    /// `syntaxDefinition.kore` (`CompiledKoreArtifacts::syntax_definition_kore`): the
    /// productions' formats, from which data-sort and collection values are printed as K text
    /// (krs-unparse, D19). `definition.kore` does not carry them.
    pub syntax_definition_kore: String,
    /// `macros.kore` (`CompiledKoreArtifacts::macros_kore`), which reading K text back expands.
    pub macros_kore: String,
    /// How the backend is built from [`Self::kore`]; it selects the one path `strategy: any`
    /// follows, so it is part of the campaign's identity.
    pub route: BackendRoute,
}

impl CompiledDefinition {
    /// The definition an in-process compilation produced, on krun's route
    /// ([`BackendRoute::SourceExecution`] with the compiler's rewrite order).
    ///
    /// `frontend_definition` is the loaded source definition the compilation started from and
    /// `source_table` its sources (`outer::load_for_compilation`, then `source_table` and
    /// `into_definition`). The frontend and execution definitions are reduced as `krust
    /// kcompile` reduces them for a compiled directory, so that a campaign runs on, and
    /// identifies, the same definition whichever way it was loaded.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when `artifacts.definition_kore` does not parse, which
    /// compiler output always does.
    pub fn from_artifacts(
        main_module: impl Into<String>,
        syntax_module: impl Into<String>,
        mut frontend_definition: FrontendDefinition,
        source_table: SourceTable,
        artifacts: CompiledKoreArtifacts,
    ) -> Result<Self, CampaignError> {
        let kore = k_rust::kore::parser::parse_definition(&artifacts.definition_kore).map_err(
            |error| CampaignError::Definition {
                message: format!("definition.kore does not parse: {error}"),
            },
        )?;
        retain_runtime_frontend_sentences(&mut frontend_definition);
        let mut execution_definition = artifacts.execution_definition;
        retain_pattern_sentences(&mut execution_definition);
        Ok(Self {
            main_module: main_module.into(),
            syntax_module: syntax_module.into(),
            frontend_definition,
            execution_definition,
            source_table,
            configuration_variables: artifacts.configuration_variables,
            kore,
            syntax_definition_kore: artifacts.syntax_definition_kore,
            macros_kore: artifacts.macros_kore,
            route: BackendRoute::SourceExecution {
                execution_rewrite_order: artifacts.execution_rewrite_order,
            },
        })
    }

    /// The SHA-256, as lowercase hexadecimal, of [`Self::frontend_definition`]'s canonical
    /// provenance JSON with [`Self::source_table`] (`k_rust::definition::json::
    /// to_provenance_string`, the serialization a compiled directory stores as `frontend.json`),
    /// in which every source is named independently of where it lies: the file of the main
    /// module as `<main>`, every other path relative to that file's directory (`./expr.k`,
    /// `./../lib/x.k`), and a `krust-builtin://` URI as it is. The document holds every
    /// sentence, attribute, term and provenance record of the definition and reads back to an
    /// equal definition, and the sources' content hashes stay in it, so one definition compiled
    /// in two directories, or in process under another entry name, gives one digest, and any
    /// change of a source's bytes (a comment included) gives another. It is computed in time
    /// linear in the document.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the definition has no provenance serialization (a
    /// source id outside the table, or a receipt the format cannot hold).
    pub fn frontend_digest(&self) -> Result<String, CampaignError> {
        self.provenance_digest("frontend", &self.frontend_definition)
    }

    /// [`Self::frontend_digest`] of [`Self::execution_definition`] (a compiled directory's
    /// `execution.json`), its sources named as the frontend's are.
    ///
    /// # Errors
    ///
    /// As [`Self::frontend_digest`].
    pub fn execution_definition_digest(&self) -> Result<String, CampaignError> {
        self.provenance_digest("execution", &self.execution_definition)
    }

    /// The SHA-256, as lowercase hexadecimal, of [`Self::syntax_definition_kore`] and
    /// [`Self::macros_kore`] joined by a newline, the name in each `Source` attribute written as
    /// [`Self::frontend_digest`] writes it and the layout normalized (the printer breaks lines
    /// by width, so a longer path moves line breaks; KORE reads whitespace only between tokens).
    #[must_use]
    pub fn syntax_definition_digest(&self) -> String {
        let names = SourceNames::of(&self.frontend_definition);
        crate::report::digest_hex(
            format!(
                "{}\n{}",
                names.kore(&self.syntax_definition_kore),
                names.kore(&self.macros_kore)
            )
            .as_bytes(),
        )
    }

    fn provenance_digest(
        &self,
        role: &str,
        definition: &FrontendDefinition,
    ) -> Result<String, CampaignError> {
        let names = SourceNames::of(&self.frontend_definition);
        to_provenance_string(definition, &self.source_table)
            .map(|json| crate::report::digest_hex(names.provenance_json(&json).as_bytes()))
            .map_err(|error| CampaignError::Definition {
                message: format!("the {role} definition has no provenance serialization: {error}"),
            })
    }

    /// The execution digest of [`Self::kore`] (`k_rust::backend::execution_digest`). It does not
    /// cover the route's rewrite order.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the definition has no digest.
    pub fn execution_digest(&self) -> Result<ExecutionDigest, CampaignError> {
        k_rust::backend::execution_digest(&self.kore).map_err(|error| CampaignError::Definition {
            message: format!("the definition has no execution digest: {error}"),
        })
    }
}

/// The constructor a campaign builds its backends with (ARCHITECTURE 5.4, T-6).
///
/// krun builds its backend with `Backend::internalize_source_definition` and the compiler's
/// rewrite order; kink uses `Backend::from_definition`, which has none. The two can follow
/// different single paths under `strategy: any`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "route", rename_all = "kebab-case")]
pub enum BackendRoute {
    /// `Backend::internalize_source_definition(&kore, main, &execution_rewrite_order)`, then
    /// `Backend::from_internalized`: krun's route.
    SourceExecution {
        /// The compiler's executable rewrite precedence
        /// (`CompiledKoreArtifacts::execution_rewrite_order`).
        execution_rewrite_order: Vec<String>,
    },
    /// `Backend::from_definition(kore, main, options)`: no rewrite order.
    FromDefinition,
}

/// The program a campaign runs, unmodified (ARCHITECTURE 2.1, 2.2).
#[derive(Clone, Debug)]
pub enum ProgramInput {
    /// A program in the object language and configuration-variable bindings, assembled into a
    /// configuration exactly as krun does (ARCHITECTURE 2.3).
    Source(ProgramSource),
    /// A KORE initial configuration whose free element variables are the holes, for clients that
    /// already work in KORE (ARCHITECTURE 2.2). Each variable is addressed by a
    /// [`crate::HoleLocation::KoreVariable`] hole; every free variable must be a hole.
    KoreTemplate(KorePattern),
}

/// A program text and its configuration-variable bindings, as krun takes them.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ProgramSource {
    /// The program's name: the file name its locations carry, and the name a span hole's
    /// [`crate::SpanAddress::program`] addresses. `None` for a definition without `$PGM` that
    /// runs from its configuration variables alone.
    pub program: Option<ProgramText>,
    /// `NAME=VALUE` bindings of configuration variables (name without `$`, value as K text), in
    /// krun's `--config-var` order. Unless bound here or by a hole, `$IO` is bound `off` and
    /// `$STDIN` to `"\n"`, what `krun --io off` binds from an empty standard input (ARCHITECTURE
    /// 5.1, D17).
    pub config_vars: Vec<(String, String)>,
}

/// The text bound to `$PGM`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ProgramText {
    /// The name locations carry and span holes address (a file name, typically).
    pub name: String,
    /// The program text, exactly as the author wrote it; never modified (ARCHITECTURE 2.1).
    pub text: String,
    /// The start sort of the program parser, as krun's `--sort` (for example `Pgm`).
    pub start_sort: String,
}

/// How many paths of a nondeterministic definition a case explores (ARCHITECTURE 5.1).
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum PathMode {
    /// `strategy: any`: k-rust's first-applicable path of each input.
    #[default]
    OnePath,
    /// `strategy: all`: every path.
    AllPaths,
}

/// The execution options of every case (ARCHITECTURE 5.1, 5.2).
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct CaseOptions {
    /// One path or all paths.
    pub paths: PathMode,
    /// `ExecuteRequest::max_depth`.
    pub max_depth: Option<u64>,
    /// `ExecuteRequest::max_work`; [`DEFAULT_MAX_WORK`] when neither bound is set.
    pub max_work: Option<u64>,
    /// `ExecuteRequest::max_simplification_iterations`.
    pub max_simplification_iterations: usize,
    /// The normal-termination pattern, in krun's `--pattern` surface syntax. `None` selects
    /// `<k> .K </k>` with the rest of the configuration free, which only a definition with
    /// exactly one `<k>` cell may use (ARCHITECTURE 5.2, R-2).
    pub normal_end_pattern: Option<String>,
    /// Per-case wall-clock safety limit in milliseconds. A case it stops is `timeout` and
    /// outside the determinism contract (ARCHITECTURE 5.1, 5.4). `None`: no limit. It bounds
    /// each execution of the case: a differential case runs the baseline and the mutant, and in
    /// the one-path mode possibly the mutant again on all paths, so its wall time can reach about
    /// three times the limit.
    ///
    /// Without a limit nothing but the caller's token bounds one rewrite step: `max_work` and
    /// `max_depth` count steps, and a step whose ground function evaluation does not terminate
    /// never ends, so a definition with such a function makes [`crate::Campaign::run`] hang
    /// until the token passed to it is cancelled. [`crate::Campaign::new`] takes no token, and
    /// its internalizations and rule-graph entry run unbounded too. A library caller that runs
    /// untrusted definitions should set a limit or pass a token.
    pub safety_limit_ms: Option<u64>,
    /// The solver options every backend of the campaign is built with (krun's
    /// `--smt-timeout` and `--smt-retry-limit`). `smtUnknowns` depend on them, so they are part
    /// of the report's identity. The SMT prelude and the simplification stack budget are always
    /// the backend's defaults.
    pub backend: BackendSettings,
    /// Shrink a confirmed witness (ARCHITECTURE 7); `true` by default. With `false` the report's
    /// witness has no shrunk case and the campaign spends nothing after the first confirmed
    /// hit, which is what a benchmark of cases-to-first-hit wants. It is not an option of a
    /// case's execution, but it lives here so that the report's identity records it with the
    /// other options.
    pub shrink: bool,
    /// Findings of either definition's full critical-pair check that the data judgement reads as
    /// resolved (`k_rust_backend::data_term`, "Assumed pairs"; ARCHITECTURE 4.3): a pair as
    /// joining, an equation as agreeing with its hook or applied as written, a precondition row as
    /// met (only an overload row: a row that an equation is headed by a constructor or an
    /// injection or indexed at a collection or a bare variable is a decided fact, and its name is
    /// refused). Each is named as the
    /// report's `definition-findings` name it: a pair
    /// `FIRST,SECOND@POSITION`, each rule
    /// by its written position `FILE:LINE:COLUMN` (the file may be shortened to any trailing
    /// part of its path), `overload:GREATER:LESSER` for a compiler-generated overload axiom, its
    /// unique id or its label, and the position `root` or the argument indexes joined by `.`;
    /// an equation at an evaluated hook not shown to agree with it `hook:EQUATION`, another
    /// per-equation report `equation:EQUATION`, a precondition row `precondition:EQUATION` (or
    /// `precondition:KIND:LABELS` when it names no equation), each `EQUATION` a rule as above;
    /// `baseline:` or `mutant:` before a name applies it on that definition only. A campaign
    /// whose target reads no data end, or a name that matches no finding, more than one finding
    /// of one definition, or different findings on the two, is refused at
    /// [`crate::Campaign::new`]. Every verdict of the campaign then holds only under these
    /// premises: the report's identity records them here (sorted), and a warning states it. Empty (and
    /// absent from the JSON) by default. Not an option of a case's execution; it lives here for
    /// the same reason as [`Self::shrink`].
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub assume_joined: Vec<String>,
}

/// The solver options of every backend a campaign builds: a serializable copy of
/// `k_rust::backend::BackendOptions`, recorded in the report.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct BackendSettings {
    /// `BackendOptions::smt_timeout_ms`.
    pub smt_timeout_ms: u32,
    /// `BackendOptions::smt_retry_limit`.
    pub smt_retry_limit: u32,
}

impl Default for BackendSettings {
    fn default() -> Self {
        let defaults = BackendOptions::default();
        Self {
            smt_timeout_ms: defaults.smt_timeout_ms,
            smt_retry_limit: defaults.smt_retry_limit,
        }
    }
}

impl BackendSettings {
    /// The backend options these settings stand for.
    #[must_use]
    pub fn options(self) -> BackendOptions {
        BackendOptions {
            smt_timeout_ms: self.smt_timeout_ms,
            smt_retry_limit: self.smt_retry_limit,
            smt_resource_limit: None,
        }
    }
}

impl Default for CaseOptions {
    fn default() -> Self {
        Self {
            paths: PathMode::OnePath,
            max_depth: None,
            max_work: None,
            max_simplification_iterations:
                k_rust::k_rust_backend::simplify::DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            normal_end_pattern: None,
            safety_limit_ms: None,
            backend: BackendSettings::default(),
            shrink: true,
            assume_joined: Vec::new(),
        }
    }
}

impl CaseOptions {
    /// The `max_work` every case runs with: the given one, or [`DEFAULT_MAX_WORK`] when neither
    /// `max_depth` nor `max_work` is set.
    #[must_use]
    pub fn effective_max_work(&self) -> Option<u64> {
        match (self.max_depth, self.max_work) {
            (None, None) => Some(DEFAULT_MAX_WORK),
            (_, work) => work,
        }
    }
}

/// A proposer: a technique that chooses the next assignment (ARCHITECTURE 8).
#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProposerKind {
    /// Proptest generation from each hole's generator (8.2; M1).
    Blind,
    /// Guard harvesting (8.3; M4).
    Dictionary,
    /// Targeted hill climbing (8.4; M4).
    Climb,
    /// Coverage-guided corpus (8.5; M5).
    Corpus,
    /// Solver queries; needs the `z3` feature (8.6; M6).
    Solve,
}

/// An assignment of values to holes, by hole name.
pub type Assignment = BTreeMap<String, Value>;

/// Which proposers run (ARCHITECTURE 8).
///
/// The explicit proposer runs first: the holes' anchor values, then the author's assignments.
/// The others are mixed by a deterministic schedule with these weights, every choice derived
/// from the campaign seed. [`crate::Campaign::new`] refuses a proposer this build or milestone
/// does not provide.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct ProposerConfig {
    /// Try the assignment of every hole's anchor value first (8.1).
    pub anchors_first: bool,
    /// Assignments the author supplies, tried after the anchors, in order (8.1). Each must
    /// satisfy the holes' constraints; holes it omits keep their anchor values.
    pub explicit: Vec<Assignment>,
    /// The scheduled proposers and their weights; a weight of 0 disables one.
    pub weights: BTreeMap<ProposerKind, u32>,
}

impl Default for ProposerConfig {
    fn default() -> Self {
        Self {
            anchors_first: true,
            explicit: Vec::new(),
            weights: BTreeMap::from([(ProposerKind::Blind, 1)]),
        }
    }
}

/// How much a campaign may spend (ARCHITECTURE 9.2).
///
/// There is deliberately no wall-clock budget: it would make the number of cases depend on the
/// host (R-27). In JSON the limit is a decimal string, which JavaScript clients read exactly
/// whatever its size.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Budget {
    /// At most this many cases, rejected cases included. Confirmation and shrink runs are not
    /// cases; the engine caps shrinking separately.
    Cases(#[serde(with = "crate::report::decimal_u64")] u64),
    /// At most this much backend work: the sum of `work` over every execution the campaign runs,
    /// including confirmation, shrinking, both sides of a differential case and the solve
    /// proposer's runs (R-7). Every case is charged at least 1, rejected and failed (`Err`)
    /// cases included, so a campaign whose cases do no work still ends. An execution starts
    /// only while the work spent is below the budget, except the confirmation of a candidate
    /// hit, which always runs; the total may therefore exceed the budget by the last case's
    /// work and one confirmation's, which for a differential case are two executions each.
    Work(#[serde(with = "crate::report::decimal_u64")] u64),
}

#[cfg(test)]
mod tests {
    use serde::de::DeserializeOwned;
    use serde_json::{Value as Json, json};

    use super::*;

    use crate::{
        holes::{HoleDecl, HoleLocation, SpanAddress},
        target::{
            DifferentialTarget, ObserverTarget, PatternTarget, RuleRef, RuleTarget, Target,
            TargetKind,
        },
        values::{Constraints, ElementSorts, GenerationBounds, IntRange, LengthRange, Value},
    };

    /// Fails to compile when a variant is added to [`Budget`]: a wall-clock budget must not
    /// exist (ARCHITECTURE 9.2, R-27), and any other new variant must be reviewed against the
    /// determinism contract.
    fn budget_limit(budget: Budget) -> (&'static str, u64) {
        match budget {
            Budget::Cases(cases) => ("cases", cases),
            Budget::Work(work) => ("work", work),
        }
    }

    #[test]
    fn budget_has_exactly_cases_and_work() {
        assert_eq!(budget_limit(Budget::Cases(3)), ("cases", 3));
        assert_eq!(budget_limit(Budget::Work(7)), ("work", 7));
        assert_eq!(
            serde_json::to_string(&Budget::Work(7)).expect("a budget serializes"),
            r#"{"work":"7"}"#
        );
    }

    /// `good` reads as a `T`, and `good` with the extra field `field` does not, with an error
    /// that names the field.
    fn refuses<T: DeserializeOwned + std::fmt::Debug>(good: &Json, field: &str) {
        serde_json::from_value::<T>(good.clone())
            .unwrap_or_else(|error| panic!("{good} does not read: {error}"));
        let mut bad = good.clone();
        bad[field] = json!(1);
        let error = serde_json::from_value::<T>(bad.clone())
            .expect_err(&format!("{bad} reads with the unknown field `{field}`"));
        assert!(error.to_string().contains(field), "{bad}: {error}");
    }
    /// `good` with the extra field `field` in the object at `path` does not read as a `T`.
    fn refuses_at<T: DeserializeOwned + std::fmt::Debug>(good: &Json, path: &[&str], field: &str) {
        let mut bad = good.clone();
        let mut inner = &mut bad;
        for key in path {
            inner = &mut inner[*key];
        }
        inner[field] = json!(1);
        let error = serde_json::from_value::<T>(bad.clone())
            .expect_err(&format!("{bad} reads with the unknown field `{field}`"));
        assert!(error.to_string().contains(field), "{bad}: {error}");
    }

    /// Every specification type of a hole refuses a field it does not know, so that a misspelt
    /// constraint is an error rather than a silent default: a hole whose `range` is misspelt
    /// would otherwise be searched unconstrained (BIND review S1). Each well-formed document
    /// still reads.
    #[test]
    fn hole_types_refuse_unknown_fields() {
        let span =
            json!({ "kind": "span", "program": "p", "line": 2, "find": "x = 1;", "literal": "1" });
        refuses::<HoleLocation>(&span, "lien");
        refuses::<SpanAddress>(
            &json!({ "program": "p", "find": "1", "literal": "1" }),
            "lien",
        );
        refuses::<HoleLocation>(&json!({ "kind": "config-var", "name": "X" }), "line");
        refuses::<HoleLocation>(&json!({ "kind": "kore-variable", "name": "X" }), "line");
        let constraints = json!({
            "range": { "min": "0", "max": "0" },
            "length": { "min": 1, "max": 2 },
            "elements": { "collection": "entries", "key": "Int", "value": "Int" },
            "choices": [{ "int": "0" }],
        });
        let hole =
            json!({ "name": "X", "sort": "Int", "location": span, "constraints": constraints });
        refuses::<HoleDecl>(&hole, "constraint");
        refuses::<Constraints>(&constraints, "rnage");
        refuses_at::<HoleDecl>(&hole, &["constraints"], "rnage");
        refuses_at::<HoleDecl>(&hole, &["location"], "lien");
        refuses::<IntRange>(&json!({ "min": "0" }), "mn");
        refuses::<LengthRange>(&json!({ "max": 3 }), "mx");
        refuses::<ElementSorts>(
            &json!({ "collection": "elements", "element": "Int" }),
            "key",
        );
        refuses_at::<Value>(
            &json!({ "m-int": { "width": 8, "value": "1" } }),
            &["m-int"],
            "sign",
        );
        refuses_at::<Value>(
            &json!({ "token": { "sort": "Id", "text": "x" } }),
            &["token"],
            "sorts",
        );
        refuses_at::<Value>(
            &json!({ "apply": { "symbol": "Lblf", "arguments": [] } }),
            &["apply"],
            "args",
        );
    }

    /// The target, the program, the identity, the options, the proposers and the bounds refuse
    /// a field they do not know, as the hole types do.
    #[test]
    fn target_and_option_types_refuse_unknown_fields() {
        let rule =
            json!({ "kind": "rule", "rule": { "by": "label", "value": "IMP.x" }, "mode": "fired" });
        let target = json!({ "kind": rule, "run-to-completion": false, "negated-property": false });
        refuses::<Target>(&target, "negated");
        refuses::<TargetKind>(&rule, "lable");
        refuses::<RuleTarget>(
            &json!({ "rule": { "by": "unique-id", "value": "u" }, "mode": "covered" }),
            "lable",
        );
        refuses::<RuleRef>(&json!({ "by": "label", "value": "IMP.x" }), "extra");
        refuses_at::<RuleRef>(
            &json!({ "by": "source", "value": { "source": "imp.k", "line": 3 } }),
            &["value"],
            "column",
        );
        refuses::<TargetKind>(
            &json!({ "kind": "pattern", "pattern": "<k> _ </k>", "at": "final" }),
            "where",
        );
        refuses::<PatternTarget>(&json!({ "pattern": "<k> _ </k>", "at": "final" }), "where");
        refuses::<TargetKind>(&json!({ "kind": "differential" }), "mutant");
        refuses::<DifferentialTarget>(&json!({}), "mutant");
        refuses::<TargetKind>(&json!({ "kind": "observer", "name": "o" }), "verison");
        refuses::<ObserverTarget>(&json!({ "name": "o" }), "verison");

        refuses::<CallerIdentity>(&json!({ "k-rust-revision": "r" }), "thread-stack");
        let text = json!({ "name": "p", "text": "1", "start-sort": "Pgm" });
        refuses::<ProgramText>(&text, "sort");
        refuses::<ProgramSource>(&json!({ "program": text, "config-vars": [] }), "programme");
        let options = serde_json::to_value(CaseOptions::default()).expect("options serialize");
        refuses::<CaseOptions>(&options, "max-dept");
        refuses_at::<CaseOptions>(&options, &["backend"], "smt-timeout");
        refuses::<BackendSettings>(&options["backend"], "smt-timeout");
        let proposers =
            serde_json::to_value(ProposerConfig::default()).expect("proposers serialize");
        refuses::<ProposerConfig>(&proposers, "weight");
        let bounds = serde_json::to_value(GenerationBounds::default()).expect("bounds serialize");
        refuses::<GenerationBounds>(&bounds, "dept");
    }

    #[test]
    fn unbounded_options_get_the_default_work_bound() {
        assert_eq!(
            CaseOptions::default().effective_max_work(),
            Some(DEFAULT_MAX_WORK)
        );
        let depth_only = CaseOptions {
            max_depth: Some(10),
            ..CaseOptions::default()
        };
        assert_eq!(depth_only.effective_max_work(), None);
    }
}

/// The definition digests of the report identity (FZ-SETUP).
#[cfg(test)]
mod digest_tests {
    use super::CompiledDefinition;
    use crate::support::{self, COIN, Fixture, IMP, MAC, MAC_KILL};

    /// `fixture`'s source with `from` (which occurs exactly once) replaced by `to`, compiled
    /// under the fixture's source name.
    fn edited(fixture: &'static Fixture, from: &str, to: &str) -> CompiledDefinition {
        assert_eq!(fixture.source.matches(from).count(), 1, "{from}");
        support::compile_source(
            fixture.file,
            &fixture.source.replace(from, to),
            fixture.main_module,
        )
    }

    fn digests(definition: &CompiledDefinition) -> (String, String) {
        (
            definition.frontend_digest().expect("a frontend digest"),
            definition
                .execution_definition_digest()
                .expect("an execution-definition digest"),
        )
    }

    /// FZ-SETUP (a): one production changed in the frontend changes the frontend digest. Making
    /// `-` right-associative changes how `a - b - c` parses.
    #[test]
    fn a_one_production_change_changes_the_frontend_digest() {
        let base = IMP.compiled().definition();
        let right = edited(
            &IMP,
            r#"| AExp "-" AExp              [symbol(_-_), left,"#,
            r#"| AExp "-" AExp              [symbol(_-_), right,"#,
        );
        assert_ne!(digests(&base).0, digests(&right).0);
    }

    /// FZ-SETUP (b): a macro change changes both definition digests, where the KORE that runs
    /// is equal (`MAC_KILL` edits only the macro rule, which `definition.kore` does not hold).
    #[test]
    fn a_macro_change_changes_both_definition_digests() {
        let base = MAC.compiled().definition();
        let kill = MAC_KILL.compiled().definition();
        assert_eq!(
            base.execution_digest().unwrap(),
            kill.execution_digest().unwrap(),
            "the executed KORE is equal"
        );
        let (base_frontend, base_execution) = digests(&base);
        let (kill_frontend, kill_execution) = digests(&kill);
        assert_ne!(base_frontend, kill_frontend);
        assert_ne!(base_execution, kill_execution);
    }

    /// FZ-SETUP (c): a change of the execution definition that patterns are compiled in changes
    /// its digest: a production added to the semantics module.
    #[test]
    fn a_change_of_the_execution_definition_changes_its_digest() {
        let base = COIN.compiled().definition();
        let marked = edited(
            &COIN,
            "  configuration <k> $PGM:Pgm </k>",
            "  syntax KItem ::= mark(Int) [symbol(mark)]\n  configuration <k> $PGM:Pgm </k>",
        );
        assert_ne!(digests(&base).1, digests(&marked).1);
    }

    /// The coin definition split in two files: the semantics in `sem/coin.k`, which requires the
    /// syntax from a sibling directory, `../lib/coin-syntax.k`.
    const SPLIT_MAIN: &str = r#"requires "../lib/coin-syntax.k"

module COIN
  imports COIN-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [heads]: <k> flip(N) => .K ... </k> <out> _ => N </out>
  rule [tails]: <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out>
endmodule
"#;
    const SPLIT_SYNTAX: &str = r"module COIN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= flip(Int)   [symbol(flip)]
endmodule
";

    /// The split coin definition with its entry at `root/sem/coin.k` (or at `entry`).
    fn split(root: &str, entry: Option<&str>, syntax: &str) -> CompiledDefinition {
        let main = entry.map_or_else(|| format!("{root}/sem/coin.k"), str::to_owned);
        let library = match entry {
            Some(_) => "../lib/coin-syntax.k".to_owned(),
            None => format!("{root}/lib/coin-syntax.k"),
        };
        support::compile_files(&main, SPLIT_MAIN, &[(&library, syntax)], "COIN")
    }

    fn all_digests(definition: &CompiledDefinition) -> (String, String, String, String) {
        let (frontend, execution) = digests(definition);
        (
            frontend,
            execution,
            definition.syntax_definition_digest(),
            definition.execution_digest().unwrap().to_string(),
        )
    }

    /// FZ-SETUP fix round (S1): one definition compiled from two directories, or in process
    /// under the bindings' default entry name, gives one identity; the digested documents name
    /// no directory; a change of a source's text still changes it.
    #[test]
    fn the_identity_does_not_depend_on_where_the_sources_lie() {
        let at_a = split("/srv/a", None, SPLIT_SYNTAX);
        let at_b = split("/home/someone/b/deeper", None, SPLIT_SYNTAX);
        let bound = split("", Some("definition.k"), SPLIT_SYNTAX);
        assert_ne!(
            at_a.frontend_definition, at_b.frontend_definition,
            "the definitions record different source paths"
        );
        assert_eq!(all_digests(&at_a), all_digests(&at_b));
        assert_eq!(all_digests(&at_a), all_digests(&bound));
        let names = crate::source_names::SourceNames::of(&at_a.frontend_definition);
        let json = k_rust::definition::json::to_provenance_string(
            &at_a.frontend_definition,
            &at_a.source_table,
        )
        .unwrap();
        assert!(json.contains("/srv/a/lib/coin-syntax.k"));
        let renamed = names.provenance_json(&json);
        assert!(!renamed.contains("/srv/a"), "no directory is digested");
        assert!(renamed.contains(r#""logical":"./../lib/coin-syntax.k""#));
        assert!(renamed.contains(r#""logical":"<main>""#));
        assert!(!names.kore(&at_a.syntax_definition_kore).contains("/srv/a"));

        // A comment appended to the required file changes no sentence, but the file's bytes.
        let commented = split("/srv/a", None, &format!("{SPLIT_SYNTAX}// a comment\n"));
        let (frontend, execution, syntax, kore) = all_digests(&commented);
        assert_ne!(frontend, all_digests(&at_a).0);
        assert_ne!(execution, all_digests(&at_a).1);
        assert_eq!((syntax, kore), (all_digests(&at_a).2, all_digests(&at_a).3));
        // A production added to the required file changes the definition.
        let grown = split(
            "/srv/b",
            None,
            &SPLIT_SYNTAX.replace(
                "[symbol(flip)]",
                "[symbol(flip)]\n               | count(Int)  [symbol(count)]",
            ),
        );
        let grown = all_digests(&grown);
        let base = all_digests(&at_a);
        assert_ne!(grown.0, base.0);
        assert_ne!(grown.1, base.1);
        assert_ne!(grown.2, base.2);
    }

    /// FZ-SETUP (d): equal definitions compiled twice give equal digests, and the in-process
    /// definition is reduced to what a compiled directory stores (the CLI half is
    /// `tests/cli.rs`, `the_command_line_runs_the_library_campaign`).
    #[test]
    fn equal_definitions_give_equal_digests() {
        let once = IMP.compiled().definition();
        let again = support::compile_source(IMP.file, IMP.source, IMP.main_module);
        assert_eq!(digests(&once), digests(&again));
        assert_eq!(
            once.frontend_definition, again.frontend_definition,
            "the digests are of equal definitions"
        );
        let mut reduced = IMP.compiled().artifacts.execution_definition.clone();
        k_rust::kompile::retain_pattern_sentences(&mut reduced);
        assert_eq!(once.execution_definition, reduced);
        assert!(
            once.execution_definition.modules.iter().all(|module| {
                module.local_sentences.iter().all(|sentence| {
                    !matches!(&**sentence, k_rust::definition::Sentence::Rule { attributes, .. }
                        if !attributes.has_any(&k_rust::definition::AttributeKey::MACRO_LIKE))
                })
            }),
            "only macro-like rules are kept in the execution definition"
        );
    }
}
