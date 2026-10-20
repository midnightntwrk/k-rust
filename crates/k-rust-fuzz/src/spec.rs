//! The campaign specification: everything a campaign's report is a function of, apart from the
//! budget (ARCHITECTURE 5.4, 9.2).

use std::{collections::BTreeMap, sync::Arc};

use k_rust::{
    backend::{BackendOptions, ExecutionDigest},
    definition::Definition as FrontendDefinition,
    kast::Sort as KastSort,
    kompile::CompiledKoreArtifacts,
    kore::ast::Definition as KoreDefinition,
    kore::ast::Pattern as KorePattern,
};
use serde::{Deserialize, Serialize};

use crate::{
    error::CampaignError,
    holes::HoleDecl,
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
#[serde(rename_all = "kebab-case")]
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
/// the execution definition (for patterns), the main and syntax modules, the configuration
/// variable sorts, and the KORE definition the backend runs, with the route used to build the
/// backend.
#[derive(Clone, Debug)]
pub struct CompiledDefinition {
    /// The main module: the module the backend executes and patterns are compiled in.
    pub main_module: String,
    /// The module whose grammar parses the program and configuration values.
    pub syntax_module: String,
    /// The frontend definition the program grammar is resolved from
    /// (`k_rust::kompile::ProgramGrammar::new`).
    pub frontend_definition: FrontendDefinition,
    /// The transformed execution definition that standalone surface patterns are compiled in
    /// (`CompiledKoreArtifacts::execution_definition`, `k_rust::kompile::compile_search_pattern`).
    pub execution_definition: FrontendDefinition,
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
    /// `frontend_definition` is the loaded source definition the compilation started from
    /// (`outer::load_for_compilation`, then `into_definition`), as krun keeps it.
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when `artifacts.definition_kore` does not parse, which
    /// compiler output always does.
    pub fn from_artifacts(
        main_module: impl Into<String>,
        syntax_module: impl Into<String>,
        frontend_definition: FrontendDefinition,
        artifacts: CompiledKoreArtifacts,
    ) -> Result<Self, CampaignError> {
        let kore = k_rust::kore::parser::parse_definition(&artifacts.definition_kore).map_err(
            |error| CampaignError::Definition {
                message: format!("definition.kore does not parse: {error}"),
            },
        )?;
        Ok(Self {
            main_module: main_module.into(),
            syntax_module: syntax_module.into(),
            frontend_definition,
            execution_definition: artifacts.execution_definition,
            configuration_variables: artifacts.configuration_variables,
            kore,
            syntax_definition_kore: artifacts.syntax_definition_kore,
            macros_kore: artifacts.macros_kore,
            route: BackendRoute::SourceExecution {
                execution_rewrite_order: artifacts.execution_rewrite_order,
            },
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
#[serde(rename_all = "kebab-case")]
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
#[serde(rename_all = "kebab-case")]
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
#[serde(rename_all = "kebab-case")]
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
    /// outside the determinism contract (ARCHITECTURE 5.1, 5.4). `None`: no limit.
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
}

/// The solver options of every backend a campaign builds: a serializable copy of
/// `k_rust::backend::BackendOptions`, recorded in the report.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
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
#[serde(rename_all = "kebab-case")]
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
    use super::*;

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
