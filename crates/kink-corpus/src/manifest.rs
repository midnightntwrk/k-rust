//! Canonical, data-only corpus declarations, with required finite bounds.

use crate::{ProgramSource, SourceFile, TestInputSpec};
use k_rust::kore::{
    ast::Sort,
    codec::{from_value, to_value},
    parser::parse_pattern,
};
use kink_campaign::{
    BudgetMutants, Coupled, CrashPolicy, OracleDeclaration, Projection, ScheduleMode, Sel,
    SelectionPolicy, StateProjection,
};
use kink_native::{
    K_RUST_REVISION,
    execution::{ExecutionBudget, SolverProfile},
    step_events::{StepEventSpec, StepObservation},
};
use kink_patch::{OperatorSpec, Sha256Digest, Universe, canonical_json, payload_digest};
use kink_pattern::{
    Atom, EventVocabulary, MatchMode, PatternArm, PatternPlan, PayloadClause, Relation,
};
use serde_json::{Map, Value};
use std::{
    collections::BTreeSet,
    fmt,
    path::{Component, Path},
};

pub const CORPUS_MANIFEST_DOMAIN: &str = "kink/corpus-manifest/v1";
/// Full conformance case names from
/// ../k-rust-927b9ce6-intake/findings/verify.md section 4 and
/// ../k-rust-927b9ce6/scripts/conformance/expectations.toml.
pub const BELOW_FLOOR: [&str; 15] = [
    "checks",
    "issue-1273",
    "fun-llvm",
    "issue-1263",
    "issue-946",
    "let-test",
    "pattern-macro",
    "pattern-macro-productions",
    "pl-tutorial/2_languages/1_simple/2_typed/1_static",
    "pl-tutorial/2_languages/2_kool/1_untyped",
    "pl-tutorial/2_languages/2_kool/2_typed/1_dynamic",
    "issue-1879-kproveTrans/haskell",
    "pl-tutorial/2_languages/1_simple/1_untyped",
    "pl-tutorial/2_languages/2_kool/2_typed/2_static",
    "pl-tutorial/2_languages/3_fun/1_untyped/1_environment",
];
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManifestError {
    Json(String),
    Schema(String),
    NonCanonical,
    RevisionMismatch,
    ProfileMismatch,
    MissingMaxDepth,
    InvalidMaxDepth,
    MissingCandidateMaximum,
    UnknownClassifier,
    PatternOracle,
    Observation(String),
    MissingBelowFloorExclusion,
}
impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ManifestError {}

#[derive(Clone, Debug)]
pub struct CorpusCampaign {
    pub schedule: ScheduleMode,
    pub selection: SelectionPolicy,
    pub budget: ExecutionBudget,
    pub budget_mutants: Option<BudgetMutants>,
    pub max_candidates_per_spec: u64,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionRoot {
    pub path: String,
    pub revision: Option<String>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Exclusion {
    pub case: String,
    pub reason: String,
    pub citation: String,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorpusInput {
    Program(TestInputSpec),
    KoreState { file: String, sha256: Sha256Digest },
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorpusTest {
    pub id: String,
    pub input: CorpusInput,
    pub oracles: Vec<OracleDeclaration>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionSpec {
    pub id: String,
    pub root: DefinitionRoot,
    pub entry: String,
    pub include_dirs: Vec<String>,
    pub main_module: String,
    pub syntax_module: Option<String>,
    pub md_selector: Option<String>,
    pub files: Vec<SourceFile>,
    pub requires_profile: Option<SolverProfile>,
    pub max_depth: Option<u64>,
    pub observation: Vec<StepEventSpec>,
    pub tests: Vec<CorpusTest>,
}
#[derive(Clone, Debug)]
pub struct CorpusManifest {
    value: Value,
    pub(crate) campaign: CorpusCampaign,
    pub(crate) universe: Universe,
    pub(crate) operators: Vec<OperatorSpec>,
    pub(crate) exclusions: Vec<Exclusion>,
    pub(crate) definitions: Vec<DefinitionSpec>,
    profiles: Vec<SolverProfile>,
}
impl CorpusManifest {
    pub fn from_canonical_json(text: &str) -> Result<Self, ManifestError> {
        let value: Value =
            serde_json::from_str(text).map_err(|e| ManifestError::Json(e.to_string()))?;
        if canonical_json(&value) != text {
            return Err(ManifestError::NonCanonical);
        }
        let top = object(
            &value,
            &[
                "schema",
                "version",
                "corpus",
                "k_rust",
                "profiles",
                "campaign",
                "universe",
                "operators",
                "exclusions",
                "definitions",
            ],
        )?;
        if string(&top["schema"])? != "kink-corpus-manifest" || number(&top["version"])? != 1 {
            return Err(schema("manifest version"));
        }
        let corpus = object(&top["corpus"], &["name", "version"])?;
        nonempty(&corpus["name"])?;
        u32::try_from(number(&corpus["version"])?).map_err(|_| schema("corpus version"))?;
        let pin = object(&top["k_rust"], &["revision"])?;
        if string(&pin["revision"])? != K_RUST_REVISION {
            return Err(ManifestError::RevisionMismatch);
        }
        let profiles = array(&top["profiles"])?
            .iter()
            .map(profile)
            .collect::<Result<Vec<_>, _>>()?;
        if profiles.is_empty() || profiles.iter().collect::<BTreeSet<_>>().len() != profiles.len() {
            return Err(schema("profiles"));
        }
        let campaign = campaign(&top["campaign"])?;
        let universe = universe(&top["universe"])?;
        let operators = array(&top["operators"])?
            .iter()
            .map(|v| {
                OperatorSpec::from_canonical_json(&canonical_json(v))
                    .map_err(|e| schema(e.to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if operators.is_empty() {
            return Err(schema("empty operators"));
        }
        let exclusions = array(&top["exclusions"])?
            .iter()
            .map(exclusion)
            .collect::<Result<Vec<_>, _>>()?;
        if BELOW_FLOOR.iter().any(|case| {
            !exclusions.iter().any(|e| {
                e.case == *case
                    && e.reason == "below-floor"
                    && e.citation == "../k-rust-927b9ce6-intake/findings/verify.md section 4"
            })
        }) {
            return Err(ManifestError::MissingBelowFloorExclusion);
        }
        let definitions = array(&top["definitions"])?
            .iter()
            .map(|v| definition(v, campaign.budget.max_depth.expect("required depth")))
            .collect::<Result<Vec<_>, _>>()?;
        if definitions.is_empty()
            || definitions
                .iter()
                .map(|d| &d.id)
                .collect::<BTreeSet<_>>()
                .len()
                != definitions.len()
        {
            return Err(schema("definition ids"));
        }
        let manifest = Self {
            value,
            campaign,
            universe,
            operators,
            exclusions,
            definitions,
            profiles,
        };
        manifest.check_profile(SolverProfile::BUILD)?;
        Ok(manifest)
    }
    pub fn check_profile(&self, profile: SolverProfile) -> Result<(), ManifestError> {
        if self.profiles.contains(&profile) {
            Ok(())
        } else {
            Err(ManifestError::ProfileMismatch)
        }
    }
    pub fn value(&self) -> Value {
        self.value.clone()
    }
    pub fn text(&self) -> String {
        canonical_json(&self.value)
    }
    pub fn digest(&self) -> Sha256Digest {
        payload_digest(CORPUS_MANIFEST_DOMAIN, self.text().as_bytes())
    }
    pub fn definitions(&self) -> &[DefinitionSpec] {
        &self.definitions
    }
    pub fn campaign(&self) -> &CorpusCampaign {
        &self.campaign
    }
    pub fn universe(&self) -> &Universe {
        &self.universe
    }
    pub fn operators(&self) -> &[OperatorSpec] {
        &self.operators
    }
    pub fn exclusions(&self) -> &[Exclusion] {
        &self.exclusions
    }
}
fn schema(detail: impl Into<String>) -> ManifestError {
    ManifestError::Schema(detail.into())
}
fn object<'a>(v: &'a Value, keys: &[&str]) -> Result<&'a Map<String, Value>, ManifestError> {
    let map = v.as_object().ok_or_else(|| schema("object"))?;
    if map.len() != keys.len() || keys.iter().any(|k| !map.contains_key(*k)) {
        return Err(schema("exact keys"));
    }
    Ok(map)
}
fn array(v: &Value) -> Result<&Vec<Value>, ManifestError> {
    v.as_array().ok_or_else(|| schema("array"))
}
fn string(v: &Value) -> Result<String, ManifestError> {
    v.as_str()
        .map(str::to_owned)
        .ok_or_else(|| schema("string"))
}
fn nonempty(v: &Value) -> Result<String, ManifestError> {
    let s = string(v)?;
    if s.is_empty() {
        Err(schema("nonempty string"))
    } else {
        Ok(s)
    }
}
fn optional(v: &Value) -> Result<Option<String>, ManifestError> {
    if v.is_null() {
        Ok(None)
    } else {
        string(v).map(Some)
    }
}
fn number(v: &Value) -> Result<u64, ManifestError> {
    v.as_u64().ok_or_else(|| schema("unsigned integer"))
}
fn boolean(v: &Value) -> Result<bool, ManifestError> {
    v.as_bool().ok_or_else(|| schema("boolean"))
}
fn strings(v: &Value) -> Result<Vec<String>, ManifestError> {
    array(v)?.iter().map(string).collect()
}
fn profile(v: &Value) -> Result<SolverProfile, ManifestError> {
    match v.as_str() {
        Some("no-z3") => Ok(SolverProfile::NoZ3),
        Some("z3") => Ok(SolverProfile::Z3),
        _ => Err(schema("profile")),
    }
}
fn depth(v: Option<&Value>) -> Result<u64, ManifestError> {
    v.and_then(Value::as_u64)
        .ok_or(ManifestError::MissingMaxDepth)
}
fn campaign(v: &Value) -> Result<CorpusCampaign, ManifestError> {
    let map = v.as_object().ok_or_else(|| schema("campaign"))?;
    let maximum = map
        .get("max_candidates_per_spec")
        .and_then(Value::as_u64)
        .filter(|n| *n > 0)
        .ok_or(ManifestError::MissingCandidateMaximum)?;
    let budget = map
        .get("budget")
        .and_then(Value::as_object)
        .ok_or(ManifestError::MissingMaxDepth)?;
    let max_depth = depth(budget.get("max_depth"))?;
    let map = object(
        v,
        &[
            "schedule",
            "selection",
            "classifier",
            "max_candidates_per_spec",
            "budget",
            "budget_mutants",
        ],
    )?;
    let budget = object(
        &map["budget"],
        &[
            "time_ms",
            "max_simplification_iterations",
            "max_depth",
            "max_breadth",
        ],
    )?;
    if map["classifier"].as_str() != Some("all-normal") {
        return Err(ManifestError::UnknownClassifier);
    }
    let schedule = match map["schedule"].as_str() {
        Some("full") => ScheduleMode::Full,
        Some("first-kill") => ScheduleMode::FirstKill,
        _ => return Err(schema("schedule")),
    };
    let selection = if map["selection"] == Value::String("none".into()) {
        SelectionPolicy::None
    } else {
        let tagged = object(&map["selection"], &["prioritize"])?;
        let s = object(&tagged["prioritize"], &["key", "coupled", "coverage"])?;
        if s["key"] != "compiled-rule-ids" || s["coverage"] != "kink/coverage/v1" {
            return Err(schema("selection"));
        }
        let coupled = match s["coupled"].as_str() {
            Some("union") => Coupled::Union,
            Some("all-sites") => Coupled::AllSites,
            _ => return Err(schema("coupled")),
        };
        SelectionPolicy::Prioritize(Sel { coupled })
    };
    Ok(CorpusCampaign {
        schedule,
        selection,
        max_candidates_per_spec: maximum,
        budget_mutants: budget_mutants(&map["budget_mutants"])?,
        budget: ExecutionBudget {
            time: std::time::Duration::from_millis(number(&budget["time_ms"])?),
            max_simplification_iterations: usize::try_from(number(
                &budget["max_simplification_iterations"],
            )?)
            .map_err(|_| schema("simplification maximum"))?,
            max_depth: Some(max_depth),
            max_breadth: if budget["max_breadth"].is_null() {
                None
            } else {
                Some(
                    std::num::NonZeroUsize::new(
                        usize::try_from(number(&budget["max_breadth"])?)
                            .map_err(|_| schema("breadth"))?,
                    )
                    .ok_or_else(|| schema("positive breadth"))?,
                )
            },
        },
    })
}
fn budget_mutants(v: &Value) -> Result<Option<BudgetMutants>, ManifestError> {
    if v.is_null() {
        return Ok(None);
    }
    let map = object(v, &["per_spec_max", "total_max", "seed"])?;
    let per_spec_max = number(&map["per_spec_max"])?;
    let total_max = number(&map["total_max"])?;
    if per_spec_max == 0 || total_max == 0 {
        return Err(schema("positive mutant budget maxima"));
    }
    let seed = nonempty(&map["seed"])?;
    if !seed.len().is_multiple_of(2)
        || !seed
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(schema("lowercase hexadecimal mutant budget seed"));
    }
    let seed = (0..seed.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&seed[i..i + 2], 16).expect("validated hexadecimal"))
        .collect();
    Ok(Some(BudgetMutants {
        per_spec_max,
        total_max,
        seed,
    }))
}
fn universe(v: &Value) -> Result<Universe, ManifestError> {
    let m = object(
        v,
        &[
            "kinds",
            "authored",
            "typed",
            "exclude_attributes",
            "exclude_macro_rules",
        ],
    )?;
    if m["kinds"] != serde_json::json!(["rule"]) || !boolean(&m["authored"])? {
        return Err(schema("authored rule universe"));
    }
    let attributes = strings(&m["exclude_attributes"])?;
    if attributes.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(schema("attribute order"));
    }
    Ok(Universe {
        authored: true,
        typed: boolean(&m["typed"])?,
        exclude_attributes: attributes,
        exclude_macro_rules: boolean(&m["exclude_macro_rules"])?,
    })
}
fn exclusion(v: &Value) -> Result<Exclusion, ManifestError> {
    let m = object(v, &["case", "reason", "citation"])?;
    let reason = string(&m["reason"])?;
    if !["below-floor", "r0", "float", "collections", "other"].contains(&reason.as_str()) {
        return Err(schema("exclusion reason"));
    }
    Ok(Exclusion {
        case: nonempty(&m["case"])?,
        reason,
        citation: nonempty(&m["citation"])?,
    })
}
/// Lexically normalized relative path; parent components may name sibling checkouts.
pub(crate) fn normalized(name: &str) -> Result<Vec<String>, ManifestError> {
    let mut parts = Vec::new();
    for c in Path::new(name).components() {
        match c {
            Component::Normal(p) => {
                parts.push(p.to_str().ok_or_else(|| schema("UTF-8 path"))?.to_owned())
            }
            Component::CurDir => {}
            Component::ParentDir if parts.last().is_some_and(|p| p != "..") => {
                parts.pop();
            }
            Component::ParentDir => parts.push("..".into()),
            _ => return Err(schema("relative path")),
        }
    }
    Ok(parts)
}
fn path(v: &Value) -> Result<String, ManifestError> {
    let s = string(v)?;
    normalized(&s)?;
    Ok(s)
}
fn hash(v: &Value) -> Result<Sha256Digest, ManifestError> {
    Sha256Digest::parse(&string(v)?).ok_or_else(|| schema("SHA-256"))
}
fn definition(v: &Value, campaign_depth: u64) -> Result<DefinitionSpec, ManifestError> {
    let m = object(
        v,
        &[
            "id",
            "root",
            "entry",
            "include_dirs",
            "main_module",
            "syntax_module",
            "md_selector",
            "files",
            "requires_profile",
            "max_depth",
            "observation",
            "tests",
        ],
    )?;
    let root = object(&m["root"], &["path", "revision"])?;
    let max_depth = if m["max_depth"].is_null() {
        None
    } else {
        Some(number(&m["max_depth"])?)
    };
    if max_depth.is_some_and(|d| d > campaign_depth) {
        return Err(ManifestError::InvalidMaxDepth);
    }
    let files = array(&m["files"])?
        .iter()
        .map(|v| {
            let f = object(v, &["name", "sha256"])?;
            Ok(SourceFile {
                name: path(&f["name"])?,
                sha256: hash(&f["sha256"])?,
            })
        })
        .collect::<Result<Vec<_>, ManifestError>>()?;
    if files.windows(2).any(|p| p[0].name >= p[1].name) {
        return Err(schema("file order"));
    }
    let observation = array(&m["observation"])?
        .iter()
        .map(observation)
        .collect::<Result<Vec<_>, _>>()?;
    let vocabulary = StepObservation::vocabulary_of(&observation)
        .map_err(|e| ManifestError::Observation(e.to_string()))?;
    let tests = array(&m["tests"])?
        .iter()
        .map(|v| test(v, &observation, &vocabulary))
        .collect::<Result<Vec<_>, _>>()?;
    if tests.is_empty() || tests.iter().map(|t| &t.id).collect::<BTreeSet<_>>().len() != tests.len()
    {
        return Err(schema("test ids"));
    }
    Ok(DefinitionSpec {
        id: nonempty(&m["id"])?,
        root: DefinitionRoot {
            path: path(&root["path"])?,
            revision: optional(&root["revision"])?,
        },
        entry: path(&m["entry"])?,
        include_dirs: array(&m["include_dirs"])?
            .iter()
            .map(path)
            .collect::<Result<_, _>>()?,
        main_module: nonempty(&m["main_module"])?,
        syntax_module: optional(&m["syntax_module"])?,
        md_selector: optional(&m["md_selector"])?,
        files,
        requires_profile: if m["requires_profile"].is_null() {
            None
        } else if m["requires_profile"] == "z3" {
            Some(SolverProfile::Z3)
        } else {
            return Err(schema("requires_profile"));
        },
        max_depth,
        observation,
        tests,
    })
}
fn observation(v: &Value) -> Result<StepEventSpec, ManifestError> {
    let decode = || {
        let m = object(v, &["constructor", "pre", "post", "payload"])?;
        let decode_pattern = |v: &Value| {
            let p = from_value(v).map_err(|e| schema(e.to_string()))?;
            if to_value(&p).map_err(|e| schema(e.to_string()))? != *v {
                return Err(schema("canonical KORE"));
            }
            Ok(p)
        };
        Ok(StepEventSpec {
            constructor: nonempty(&m["constructor"])?,
            pre: decode_pattern(&m["pre"])?,
            post: if m["post"].is_null() {
                None
            } else {
                Some(decode_pattern(&m["post"])?)
            },
            payload: strings(&m["payload"])?,
        })
    };
    decode().map_err(|e: ManifestError| ManifestError::Observation(e.to_string()))
}
fn test(
    v: &Value,
    observation: &[StepEventSpec],
    vocabulary: &EventVocabulary,
) -> Result<CorpusTest, ManifestError> {
    let m = object(v, &["id", "input", "oracles"])?;
    let input = if let Some(kore) = m["input"].get("kore_state") {
        object(&m["input"], &["kore_state"])?;
        let k = object(kore, &["file", "sha256"])?;
        CorpusInput::KoreState {
            file: path(&k["file"])?,
            sha256: hash(&k["sha256"])?,
        }
    } else {
        let i = object(&m["input"], &["program", "start_sort", "variables"])?;
        let program = if let Some(file) = i["program"].get("file") {
            object(&i["program"], &["file"])?;
            ProgramSource::File(path(file)?)
        } else {
            let p = object(&i["program"], &["text"])?;
            ProgramSource::Text(string(&p["text"])?)
        };
        let variables = array(&i["variables"])?
            .iter()
            .map(|v| {
                let p = object(v, &["name", "text"])?;
                Ok((nonempty(&p["name"])?, string(&p["text"])?))
            })
            .collect::<Result<Vec<_>, ManifestError>>()?;
        if variables
            .iter()
            .map(|(n, _)| n)
            .collect::<BTreeSet<_>>()
            .len()
            != variables.len()
        {
            return Err(schema("variable names"));
        }
        CorpusInput::Program(TestInputSpec {
            program,
            start_sort: optional(&i["start_sort"])?,
            variables,
        })
    };
    let oracles = array(&m["oracles"])?
        .iter()
        .map(|v| oracle(v, observation, vocabulary))
        .collect::<Result<Vec<_>, _>>()?;
    if oracles.is_empty() {
        return Err(schema("empty oracles"));
    }
    Ok(CorpusTest {
        id: nonempty(&m["id"])?,
        input,
        oracles,
    })
}
fn oracle(
    v: &Value,
    observation: &[StepEventSpec],
    vocabulary: &EventVocabulary,
) -> Result<OracleDeclaration, ManifestError> {
    let o = object(v, &["crash_policy", "projection"])?;
    let crash_policy = match o["crash_policy"].as_str() {
        Some("reject") => CrashPolicy::Reject,
        Some("compare-identity") => CrashPolicy::CompareIdentity,
        Some("distinguish") => CrashPolicy::Distinguish,
        _ => return Err(schema("crash policy")),
    };
    let p = &o["projection"];
    let projection = if *p == "whole-term" {
        Projection::State(StateProjection::WholeTerm)
    } else if let Some(e) = p.get("exit-stop") {
        object(p, &["exit-stop"])?;
        let e = object(e, &["exit_code_cell"])?;
        Projection::State(StateProjection::ExitStop {
            exit_code_cell: optional(&e["exit_code_cell"])?,
        })
    } else if let Some(paths) = p.get("term-paths") {
        object(p, &["term-paths"])?;
        let paths = array(paths)?
            .iter()
            .map(|v| {
                array(v)?
                    .iter()
                    .map(|n| u32::try_from(number(n)?).map_err(|_| schema("path index")))
                    .collect()
            })
            .collect::<Result<_, ManifestError>>()?;
        Projection::State(StateProjection::TermPaths(paths))
    } else if let Some(pattern) = p.get("pattern") {
        object(p, &["pattern"])?;
        let p = object(pattern, &["plan", "with_bindings"])?;
        if observation.is_empty() {
            return Err(ManifestError::PatternOracle);
        }
        Projection::Pattern {
            plan: plan(&p["plan"], vocabulary)?,
            with_bindings: boolean(&p["with_bindings"])?,
        }
    } else {
        return Err(schema("projection"));
    };
    OracleDeclaration::new(crash_policy, projection).map_err(|e| schema(e.to_string()))
}
fn plan(v: &Value, vocabulary: &EventVocabulary) -> Result<PatternPlan, ManifestError> {
    let decode = || {
        let p = object(v, &["variables", "arms", "side_condition"])?;
        if !p["side_condition"].is_null() {
            return Err(ManifestError::PatternOracle);
        }
        let variables = array(&p["variables"])?
            .iter()
            .map(|v| {
                let m = object(v, &["name", "sort"])?;
                let text = string(&m["sort"])?;
                let sort: Sort = parse_pattern(&format!("X:{text}"))
                    .map_err(|e| schema(e.to_string()))?
                    .syntactic_sort()
                    .ok_or_else(|| schema("sort"))?
                    .clone();
                if sort.to_string() != text {
                    return Err(schema("canonical sort"));
                }
                Ok((nonempty(&m["name"])?, sort))
            })
            .collect::<Result<Vec<_>, ManifestError>>()?;
        let arms = array(&p["arms"])?
            .iter()
            .map(|v| {
                let m = object(v, &["atoms", "relations"])?;
                let atoms = array(&m["atoms"])?
                    .iter()
                    .map(|v| {
                        let a = object(v, &["constructor", "payload"])?;
                        let payload = array(&a["payload"])?
                            .iter()
                            .map(|v| {
                                let c = object(v, &["position", "mode", "variable"])?;
                                let mode = match c["mode"].as_str() {
                                    Some("bind") => MatchMode::Bind,
                                    Some("use") => MatchMode::Use,
                                    _ => return Err(schema("match mode")),
                                };
                                Ok(PayloadClause {
                                    position: usize::try_from(number(&c["position"])?)
                                        .map_err(|_| schema("position"))?,
                                    mode,
                                    variable: nonempty(&c["variable"])?,
                                })
                            })
                            .collect::<Result<_, ManifestError>>()?;
                        Ok(Atom {
                            constructor: nonempty(&a["constructor"])?,
                            payload,
                        })
                    })
                    .collect::<Result<_, ManifestError>>()?;
                let relations = array(&m["relations"])?
                    .iter()
                    .map(|v| match v.as_str() {
                        Some("next-event") => Ok(Relation::NextEvent),
                        Some("eventually-after") => Ok(Relation::EventuallyAfter),
                        _ => Err(schema("relation")),
                    })
                    .collect::<Result<_, _>>()?;
                Ok(PatternArm { atoms, relations })
            })
            .collect::<Result<_, ManifestError>>()?;
        PatternPlan::new(vocabulary, variables, arms, None)
            .map_err(|_| ManifestError::PatternOracle)
    };
    decode().map_err(|_| ManifestError::PatternOracle)
}
/// Match the author id, or any enclosing full conformance case directory.
pub fn exclusion_applies(definition: &DefinitionSpec, exclusion: &Exclusion) -> bool {
    if definition.id == exclusion.case {
        return true;
    }
    let joined = format!("{}/{}", definition.root.path, definition.entry);
    let Ok(parts) = normalized(&joined) else {
        return false;
    };
    path_excluded(&parts, &exclusion.case)
}
pub(crate) fn path_excluded(parts: &[String], case: &str) -> bool {
    let needle = format!("k-distribution/tests/regression-new/{case}")
        .split('/')
        .map(str::to_owned)
        .collect::<Vec<_>>();
    parts
        .windows(needle.len())
        .enumerate()
        .any(|(i, p)| p == needle && i + needle.len() < parts.len())
}
