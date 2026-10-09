//! Data operators over the declared written-rule universe.
//!
//! A `Sort` clause means the sentence typer's **placed** sort, not a production's
//! declared result sort. V1 refuses `Bag` and `#OptionalDots`: the result sorts of
//! the builtin `#cells`, `#dots` and `#noDots` productions in kast.md, which the
//! pinned typer treats as syntax without a placed sort. The constructor and codec
//! both enforce this refusal, before discovery can derive any site.

use crate::{
    Baseline, CandidateFailure, CandidateGeneration, CodecError, Edit, Patch, PatchOrigin,
    ResolvedUniverse, SelectionPolicy, Sha256Digest, SiteSelector, canonical_json, derive_sites_in,
    payload_digest, select,
};
use k_rust::kast::{Sort, Term, parser::parse_sort};
use serde_json::{Value, json};

pub const OPERATOR_DOMAIN: &str = "kink/operator/v1";

/// Result sorts of the pinned kast.md's syntax-only cell labels.
/// See KCELLS `#cells` and RULE-CELLS `#dots`/`#noDots` and
/// k-rust's `kompile/sort_injections/typing.rs` `PositionTyping::sort`.
pub const BUILTIN_CELL_SYNTAX_SORTS: [&str; 2] = ["#OptionalDots", "Bag"];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Clause {
    RuleLabel(String),
    Path(Vec<u32>),
    Sort(Sort),
    Head { label: String },
    NotHead { label: String },
    NotToken { token: String, sort: Sort },
    TokenOfSort { sort: Sort },
    RuleAttribute { key: String, present: bool },
    ArgumentCount { count: u32 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Action {
    ReplaceHead { to: String },
    ReplaceWithToken { token: String, sort: Sort },
    Wrap { label: String },
    Unwrap { argument: u32 },
    SwapArguments([u32; 2]),
    IntOffset(i64),
    RemoveAttribute { key: String },
    DeleteRule,
}

/// A validated v1 spec. Private fields prevent bypassing codec refusals.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperatorSpec {
    id: String,
    variant: String,
    version: u32,
    selector: Vec<Clause>,
    action: Action,
}

impl OperatorSpec {
    /// Builds a spec with the v1 `each` policy.
    ///
    /// # Errors
    /// Refuses a Sort clause naming a builtin cell-syntax sort.
    pub fn new(
        id: impl Into<String>,
        variant: impl Into<String>,
        version: u32,
        selector: Vec<Clause>,
        action: Action,
    ) -> Result<Self, CodecError> {
        for clause in &selector {
            if let Clause::Sort(sort) = clause
                && BUILTIN_CELL_SYNTAX_SORTS.contains(&sort.name.as_str())
            {
                return Err(decode(
                    "Sort clause names builtin cell syntax without a placed sort",
                ));
            }
        }
        Ok(Self {
            id: id.into(),
            variant: variant.into(),
            version,
            selector,
            action,
        })
    }

    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }
    #[must_use]
    pub fn variant(&self) -> &str {
        &self.variant
    }
    #[must_use]
    pub const fn version(&self) -> u32 {
        self.version
    }
    #[must_use]
    pub fn selector(&self) -> &[Clause] {
        &self.selector
    }
    #[must_use]
    pub const fn action(&self) -> &Action {
        &self.action
    }
    #[must_use]
    pub fn name(&self) -> String {
        format!("{}/{}@{}", self.id, self.variant, self.version)
    }
    #[must_use]
    pub fn canonical_value(&self) -> Value {
        json!({"id":self.id,"variant":self.variant,"version":self.version,
            "selector":self.selector.iter().map(Clause::value).collect::<Vec<_>>(),
            "policy":"each","action":self.action.value()})
    }
    #[must_use]
    pub fn canonical_json(&self) -> String {
        canonical_json(&self.canonical_value())
    }
    #[must_use]
    pub fn digest(&self) -> Sha256Digest {
        payload_digest(OPERATOR_DOMAIN, self.canonical_json().as_bytes())
    }

    /// Decodes exact keys and rejects every re-encoding difference.
    ///
    /// # Errors
    /// Returns Decode for invalid keys, types, policy, clauses or actions, and
    /// NonCanonical for noncanonical bytes (including noncanonical sort text).
    pub fn from_canonical_json(text: &str) -> Result<Self, CodecError> {
        let value: Value =
            serde_json::from_str(text).map_err(|e| CodecError::Decode(e.to_string()))?;
        exact(
            &value,
            &["id", "variant", "version", "selector", "policy", "action"],
        )?;
        if string(&value["policy"])? != "each" {
            return Err(decode("unknown policy"));
        }
        let spec = Self::new(
            string(&value["id"])?,
            string(&value["variant"])?,
            u32_value(&value["version"])?,
            array(&value["selector"])?
                .iter()
                .map(Clause::read)
                .collect::<Result<_, _>>()?,
            Action::read(&value["action"])?,
        )?;
        if spec.canonical_json() != text {
            return Err(CodecError::NonCanonical);
        }
        Ok(spec)
    }
}

impl Clause {
    fn value(&self) -> Value {
        match self {
            Self::RuleLabel(label) => json!({"rule-label":label}),
            Self::Path(path) => json!({"path":path}),
            Self::Sort(sort) => json!({"sort":sort.to_string()}),
            Self::Head { label } => json!({"head":label}),
            Self::NotHead { label } => json!({"not-head":label}),
            Self::NotToken { token, sort } => {
                json!({"not-token":{"token":token,"sort":sort.to_string()}})
            }
            Self::TokenOfSort { sort } => json!({"token-of-sort":sort.to_string()}),
            Self::RuleAttribute { key, present } => {
                json!({"rule-attribute":{"key":key,"present":present}})
            }
            Self::ArgumentCount { count } => json!({"argument-count":count}),
        }
    }
    fn read(value: &Value) -> Result<Self, CodecError> {
        let (tag, inner) = tagged(value)?;
        Ok(match tag {
            "rule-label" => Self::RuleLabel(string(inner)?.to_owned()),
            "path" => Self::Path(
                array(inner)?
                    .iter()
                    .map(u32_value)
                    .collect::<Result<_, _>>()?,
            ),
            "sort" => Self::Sort(sort(inner)?),
            "head" => Self::Head {
                label: string(inner)?.to_owned(),
            },
            "not-head" => Self::NotHead {
                label: string(inner)?.to_owned(),
            },
            "not-token" => {
                exact(inner, &["token", "sort"])?;
                Self::NotToken {
                    token: string(&inner["token"])?.to_owned(),
                    sort: sort(&inner["sort"])?,
                }
            }
            "token-of-sort" => Self::TokenOfSort { sort: sort(inner)? },
            "rule-attribute" => {
                exact(inner, &["key", "present"])?;
                Self::RuleAttribute {
                    key: string(&inner["key"])?.to_owned(),
                    present: inner["present"]
                        .as_bool()
                        .ok_or_else(|| decode("expected bool"))?,
                }
            }
            "argument-count" => Self::ArgumentCount {
                count: u32_value(inner)?,
            },
            _ => return Err(decode("unknown clause")),
        })
    }
    fn selector(&self) -> SiteSelector {
        match self {
            Self::RuleLabel(label) => SiteSelector::RuleLabel(label.clone()),
            Self::Path(path) => SiteSelector::Path(path.clone()),
            Self::Sort(sort) => SiteSelector::Sort(sort.clone()),
            Self::Head { label } => SiteSelector::Head {
                label: label.clone(),
            },
            Self::NotHead { label } => SiteSelector::NotHead {
                label: label.clone(),
            },
            Self::NotToken { token, sort } => SiteSelector::NotToken {
                token: token.clone(),
                sort: sort.clone(),
            },
            Self::TokenOfSort { sort } => SiteSelector::TokenOfSort { sort: sort.clone() },
            Self::RuleAttribute { key, present } => SiteSelector::RuleAttribute {
                key: key.clone(),
                present: *present,
            },
            Self::ArgumentCount { count } => SiteSelector::ArgumentCount { count: *count },
        }
    }
}

impl Action {
    fn value(&self) -> Value {
        match self {
            Self::ReplaceHead { to } => json!({"replace-head":{"to":to}}),
            Self::ReplaceWithToken { token, sort } => {
                json!({"replace-with-token":{"token":token,"sort":sort.to_string()}})
            }
            Self::Wrap { label } => json!({"wrap":{"label":label}}),
            Self::Unwrap { argument } => json!({"unwrap":{"argument":argument}}),
            Self::SwapArguments(indices) => json!({"swap-arguments":indices}),
            Self::IntOffset(offset) => json!({"int-offset":offset}),
            Self::RemoveAttribute { key } => json!({"remove-attribute":{"key":key}}),
            Self::DeleteRule => json!("delete-rule"),
        }
    }
    fn read(value: &Value) -> Result<Self, CodecError> {
        if value.as_str() == Some("delete-rule") {
            return Ok(Self::DeleteRule);
        }
        let (tag, inner) = tagged(value)?;
        Ok(match tag {
            "replace-head" => {
                exact(inner, &["to"])?;
                Self::ReplaceHead {
                    to: string(&inner["to"])?.to_owned(),
                }
            }
            "replace-with-token" => {
                exact(inner, &["token", "sort"])?;
                Self::ReplaceWithToken {
                    token: string(&inner["token"])?.to_owned(),
                    sort: sort(&inner["sort"])?,
                }
            }
            "wrap" => {
                exact(inner, &["label"])?;
                Self::Wrap {
                    label: string(&inner["label"])?.to_owned(),
                }
            }
            "unwrap" => {
                exact(inner, &["argument"])?;
                Self::Unwrap {
                    argument: u32_value(&inner["argument"])?,
                }
            }
            "swap-arguments" => {
                let indices = array(inner)?;
                if indices.len() != 2 {
                    return Err(decode("swap needs two indices"));
                }
                Self::SwapArguments([u32_value(&indices[0])?, u32_value(&indices[1])?])
            }
            "int-offset" => Self::IntOffset(inner.as_i64().ok_or_else(|| decode("expected i64"))?),
            "remove-attribute" => {
                exact(inner, &["key"])?;
                Self::RemoveAttribute {
                    key: string(&inner["key"])?.to_owned(),
                }
            }
            _ => return Err(decode("unknown action")),
        })
    }

    fn patch(&self, baseline: &Baseline, origin: &PatchOrigin) -> Patch {
        // Each selects one existing term position, and fold checks sentence authorization.
        let at = &origin.site_tuple[0];
        let expected = baseline.term(at).expect("derived site exists");
        let edit = match self {
            Self::RemoveAttribute { key } => baseline
                .sentence(&at.sentence)
                .and_then(|sentence| sentence.attributes().get(key))
                .map(|value| Edit::RemoveAttribute {
                    at: at.sentence.clone(),
                    key: key.clone(),
                    expected: value.clone(),
                }),
            Self::DeleteRule => Some(Edit::DeleteSentence {
                at: at.sentence.clone(),
            }),
            _ => None,
        }
        .unwrap_or_else(|| Edit::ReplaceTerm {
            at: at.clone(),
            expected: expected.clone(),
            replacement: self
                .replacement(expected)
                .unwrap_or_else(|| expected.clone()),
        });
        Patch::new(vec![edit]).expect("one edit is a nonempty patch")
    }

    fn replacement(&self, term: &Term) -> Option<Term> {
        match (self, term.unannotated()) {
            (Self::ReplaceHead { to }, Term::Apply { label, arguments }) => {
                let mut label = label.clone();
                label.name = to.clone();
                Some(Term::Apply {
                    label,
                    arguments: arguments.clone(),
                })
            }
            (Self::ReplaceWithToken { token, sort }, _) => Some(Term::Token {
                token: token.clone(),
                sort: sort.clone(),
            }),
            (Self::Wrap { label }, _) => Some(Term::apply(label, vec![term.clone()])),
            (Self::Unwrap { argument }, Term::Apply { arguments, .. }) => {
                arguments.get(usize::try_from(*argument).ok()?).cloned()
            }
            (Self::SwapArguments([a, b]), Term::Apply { label, arguments }) => {
                let a = usize::try_from(*a).ok()?;
                let b = usize::try_from(*b).ok()?;
                if a >= arguments.len() || b >= arguments.len() {
                    return None;
                }
                let mut arguments = arguments.clone();
                arguments.swap(a, b);
                Some(Term::Apply {
                    label: label.clone(),
                    arguments,
                })
            }
            (Self::IntOffset(offset), Term::Token { token, sort }) if *sort == Sort::new("Int") => {
                let value = token
                    .parse::<i128>()
                    .ok()?
                    .checked_add(i128::from(*offset))?;
                Some(Term::Token {
                    token: value.to_string(),
                    sort: sort.clone(),
                })
            }
            _ => None,
        }
    }
}

/// Derives and folds a data operator without supplied or filtered sites.
///
/// # Errors
/// Returns the discovery, selection or fold failure unchanged. An action that
/// cannot transform an origin yields a no-change patch and a rejected origin.
pub fn generate<'b>(
    baseline: &'b Baseline,
    universe: &ResolvedUniverse,
    spec: &OperatorSpec,
    cap: usize,
) -> Result<CandidateGeneration<'b>, CandidateFailure> {
    let clauses = spec
        .selector
        .iter()
        .map(Clause::selector)
        .collect::<Vec<_>>();
    let discovery = derive_sites_in(baseline, universe, &clauses)?;
    select(&discovery, SelectionPolicy::Each, cap)?
        .fold(&spec.name(), |origin| spec.action.patch(baseline, origin))
}

fn decode(detail: &str) -> CodecError {
    CodecError::Decode(detail.to_owned())
}
fn exact(value: &Value, keys: &[&str]) -> Result<(), CodecError> {
    let object = value.as_object().ok_or_else(|| decode("expected object"))?;
    if object.len() != keys.len() || keys.iter().any(|key| !object.contains_key(*key)) {
        return Err(decode("unexpected object keys"));
    }
    Ok(())
}
fn tagged(value: &Value) -> Result<(&str, &Value), CodecError> {
    let object = value
        .as_object()
        .ok_or_else(|| decode("expected tagged object"))?;
    if object.len() != 1 {
        return Err(decode("expected one tag"));
    }
    let (tag, inner) = object.iter().next().expect("one key");
    Ok((tag, inner))
}
fn string(value: &Value) -> Result<&str, CodecError> {
    value.as_str().ok_or_else(|| decode("expected string"))
}
fn array(value: &Value) -> Result<&Vec<Value>, CodecError> {
    value.as_array().ok_or_else(|| decode("expected array"))
}
fn u32_value(value: &Value) -> Result<u32, CodecError> {
    value
        .as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| decode("expected u32"))
}
fn sort(value: &Value) -> Result<Sort, CodecError> {
    parse_sort(string(value)?).map_err(|e| CodecError::Decode(e.to_string()))
}
