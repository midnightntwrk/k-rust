//! Chain patterns: `steps = [{ pattern = "...", unless = "..." }, ...]` in a `[[pattern]]`, in
//! place of `pattern` ([`super::PatternForm::Chain`]).
//!
//! **Meaning.** A chain of steps P1, [U2] P2, ..., [Un] Pn holds on a path of a run when the path
//! has states s1, ..., sn, each at or after the one before it, such that under one assignment of
//! the variables the parts share each si matches Pi (its body, with its `requires` true), and for
//! each i ≥ 2 that has an `unless` Ui no state strictly between s(i-1) and si matches Ui (with
//! Ui's `requires` true). It holds on a program when it holds on some path of the program's run.
//! `id`, `programs`, `expect` and `note` apply to a chain as to a single pattern.
//!
//! **Parts.** Each step's text and each `unless` text is a part: K text as a single pattern is
//! written, `requires` included, lowered alone by [`Lowering::lower`] to `\and(body, P...)` and
//! its generated variables. A `=>` inside a part keeps the meaning K gives it in a pattern: the
//! part denotes the configurations its left side matches. A part's variables are the free
//! variables of its target that the compiler did not mint, by the compiler's own record of what
//! it minted ([`LoweredPattern::minted`]) and never by a name's spelling, each a KORE name and
//! sort; a
//! step's variables are those of its body and those of its `requires`, and an `unless`'s are those
//! of its own body and `requires`. The rules on them ([`chain_variables`]):
//! - A variable named in exactly one part is local to it. A step's body-only local is bound by
//!   the step's match and reported, and no later part needs it. A step's requires-only local is
//!   existential, as in a single pattern. An `unless`'s local is existential: one value of it for
//!   which a state matches kills the chain's progress there.
//! - A variable named in two or more parts is shared, and one value of it is carried from the
//!   part that binds it to every later part that names it. It is bound by the body of the first
//!   step whose body names it, step i; that step must exist. Every other part naming it comes
//!   after that body: step j's body or `requires` with j ≥ i, or step j's `unless` with j > i. So
//!   a step's `requires` names no variable a later step's body binds, and an `unless`, which is
//!   matched on the states before its own step, names no variable its own or a later step binds.
//!   A variable named only in `requires` or only in `unless` parts is never bound, so no one
//!   value of it can be carried, and a set variable binds a set of values, which is not carried
//!   either: both are refused when shared. So is a written variable that stands for several
//!   cells of one cell in some part ([`LoweredPattern::split`]): the compiler replaces it there
//!   by one variable per cell, so no variable of the target is it.
//! - Every occurrence of a shared variable has one sort. A KORE variable carries its sort, so a
//!   name written `P:Int` in one part and inferred as `P:K` in another names two variables, which
//!   is refused rather than read as two unrelated values.
//!
//! A violation is [`super::INVALID_PATTERN`], with a message naming each variable and the parts.
//!
//! **Decoding** ([`decode_steps`]). `steps` is a non-empty array of tables with a non-empty
//! `pattern` and an optional non-empty `unless`; the first step has no `unless`, since no step
//! comes before it; `pattern` and `steps` are exclusive. A violation is an error naming the key,
//! as every decoding error is. A chain of one step without `unless` asks exactly what its
//! `pattern` asks, and is decoded as that single pattern, so it has the single pattern's entry,
//! lowering, digest and every key and record.
//!
//! **Digest** ([`CHAIN_DOMAIN`]). The canonical KORE JSON of `{steps: [{target, generated,
//! unless: null | {target, generated}}]}`, each part's compiled target and generated variables as
//! a single pattern's digest takes them: the layout of the text, the `id` and the `note` are not
//! in it. Each step's imports and exports are a function of the targets, so they are not in it.

use super::{LoweredPattern, Lowering, PatternForm, generated, join, known_keys, non_empty};
use crate::manifest::ManifestError;
use k_rust::{
    k_rust_backend::definition::BackendDefinition,
    kast::identifier::decode_variable,
    kore::{
        ast::{Pattern, Sort, Variable, VariableKind},
        json as kore_json,
    },
};
use kink_native::execution::{ChainRequest, ChainStepRequest, UnlessRequest};
use kink_patch::{Sha256Digest, canonical_json, payload_digest};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use toml::Value as TomlValue;

/// Domain of a chain's digest: each part's KORE target and the variables the compiler generated
/// (module docs).
pub const CHAIN_DOMAIN: &str = "kink-flow/chain/v1";

/// How a chain's text becomes the request its run makes: each part lowered as a single pattern
/// is ([`super::LOWERING_VERSION`]), and each step's imports and exports from the rules on the
/// variables ([`Lowering::lower_chain`], [`LoweredChain::request`]). It is the `lowering` of every
/// cached chain answer's key, in place of a single pattern's, so it changes whenever kink changes
/// either.
pub const CHAIN_LOWERING_VERSION: &str = "kink-flow/chain-lowering/v1";

/// One step of a chain as the list writes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepText {
    /// The step's K text, written as a single pattern's.
    pub pattern: String,
    /// The K text of the step's `unless` (a step after the first): no state strictly between the
    /// state of the step before and this step's state matches it.
    pub unless: Option<String>,
}

/// Decode `steps` (module docs, "Decoding"), whose key is `key`: a chain of at least two steps,
/// or the single pattern a chain of one step without `unless` is.
pub(super) fn decode_steps(value: &TomlValue, key: &str) -> Result<PatternForm, ManifestError> {
    let TomlValue::Array(items) = value else {
        return Err(ManifestError::new(
            key,
            "expected an array of step tables `{ pattern = \"...\", unless = \"...\" }`",
        ));
    };
    if items.is_empty() {
        return Err(ManifestError::new(
            key,
            "must not be empty: a chain has at least one step",
        ));
    }
    let mut steps = items
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let at = format!("{key}[{index}]");
            let table = item.as_table().ok_or_else(|| {
                ManifestError::new(
                    &at,
                    "expected a table `{ pattern = \"...\", unless = \"...\" }`",
                )
            })?;
            known_keys(table, &at, &["pattern", "unless"])?;
            let pattern = non_empty(
                table.get("pattern").ok_or_else(|| {
                    ManifestError::new(join(&at, "pattern"), "missing required key")
                })?,
                &join(&at, "pattern"),
            )?;
            let unless = table
                .get("unless")
                .map(|unless| non_empty(unless, &join(&at, "unless")))
                .transpose()?;
            if index == 0 && unless.is_some() {
                return Err(ManifestError::new(
                    join(&at, "unless"),
                    "the first step has no `unless`: an `unless` constrains the states between \
                     a step and the step before it",
                ));
            }
            Ok(StepText { pattern, unless })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if steps.len() == 1 {
        let step = steps.swap_remove(0);
        debug_assert!(step.unless.is_none(), "the first step has no unless");
        return Ok(PatternForm::Single(step.pattern));
    }
    Ok(PatternForm::Chain(steps))
}

/// A chain lowered to its parts' KORE targets ([`Lowering::lower_chain`]).
#[derive(Clone, Debug)]
pub struct LoweredChain {
    /// The steps, in order.
    pub steps: Vec<LoweredStep>,
    /// [`CHAIN_DOMAIN`] digest of the parts' targets and generated variables (module docs).
    pub digest: Sha256Digest,
}

/// One lowered step of a chain.
#[derive(Clone, Debug)]
pub struct LoweredStep {
    /// The step's own lowering, as a single pattern's.
    pub pattern: LoweredPattern,
    /// The shared variables the step names (body or `requires`) that an earlier step's body
    /// binds, in variable order: the step is matched with their values substituted.
    pub imports: Vec<Variable>,
    /// The variables the step's body binds that a later part names, in variable order: what a
    /// match of the step carries to the parts after it. A variable only the step names is not
    /// carried.
    pub exports: Vec<Variable>,
    /// The step's `unless` (never on the first step).
    pub unless: Option<LoweredUnless>,
}

/// A lowered `unless` of a step.
#[derive(Clone, Debug)]
pub struct LoweredUnless {
    /// The `unless`'s own lowering, as a single pattern's.
    pub pattern: LoweredPattern,
    /// The shared variables the `unless` names, all bound by the body of a step before its own,
    /// in variable order: it is matched with their values substituted, and its other variables
    /// are existential.
    pub imports: Vec<Variable>,
}

impl LoweredChain {
    /// The request a run matches this chain by: each step's target, its imports and exports, and
    /// its `unless`'s target and imports, in step order, keeping at most `partial_cap` partial
    /// occurrences per path.
    #[must_use]
    pub fn request(&self, partial_cap: usize) -> ChainRequest {
        ChainRequest {
            steps: self
                .steps
                .iter()
                .map(|step| ChainStepRequest {
                    pattern: step.pattern.target.clone(),
                    imports: step.imports.clone(),
                    exports: step.exports.clone(),
                    unless: step.unless.as_ref().map(|unless| UnlessRequest {
                        pattern: unless.pattern.target.clone(),
                        imports: unless.imports.clone(),
                    }),
                })
                .collect(),
            partial_cap,
        }
    }

    /// The digest of `steps`, each a lowered step and its lowered `unless` (module docs).
    fn digest_of(
        steps: &[(LoweredPattern, Option<LoweredPattern>)],
    ) -> Result<Sha256Digest, String> {
        let part = |lowered: &LoweredPattern| -> Result<Value, String> {
            let target = kore_json::to_value(&lowered.target)
                .map_err(|e| format!("cannot encode the compiled pattern: {e}"))?;
            Ok(json!({"target": target, "generated": lowered.generated}))
        };
        let steps = steps
            .iter()
            .map(|(step, unless)| {
                let mut value = part(step)?;
                value["unless"] = unless
                    .as_ref()
                    .map(part)
                    .transpose()?
                    .unwrap_or(Value::Null);
                Ok(value)
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(payload_digest(
            CHAIN_DOMAIN,
            canonical_json(&json!({ "steps": steps })).as_bytes(),
        ))
    }
}

impl Lowering {
    /// Lower a chain (module docs): each part by [`Lowering::lower`], against `definition`, then
    /// the rules on the variables the parts share ([`chain_variables`]). A part's refusal names
    /// the part (`step 2: ...`, `step 2's unless: ...`) before k-rust's message.
    pub fn lower_chain(
        &self,
        steps: &[StepText],
        definition: &BackendDefinition,
    ) -> Result<LoweredChain, String> {
        if steps.is_empty() {
            return Err("a chain has at least one step".to_owned());
        }
        let parts = steps
            .iter()
            .enumerate()
            .map(|(index, step)| {
                let number = index + 1;
                if index == 0 && step.unless.is_some() {
                    return Err("step 1 has an `unless`, which only a later step has".to_owned());
                }
                let pattern = self
                    .lower(&step.pattern, definition)
                    .map_err(|e| format!("step {number}: {e}"))?;
                let unless = step
                    .unless
                    .as_deref()
                    .map(|text| {
                        self.lower(text, definition)
                            .map_err(|e| format!("step {number}'s unless: {e}"))
                    })
                    .transpose()?;
                Ok((pattern, unless))
            })
            .collect::<Result<Vec<_>, String>>()?;
        LoweredChain::from_parts(parts)
    }
}

impl LoweredChain {
    /// The chain of the lowered parts `parts`, each a step and its `unless`, in order: the rules
    /// on the variables the parts share ([`chain_variables`]), each step's imports and exports,
    /// and the digest. [`Lowering::lower_chain`] builds every chain so, and an explanation builds
    /// a chain's prefixes and the chains it derives from them so ([`super::explain`]).
    pub fn from_parts(
        parts: Vec<(LoweredPattern, Option<LoweredPattern>)>,
    ) -> Result<Self, String> {
        let variables = chain_variables(&parts)?;
        let digest = Self::digest_of(&parts)?;
        let steps = parts
            .into_iter()
            .zip(variables)
            .map(|((pattern, unless), variables)| LoweredStep {
                pattern,
                imports: variables.imports,
                exports: variables.exports,
                unless: unless.map(|pattern| LoweredUnless {
                    pattern,
                    imports: variables.unless_imports,
                }),
            })
            .collect();
        Ok(Self { steps, digest })
    }

    /// The parts of the first `count` steps, each a step's lowering and its `unless`'s, in
    /// order: what [`Self::from_parts`] builds a prefix of the chain from.
    #[must_use]
    pub fn parts(&self, count: usize) -> Vec<(LoweredPattern, Option<LoweredPattern>)> {
        self.steps
            .iter()
            .take(count)
            .map(|step| {
                (
                    step.pattern.clone(),
                    step.unless.as_ref().map(|unless| unless.pattern.clone()),
                )
            })
            .collect()
    }
}

/// A part of a chain where a variable is named, by step index (from 0).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Part {
    /// The `unless` of the step.
    Unless(usize),
    /// The step's body.
    Body(usize),
    /// The step's `requires`.
    Requires(usize),
}

impl Part {
    /// The part's place in the chain's order: a step's `unless` is matched on the states before
    /// the step's own, so it comes before the step's body and `requires`, which one match
    /// decides together.
    const fn position(self) -> (usize, u8) {
        match self {
            Self::Unless(step) => (step, 0),
            Self::Body(step) | Self::Requires(step) => (step, 1),
        }
    }

    /// The part as a unit of the chain: a step (its body and `requires` together) or a step's
    /// `unless`.
    fn unit(self) -> String {
        match self {
            Self::Unless(_) => self.describe(),
            Self::Body(step) | Self::Requires(step) => format!("step {}", step + 1),
        }
    }

    fn describe(self) -> String {
        match self {
            Self::Unless(step) => format!("step {}'s unless", step + 1),
            Self::Body(step) => format!("step {}'s body", step + 1),
            Self::Requires(step) => format!("step {}'s requires", step + 1),
        }
    }
}

/// The variables of one step of a chain that its evaluation carries ([`LoweredStep`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct StepVariables {
    imports: Vec<Variable>,
    exports: Vec<Variable>,
    unless_imports: Vec<Variable>,
}

/// The variables `lowered` names that the compiler did not generate: those free in its body and
/// those free in its `requires` (the target is `\and(body, P...)`).
fn named_variables(lowered: &LoweredPattern) -> (BTreeSet<Variable>, BTreeSet<Variable>) {
    let (body, predicates): (&Pattern, &[Pattern]) = match &lowered.target {
        Pattern::And { arguments, .. } => match arguments.split_first() {
            Some((body, predicates)) => (body, predicates),
            None => return (BTreeSet::new(), BTreeSet::new()),
        },
        other => (other, &[]),
    };
    let named = |variables: BTreeSet<Variable>| {
        variables
            .into_iter()
            .filter(|variable| !generated(lowered, &variable.name))
            .collect::<BTreeSet<_>>()
    };
    let requires = predicates
        .iter()
        .flat_map(Pattern::free_variables)
        .collect::<BTreeSet<_>>();
    (named(body.free_variables()), named(requires))
}

/// The K spelling of a KORE variable name for a message.
fn variable_label(name: &str) -> String {
    let (kind, decoded) = decode_variable(name);
    let decoded = decoded.unwrap_or_else(|_| name.to_owned());
    match kind {
        VariableKind::Element => decoded,
        VariableKind::Set => format!("@{decoded}"),
    }
}

/// The K spelling of a KORE sort for a message (`SortInt{}` is `Int`).
fn sort_label(sort: &Sort) -> String {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => name
            .strip_prefix("Sort")
            .map_or_else(|| sort.to_string(), str::to_owned),
        _ => sort.to_string(),
    }
}

/// `items` as an English list: `a`, `a and b`, `a, b and c`.
fn listed(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// Check the rules on a chain's variables (module docs, "Parts") over its lowered parts (each
/// step and its `unless`), and give each step's imports and exports and its `unless`'s imports.
/// Every violation is named, each with its variable and the parts, in variable order.
fn chain_variables(
    parts: &[(LoweredPattern, Option<LoweredPattern>)],
) -> Result<Vec<StepVariables>, String> {
    // Every occurrence of a named variable, by KORE name: the part and the variable (its sort).
    let mut occurrences: BTreeMap<&str, Vec<(Part, &Variable)>> = BTreeMap::new();
    let named = parts
        .iter()
        .enumerate()
        .map(|(step, (pattern, unless))| {
            let (body, requires) = named_variables(pattern);
            let unless = unless.as_ref().map(|unless| {
                let (body, requires) = named_variables(unless);
                body.union(&requires).cloned().collect::<BTreeSet<_>>()
            });
            (step, body, requires, unless.unwrap_or_default())
        })
        .collect::<Vec<_>>();
    for (step, body, requires, unless) in &named {
        for (part, variables) in [
            (Part::Unless(*step), unless),
            (Part::Body(*step), body),
            (Part::Requires(*step), requires),
        ] {
            for variable in variables {
                occurrences
                    .entry(variable.name.as_str())
                    .or_default()
                    .push((part, variable));
            }
        }
    }
    let mut variables = vec![StepVariables::default(); parts.len()];
    let mut imports = vec![BTreeSet::new(); parts.len()];
    let mut exports = vec![BTreeSet::new(); parts.len()];
    let mut unless_imports = vec![BTreeSet::new(); parts.len()];
    // Each violation with the KORE name of its variable, sorted by it at the end.
    let mut violations: Vec<(&str, String)> = Vec::new();
    // A written variable that stands for several cells is replaced by one minted variable per
    // cell, so no variable of the target is it: it is shared when another part names it.
    let mut split: BTreeMap<&str, Vec<Part>> = BTreeMap::new();
    for (step, (pattern, unless)) in parts.iter().enumerate() {
        for name in &pattern.split {
            split.entry(name).or_default().push(Part::Body(step));
        }
        for name in unless.iter().flat_map(|unless| &unless.split) {
            split.entry(name).or_default().push(Part::Unless(step));
        }
    }
    for (name, written) in &split {
        let mut named = written.clone();
        named.extend(
            occurrences
                .get(name)
                .into_iter()
                .flatten()
                .map(|(part, _)| *part),
        );
        named.sort_by_key(|part| part.position());
        let mut units = named.iter().map(|part| part.unit()).collect::<Vec<_>>();
        units.dedup();
        if units.len() < 2 {
            continue;
        }
        let mut cells = written.iter().map(|part| part.unit()).collect::<Vec<_>>();
        cells.dedup();
        violations.push((
            name,
            format!(
                "the variable {} is named in {} and stands for several cells in {}, where the \
                 compiler replaces it by one variable per cell, so no one value of it is carried \
                 between the parts; name the cells it stands for instead",
                variable_label(name),
                listed(&units),
                listed(&cells),
            ),
        ));
    }
    for (name, occurring) in &occurrences {
        if split.contains_key(name) {
            continue;
        }
        // A step's body and `requires` are one part, its `unless` another.
        let units = occurring
            .iter()
            .map(|(part, _)| match part {
                Part::Unless(step) => (*step, true),
                Part::Body(step) | Part::Requires(step) => (*step, false),
            })
            .collect::<BTreeSet<_>>();
        if units.len() < 2 {
            continue;
        }
        let label = variable_label(name);
        // The parts in chain order, each once.
        let in_order = |parts: &mut dyn Iterator<Item = Part>, describe: fn(Part) -> String| {
            let mut parts = parts.collect::<Vec<_>>();
            parts.sort_by_key(|part| part.position());
            let mut described = parts.into_iter().map(describe).collect::<Vec<_>>();
            described.dedup();
            listed(&described)
        };
        let units_named = in_order(&mut occurring.iter().map(|(part, _)| *part), Part::unit);
        let mut sorts: BTreeMap<&Sort, Vec<Part>> = BTreeMap::new();
        for (part, variable) in occurring {
            sorts.entry(&variable.sort).or_default().push(*part);
        }
        let before = violations.len();
        if occurring
            .iter()
            .any(|(_, variable)| variable.kind == VariableKind::Set)
        {
            violations.push((
                name,
                format!(
                    "the set variable {label} is named in {}: a set variable is matched against a \
                 set of values, which is not carried from one part to another, so give it a \
                 different name in each part",
                    units_named,
                ),
            ));
        }
        if sorts.len() > 1 {
            let each = sorts
                .iter()
                .map(|(sort, parts)| {
                    format!(
                        "sort {} (in {})",
                        sort_label(sort),
                        in_order(&mut parts.iter().copied(), Part::unit)
                    )
                })
                .collect::<Vec<_>>();
            violations.push((
                name,
                format!(
                    "the variable {label} has {}: a variable the parts share has one sort, so \
                 write the same sort in every part that names it (`{label}:{}`)",
                    listed(&each),
                    sort_label(sorts.keys().next().expect("two sorts")),
                ),
            ));
        }
        let binding = occurring
            .iter()
            .filter_map(|(part, _)| match part {
                Part::Body(step) => Some(*step),
                Part::Unless(_) | Part::Requires(_) => None,
            })
            .min();
        let Some(binding) = binding else {
            violations.push((name, format!(
                "the variable {label} is named in {} and in no step's body: a variable the parts \
                 share is bound by the body of the first step that names it, which carries one \
                 value of it to the later parts, so name it in a step's body or give it a \
                 different name in each part",
                in_order(&mut occurring.iter().map(|(part, _)| *part), Part::describe),
            )));
            continue;
        };
        let bound_at = Part::Body(binding);
        for early in occurring
            .iter()
            .map(|(part, _)| *part)
            .filter(|part| part.position() < bound_at.position())
            .collect::<BTreeSet<_>>()
        {
            let rule = match early {
                Part::Unless(_) => {
                    "an `unless` is matched on the states before its step's, so it names only \
                     variables that a step before its own binds"
                }
                Part::Requires(_) | Part::Body(_) => {
                    "a step's `requires` names only variables that its own body or an earlier \
                     step's body binds"
                }
            };
            violations.push((name, format!(
                "the variable {label} is named in {} but bound by {}, the first step's body that \
                 names it: {rule}",
                early.describe(),
                bound_at.describe(),
            )));
        }
        if violations.len() > before {
            continue;
        }
        let variable = occurring[0].1;
        exports[binding].insert(variable.clone());
        for (part, _) in occurring {
            match *part {
                Part::Body(step) | Part::Requires(step) if step > binding => {
                    imports[step].insert(variable.clone());
                }
                Part::Unless(step) => {
                    unless_imports[step].insert(variable.clone());
                }
                Part::Body(_) | Part::Requires(_) => {}
            }
        }
    }
    if !violations.is_empty() {
        violations.sort_by_key(|(name, _)| *name);
        let messages = violations
            .into_iter()
            .map(|(_, message)| message)
            .collect::<Vec<_>>();
        return Err(messages.join("; "));
    }
    for (step, variables) in variables.iter_mut().enumerate() {
        variables.imports = std::mem::take(&mut imports[step]).into_iter().collect();
        variables.exports = std::mem::take(&mut exports[step]).into_iter().collect();
        variables.unless_imports = std::mem::take(&mut unless_imports[step])
            .into_iter()
            .collect();
    }
    Ok(variables)
}

#[cfg(test)]
mod tests {
    //! The rules on a chain's variables over hand-built targets, one corner at a time, then the
    //! decoding of `steps`, then the lowering of real chains on calc.
    use super::*;
    use crate::{
        manifest::FlowManifest,
        pattern::{PATTERN_DOMAIN, PatternList, Searcher},
    };
    use k_rust::kore::parser::parse_pattern;
    use std::path::Path;

    /// A variable written `P` (sort Int), `P:Sort`, or `@P` (a set variable of sort Int), as
    /// KORE text.
    fn variable(written: &str) -> String {
        let (name, sort) = written.split_once(':').unwrap_or((written, "Int"));
        match name.strip_prefix('@') {
            Some(name) => format!("@Var{name}:Sort{sort}{{}}"),
            None => format!("Var{name}:Sort{sort}{{}}"),
        }
    }

    /// A lowered part whose body names `body` and whose `requires` names `requires`.
    fn part(body: &[&str], requires: &[&str]) -> LoweredPattern {
        let body = format!(
            "Lblbody{{}}({})",
            body.iter()
                .map(|v| variable(v))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let predicates = if requires.is_empty() {
            vec![r"\top{SortGeneratedTopCell{}}()".to_owned()]
        } else {
            requires
                .iter()
                .map(|v| {
                    format!(
                        r#"\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(Lblcond{{}}({}), \dv{{SortBool{{}}}}("true"))"#,
                        variable(v)
                    )
                })
                .collect()
        };
        let target = format!(
            r"\and{{SortGeneratedTopCell{{}}}}({body}, {})",
            predicates.join(", ")
        );
        LoweredPattern {
            target: parse_pattern(&target).unwrap(),
            generated: BTreeSet::new(),
            minted: BTreeSet::new(),
            split: BTreeSet::new(),
            digest: payload_digest(PATTERN_DOMAIN, b"test"),
            requires_only: BTreeSet::new(),
        }
    }

    fn step(body: &[&str], requires: &[&str]) -> (LoweredPattern, Option<LoweredPattern>) {
        (part(body, requires), None)
    }

    fn guarded(
        body: &[&str],
        requires: &[&str],
        unless: (&[&str], &[&str]),
    ) -> (LoweredPattern, Option<LoweredPattern>) {
        (part(body, requires), Some(part(unless.0, unless.1)))
    }

    fn names(variables: &[Variable]) -> Vec<String> {
        variables.iter().map(ToString::to_string).collect()
    }

    /// Each step's (imports, exports, unless imports), as KORE text.
    fn carried(
        parts: &[(LoweredPattern, Option<LoweredPattern>)],
    ) -> Vec<(Vec<String>, Vec<String>, Vec<String>)> {
        chain_variables(parts)
            .unwrap()
            .iter()
            .map(|step| {
                (
                    names(&step.imports),
                    names(&step.exports),
                    names(&step.unless_imports),
                )
            })
            .collect()
    }

    #[track_caller]
    fn refused(parts: &[(LoweredPattern, Option<LoweredPattern>)], expected: &[&str]) {
        let message = chain_variables(parts).unwrap_err();
        for part in expected {
            assert!(message.contains(part), "{part:?} in {message}");
        }
    }

    const NONE: (Vec<String>, Vec<String>, Vec<String>) = (Vec::new(), Vec::new(), Vec::new());

    fn p() -> Vec<String> {
        vec!["VarP:SortInt{}".to_owned()]
    }

    #[test]
    fn a_variable_in_one_part_is_local_and_carried_nowhere() {
        // Q only in step 1's body (reported, not carried), R only in step 2's requires (an
        // existential), S only in step 2's unless (an existential), T in step 1's body and its
        // own requires (one part).
        let parts = [
            step(&["Q", "T"], &["T"]),
            guarded(&[], &["R"], (&["S"], &["S"])),
        ];
        assert_eq!(carried(&parts), vec![NONE, NONE]);
    }

    #[test]
    fn a_shared_variable_is_bound_by_the_first_body_and_imported_after() {
        // Bound by step 1's body, named again in step 2's body and requires, and in step 3's
        // requires only: step 1 exports it and both later steps import it.
        let parts = [step(&["P"], &[]), step(&["P"], &["P"]), step(&[], &["P"])];
        assert_eq!(
            carried(&parts),
            vec![
                (vec![], p(), vec![]),
                (p(), vec![], vec![]),
                (p(), vec![], vec![]),
            ]
        );
        // The step that binds it may name it in its own requires.
        let parts = [step(&[], &[]), step(&["P"], &["P"]), step(&["P"], &[])];
        assert_eq!(
            carried(&parts),
            vec![NONE, (vec![], p(), vec![]), (p(), vec![], vec![])]
        );
    }

    #[test]
    fn an_unless_after_the_binding_step_imports_the_variable() {
        // P is bound by step 2's body and named in step 3's unless.
        let parts = [
            step(&[], &[]),
            step(&["P"], &[]),
            guarded(&[], &[], (&["P"], &[])),
        ];
        assert_eq!(
            carried(&parts),
            vec![NONE, (vec![], p(), vec![]), (vec![], vec![], p())]
        );
        // In an unless's requires as well.
        let parts = [step(&["P"], &[]), guarded(&[], &[], (&[], &["P"]))];
        assert_eq!(
            carried(&parts),
            vec![(vec![], p(), vec![]), (vec![], vec![], p())]
        );
    }

    #[test]
    fn a_variable_in_two_requires_only_is_refused() {
        refused(
            &[step(&[], &["P"]), step(&[], &["P"])],
            &[
                "the variable P is named in step 1's requires and step 2's requires and in no \
                 step's body",
            ],
        );
    }

    #[test]
    fn a_variable_in_two_unlesses_only_is_refused() {
        refused(
            &[
                step(&[], &[]),
                guarded(&[], &[], (&["P"], &[])),
                guarded(&[], &[], (&[], &["P"])),
            ],
            &[
                "the variable P is named in step 2's unless and step 3's unless and in no step's body",
            ],
        );
    }

    #[test]
    fn a_requires_before_the_binding_body_is_refused() {
        refused(
            &[step(&[], &["P"]), step(&["P"], &[])],
            &[
                "the variable P is named in step 1's requires but bound by step 2's body",
                "a step's `requires` names only variables",
            ],
        );
    }

    #[test]
    fn an_unless_at_or_before_the_binding_step_is_refused() {
        // At the binding step: U2 is matched on the states before step 2's.
        refused(
            &[step(&[], &[]), guarded(&["P"], &[], (&["P"], &[]))],
            &[
                "the variable P is named in step 2's unless but bound by step 2's body",
                "an `unless` is matched on the states before its step's",
            ],
        );
        // Before it: U2 names a variable step 3 binds.
        refused(
            &[
                step(&[], &[]),
                guarded(&[], &[], (&[], &["P"])),
                step(&["P"], &[]),
            ],
            &["the variable P is named in step 2's unless but bound by step 3's body"],
        );
    }

    #[test]
    fn a_shared_variable_has_one_sort() {
        refused(
            &[step(&["P:Int"], &[]), step(&["P:K"], &[])],
            &[
                "the variable P has sort Int (in step 1) and sort K (in step 2)",
                "`P:Int`",
            ],
        );
        // An unless naming the variable shares it as a step does.
        refused(
            &[
                step(&["P:Int"], &[]),
                guarded(&[], &[], (&["P:KItem"], &[])),
            ],
            &["sort Int (in step 1) and sort KItem (in step 2's unless)"],
        );
    }

    #[test]
    fn a_shared_set_variable_is_refused() {
        refused(
            &[step(&["@S"], &[]), step(&["@S"], &[])],
            &["the set variable @S is named in step 1 and step 2"],
        );
    }

    #[test]
    fn every_violation_is_named_in_variable_order() {
        let message = chain_variables(&[
            step(&["B"], &["A"]),
            step(&["A"], &["C"]),
            step(&[], &["C"]),
        ])
        .unwrap_err();
        let a = message.find("variable A").unwrap();
        let c = message.find("variable C").unwrap();
        assert!(a < c, "{message}");
        assert_eq!(message.matches("; ").count(), 1, "{message}");
    }

    #[test]
    fn imports_and_exports_are_in_variable_order() {
        // Written Z, B, A in step 1: carried in variable order; step 3 imports from step 1
        // directly, past step 2, which names none of them.
        let parts = [
            step(&["Z", "B", "A"], &[]),
            step(&[], &[]),
            step(&["A", "Z"], &["B"]),
        ];
        let abz = vec![
            "VarA:SortInt{}".to_owned(),
            "VarB:SortInt{}".to_owned(),
            "VarZ:SortInt{}".to_owned(),
        ];
        assert_eq!(
            carried(&parts),
            vec![(vec![], abz.clone(), vec![]), NONE, (abz, vec![], vec![])]
        );
    }

    #[test]
    fn minted_variables_are_never_shared() {
        // `G` and `D` are recorded as minted in each part: each part's are its own, whatever
        // their sorts.
        let minted = |sort: &str| {
            let mut lowered = part(&[&format!("G:{sort}"), &format!("D:{sort}")], &[]);
            lowered.minted = BTreeSet::from(["VarG".to_owned(), "VarD".to_owned()]);
            (lowered, None)
        };
        assert_eq!(carried(&[minted("Int"), minted("K")]), vec![NONE, NONE]);
    }

    #[test]
    fn a_written_variable_is_shared_whatever_its_spelling() {
        // Spelled as the compiler spells what it mints, but not recorded as minted: the
        // author's, so shared, and its two sorts are refused.
        let written = |sort: &str| {
            let mut lowered = part(&[], &[]);
            lowered.target = parse_pattern(&format!(
                r"\and{{SortGeneratedTopCell{{}}}}(Lblbody{{}}(Var'Unds'Gen0:Sort{sort}{{}}), \top{{SortGeneratedTopCell{{}}}}())"
            ))
            .unwrap();
            (lowered, None)
        };
        refused(
            &[written("Int"), written("K")],
            &["the variable _Gen0 has sort Int (in step 1) and sort K (in step 2)"],
        );
    }

    #[test]
    fn a_variable_split_into_cells_is_not_shared() {
        // X stands for several cells in step 1, so the target names its cells, not X.
        let mut first = part(&[], &[]);
        first.split = BTreeSet::from(["VarX".to_owned()]);
        refused(
            &[(first.clone(), None), step(&["X"], &[])],
            &[
                "the variable X is named in step 1 and step 2 and stands for several cells in \
                 step 1",
            ],
        );
        refused(
            &[(first.clone(), None), (first.clone(), None)],
            &["stands for several cells in step 1 and step 2"],
        );
        // Split in one part and named nowhere else: local.
        assert_eq!(carried(&[(first, None), step(&[], &[])]), vec![NONE, NONE]);
    }

    fn decoded(steps: &str) -> Result<PatternList, ManifestError> {
        PatternList::decode(&format!("[[pattern]]\nid = \"a\"\nsteps = {steps}\n"))
    }

    #[track_caller]
    fn decode_error(steps: &str, key: &str, message: &str) {
        let error = decoded(steps).unwrap_err();
        assert_eq!(error.key, key, "{error}");
        assert!(error.message.contains(message), "{error}");
    }

    #[test]
    fn steps_decode_strictly() {
        decode_error("[]", "pattern \"a\".steps", "must not be empty");
        decode_error("\"<k> 1 </k>\"", "pattern \"a\".steps", "expected an array");
        decode_error(
            "[\"<k> 1 </k>\"]",
            "pattern \"a\".steps[0]",
            "expected a table",
        );
        decode_error(
            "[{ pattern = \"<k> 1 </k>\", unless = \"<k> 2 </k>\" }]",
            "pattern \"a\".steps[0].unless",
            "the first step has no `unless`",
        );
        decode_error(
            "[{ pattern = \"<k> 1 </k>\" }, { unless = \"<k> 2 </k>\" }]",
            "pattern \"a\".steps[1].pattern",
            "missing required key",
        );
        decode_error(
            "[{ pattern = \"<k> 1 </k>\" }, { pattern = \"<k> 2 </k>\", unless = \" \" }]",
            "pattern \"a\".steps[1].unless",
            "must not be empty",
        );
        decode_error(
            "[{ pattern = \"<k> 1 </k>\" }, { pattern = \"<k> 2 </k>\", requires = \"true\" }]",
            "pattern \"a\".steps[1].requires",
            "unknown key",
        );
        let error = PatternList::decode(
            "[[pattern]]\nid = \"a\"\npattern = \"<k> 1 </k>\"\nsteps = [{ pattern = \"<k> 1 \
             </k>\" }]\n",
        )
        .unwrap_err();
        assert_eq!(error.key, "pattern \"a\".steps", "{error}");
        assert!(error.message.contains("keep one of the two"), "{error}");
        let error = PatternList::decode("[[pattern]]\nid = \"a\"\n").unwrap_err();
        assert_eq!(error.key, "pattern \"a\".pattern", "{error}");
        assert!(error.message.contains("`steps`"), "{error}");
    }

    #[test]
    fn a_chain_decodes_with_the_keys_a_pattern_has() {
        let list = PatternList::decode(
            "[[pattern]]\nid = \"a\"\nnote = \"n\"\nprograms = [\"add\"]\nsteps = [\n  { pattern \
             = \"<k> 1 </k>\" },\n  { pattern = \"<k> 2 </k>\", unless = \"<k> 3 </k>\" },\n]\n\n\
             [[pattern]]\nid = \"b\"\nexpect = \"no\"\nsteps = [{ pattern = \"<k> 1 </k>\" }, { \
             pattern = \"<k> 1 </k>\" }]\n",
        )
        .unwrap();
        let a = &list.patterns[0];
        assert_eq!(
            a.form,
            PatternForm::Chain(vec![
                StepText {
                    pattern: "<k> 1 </k>".into(),
                    unless: None,
                },
                StepText {
                    pattern: "<k> 2 </k>".into(),
                    unless: Some("<k> 3 </k>".into()),
                },
            ])
        );
        assert_eq!(a.single(), None);
        assert_eq!(a.programs, Some(vec!["add".to_owned()]));
        assert_eq!(a.note.as_deref(), Some("n"));
        assert_eq!(
            list.patterns[1].expect,
            Some(super::super::PatternExpect::No)
        );
        // `expect` beside `programs` is refused for a chain as for a pattern.
        let error = PatternList::decode(
            "[[pattern]]\nid = \"a\"\nexpect = \"no\"\nprograms = [\"add\"]\nsteps = [{ pattern \
             = \"<k> 1 </k>\" }, { pattern = \"<k> 1 </k>\" }]\n",
        )
        .unwrap_err();
        assert_eq!(error.key, "pattern \"a\".expect", "{error}");
    }

    #[test]
    fn a_chain_of_one_step_is_its_pattern() {
        let text = "<k> I:Int </k>\n  requires I >Int 5 ";
        let single = PatternList::decode(&format!(
            "[[pattern]]\nid = \"a\"\nnote = \"n\"\nprograms = [\"add\"]\npattern = {text:?}\n"
        ))
        .unwrap();
        let chain = PatternList::decode(&format!(
            "[[pattern]]\nid = \"a\"\nnote = \"n\"\nprograms = [\"add\"]\nsteps = [{{ pattern = \
             {text:?} }}]\n"
        ))
        .unwrap();
        assert_eq!(chain, single);
        assert_eq!(chain.patterns[0].single(), Some(text));
    }

    /// calc's lowering context and searcher definition, given to `body` on a thread with the
    /// command's stack.
    fn on_calc(body: impl FnOnce(&Lowering, &BackendDefinition) + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || {
                let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let (_, admitted) = crate::admit::admit_spec(&manifest);
                let (spec, _) = admitted.expect("calc is admitted");
                let main = &manifest.spec.main_module;
                let searcher = Searcher::new(&spec, main, manifest.budget).unwrap();
                let lowering = Lowering::new(&spec, main).unwrap();
                body(&lowering, searcher.definition());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    fn chain(steps: &[(&str, Option<&str>)]) -> Vec<StepText> {
        steps
            .iter()
            .map(|(pattern, unless)| StepText {
                pattern: (*pattern).to_owned(),
                unless: unless.map(str::to_owned),
            })
            .collect()
    }

    /// One admission of calc for every lowering check: the one-step pin, comments, `=>`, the
    /// carried variables of a real chain, sorts, part refusals and the chain digest.
    #[test]
    fn chains_lower_on_calc() {
        on_calc(|lowering, definition| {
            // A one-step chain is its pattern: the decoded entry is the single pattern's, so its
            // lowering and digest are too (the fixture pin of `result-three`).
            let list = PatternList::decode(
                "[[pattern]]\nid = \"result-three\"\nsteps = [{ pattern = \"<k> 3 </k>\" }]\n",
            )
            .unwrap();
            let single = lowering
                .lower(list.patterns[0].single().unwrap(), definition)
                .unwrap();
            assert_eq!(
                single.digest.to_string(),
                "a585d2cf629504e1272931036566d3324ffd48219377fa22ad71569f1c4800cb"
            );

            // A K comment in a part is layout: it lowers, to the same target and digest.
            for commented in [
                "<k> 3 /* the result */ </k>",
                "/* the result */\n<k> 3 </k>",
                "<k> 3 </k> // the result",
            ] {
                let lowered = lowering.lower(commented, definition).unwrap();
                assert_eq!(lowered.digest, single.digest, "{commented}");
            }

            // A `=>` keeps K's meaning: the part denotes its left side.
            let rewrite = lowering.lower("<k> 1 + 2 => 3 </k>", definition).unwrap();
            let left = lowering.lower("<k> 1 + 2 </k>", definition).unwrap();
            assert_eq!(rewrite.target, left.target, "{rewrite:?}");

            // Step 1's body binds I and J, step 2 names them in its requires; K is step 2's
            // own and `_` and the completed cells are generated: nothing else is carried.
            let sum = chain(&[
                ("<k> I:Int + J:Int ~> _ </k>", None),
                (
                    "<k> K:Int </k> requires K ==Int I +Int J",
                    Some("<k> I /* a later state */ </k> requires I ==Int J"),
                ),
            ]);
            let lowered = lowering.lower_chain(&sum, definition).unwrap();
            let ij = vec!["VarI:SortInt{}".to_owned(), "VarJ:SortInt{}".to_owned()];
            assert_eq!(names(&lowered.steps[0].imports), Vec::<String>::new());
            assert_eq!(names(&lowered.steps[0].exports), ij);
            assert_eq!(names(&lowered.steps[1].imports), ij);
            assert_eq!(names(&lowered.steps[1].exports), Vec::<String>::new());
            assert!(lowered.steps[0].unless.is_none());
            // The unless writes I without a sort, and its requires gives it sort Int.
            assert_eq!(
                names(&lowered.steps[1].unless.as_ref().unwrap().imports),
                ij
            );
            assert_eq!(lowered.steps[1].pattern.digest, {
                lowering
                    .lower("<k> K:Int </k> requires K ==Int I +Int J", definition)
                    .unwrap()
                    .digest
            });

            // `P:Int` in one part and an inferred sort in another name two variables.
            let message = lowering
                .lower_chain(
                    &chain(&[("<k> P:Int </k>", None), ("<k> P ~> _ </k>", None)]),
                    definition,
                )
                .unwrap_err();
            assert!(
                message.starts_with("the variable P has sort ") && message.contains("sort Int"),
                "{message}"
            );

            // A part's refusal names the part.
            let message = lowering
                .lower_chain(
                    &chain(&[("<k> 3 </k>", None), ("<k> 3 + </k>", None)]),
                    definition,
                )
                .unwrap_err();
            assert!(message.starts_with("step 2: "), "{message}");
            let message = lowering
                .lower_chain(
                    &chain(&[
                        ("<k> 3 </k>", None),
                        ("<k> 3 </k>", Some("<k> X => Y </k>")),
                    ]),
                    definition,
                )
                .unwrap_err();
            assert!(message.starts_with("step 2's unless: "), "{message}");

            // The digest is the parts' KORE: layout, comments, the id and the note are not in
            // it, a change of a part's KORE or a new unless moves it.
            let digest = |steps: &[(&str, Option<&str>)]| {
                lowering
                    .lower_chain(&chain(steps), definition)
                    .unwrap()
                    .digest
            };
            let base = digest(&[("<k> 1 + 2 ~> _ </k>", None), ("<k> 3 </k>", None)]);
            assert_eq!(
                base,
                digest(&[
                    ("  <k> 1 +\n 2 ~> _ </k>", None),
                    ("<k> 3 /* done */ </k>", None)
                ])
            );
            let listed = |id: &str, note: &str| {
                let list = PatternList::decode(&format!(
                    "[[pattern]]\nid = {id:?}\nnote = {note:?}\nsteps = [{{ pattern = \"<k> 1 + \
                     2 ~> _ </k>\" }}, {{ pattern = \"<k> 3 </k>\" }}]\n"
                ))
                .unwrap();
                let PatternForm::Chain(steps) = &list.patterns[0].form else {
                    panic!("a chain")
                };
                lowering.lower_chain(steps, definition).unwrap().digest
            };
            assert_eq!(listed("a", "one"), base);
            assert_eq!(listed("b", "two"), base);
            assert_ne!(
                digest(&[("<k> 1 + 2 ~> _ </k>", None), ("<k> 4 </k>", None)]),
                base
            );
            assert_ne!(
                digest(&[
                    ("<k> 1 + 2 ~> _ </k>", None),
                    ("<k> 3 </k>", Some("<k> 4 </k>"))
                ]),
                base
            );
            // The single pattern of a part has another domain: a chain digest never equals one.
            assert_ne!(base, left.digest);
        });
    }
}
