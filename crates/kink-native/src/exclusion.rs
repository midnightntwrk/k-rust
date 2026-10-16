//! Exclusions: the conditions under which a run is no evidence for any comparison, whatever its
//! leaves say (re-pin R0b, `draft/tasks/repin-501f18b9`). Each makes the whole side of a test
//! Unknown, every oracle slot at once, so no other slot of the same test can still distinguish and
//! no outcome record is written for it. kink-campaign applies them when it judges a run
//! (`Runtime::judge`), on the baseline and on every mutant side, on a live run and on a stored
//! baseline run a `BaselineSession` reuses alike, before any evidence leaves the runner.
//!
//! - [`Exclusion::StackStop`]: the run counted a stop for lack of native stack (`stackStops`,
//!   finding A-06, k-rust KINK-06/5). A dismissed stop leaves no leaf trace: the leaf can be less
//!   simplified, or a step decided without a refinement, and whether a stop happens depends on the
//!   thread's stack and on other threads.
//! - [`Exclusion::LoadStackStop`]: the load of the side's definition counted a stop for lack of
//!   stack in its discharge of rewrite-rule definedness (`discharge_counts().stack_stops`) or in
//!   its critical-pair check (`value_claims().counts().condition_stack_stops`), read through
//!   `select_definition` on the backend that runs (finding A-08, KINK-06/4): the loaded rewrite
//!   theory and its value claims are then not a function of the definition. Budget stops are a
//!   function of the definition and only withdraw claims, so they exclude nothing.
//! - [`Exclusion::ContradictedClaim`]: a leaf is an undefined step that falsifies a trusted claim
//!   (re-pin decision 2, finding A-13): k-rust names a contradicted `total` claim
//!   (`contradictedTotal`), or a `Trivial` leaf's rule carries `preserves-definedness`. The
//!   definition is inconsistent there, and any verdict follows from an inconsistent theory. Under
//!   PathSet (the only modality kink requests) a `Trivial` leaf's rule id is its own rule; under
//!   StateSet it is witness metadata, and closing the case there needs k-rust's flag (KINK-18).
//! - [`Exclusion::ImplementationChosenHook`]: the definition references a hook for which k-rust
//!   chooses a value the definition leaves open (re-pin decision 1, findings D-10, E-10, E-11):
//!   kills are relative to the definition, not to k-rust's model of it. [`IMPLEMENTATION_CHOSEN_HOOKS`].
//! - [`Exclusion::AllowanceRefusal`]: a leaf reports a hook left unevaluated whose refusal reads
//!   the process's memory allowance (Execute promise exclusion, findings A-07, B-02, B-07): the
//!   result is a function of the host, not of the inputs a key names.
//!
//! A definition that holds an axiom rooted at a collection role symbol is not excluded as a whole,
//! but none of its collection terms is a terminal value (finding C-10,
//! [`DefinitionExclusions::collections_trusted`]).

use std::collections::BTreeSet;

use k_rust::backend::BackendDiagnosticOutput;
use k_rust::kore::{
    ast::{Attributes, Definition, Pattern, Sentence},
    walk,
};
use k_rust::names::KoreAttribute;
use k_rust_backend::{
    confluence::ViolationKind, definition::BackendDefinition, rule::TermIndex,
    term::CollectionMetadata,
};

use crate::execution::{AdaptedExecution, AdaptedLeaf, HaltClass};

/// The hooks for which k-rust 501f18b9 may compute a value the definition leaves open, exactly
/// the hooks for which its `implementation_chosen_in` (`k-rust-backend/src/builtin.rs`) can
/// return `Some`: the match arms (`MAP.keys_list`, `MAP.values`, `SET.set2list`, `MAP.choice`,
/// `SET.choice`), the six Float operations `float::mixed_destination` reads (`BinaryOperation::of`)
/// and `FLOAT.sign` (`float::nan_sign`); and `BYTES.string2bytes`, which leaves a code point above
/// 255 unevaluated but read as defined by `total` (finding E-11). Pinned against the k-rust source
/// by the kink-native test `implementation_chosen_hooks_are_k_rusts`.
pub const IMPLEMENTATION_CHOSEN_HOOKS: [&str; 13] = [
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.sign",
    "BYTES.string2bytes",
];

/// The hooks whose result size the process's memory allowance caps (k-rust `bytes.rs`, the only
/// readers of `Allowance::of_process`): a refusal of one depends on the host.
pub const ALLOWANCE_HOOKS: [&str; 3] = ["BYTES.padRight", "BYTES.padLeft", "BYTES.int2bytes"];

/// Why a run is no evidence for any comparison (see the module documentation).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Exclusion {
    StackStop,
    LoadStackStop,
    ContradictedClaim,
    ImplementationChosenHook,
    AllowanceRefusal,
}

impl Exclusion {
    /// The report name, which is also the reason a run document gives.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::StackStop => "stack-stop",
            Self::LoadStackStop => "load-stack-stop",
            Self::ContradictedClaim => "contradicted-claim",
            Self::ImplementationChosenHook => "implementation-chosen-hook",
            Self::AllowanceRefusal => "allowance-refusal",
        }
    }
}

/// A non-prelude sentence of a definition that references a symbol with an
/// [`IMPLEMENTATION_CHOSEN_HOOKS`] hook.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HookReference {
    /// The KORE module of the sentence.
    pub module: String,
    /// The sentence's `UNIQUE_ID`, label or source position, as far as it has one.
    pub sentence: String,
    pub symbol: String,
    pub hook: String,
}

/// What a loaded definition contributes to the exclusions of every run on it. Built once per
/// backend, from the compiled KORE the backend loaded and that backend's selected definition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DefinitionExclusions {
    /// `discharge_counts().stack_stops + value_claims().counts().condition_stack_stops` of the
    /// default module's load (the only module kink's requests name).
    pub load_stack_stops: usize,
    /// The non-prelude sentences that reference an implementation-chosen hook.
    pub implementation_chosen: Vec<HookReference>,
    /// The axioms rooted at a collection role symbol: the executable equations the load reports
    /// as `IndexedAt(Map | List | Set)` and the `simplification` or `symbolic` axioms it does not
    /// report (k-rust `collection_leaf_contract.rs`), each as its id, label or position.
    pub role_rooted_axioms: Vec<String>,
    /// The `UNIQUE_ID`s of the axioms written with `preserves-definedness`.
    pub preserves_definedness: BTreeSet<String>,
}

impl DefinitionExclusions {
    /// The exclusions of `kore`, loaded as `definition` (the definition the backend selected for
    /// the default module, after the load). Only the definition's own sentences count for the
    /// implementation-chosen census (see `authored`): not the prelude's, whose `Source` starts
    /// with one of `builtin_prefixes` (k-rust `CompileOptions::builtin_source_prefixes`), and not
    /// kompile's derived axioms. Every axiom counts for the role-rooted scan.
    #[must_use]
    pub fn of(
        kore: &Definition,
        definition: &BackendDefinition,
        builtin_prefixes: &[String],
    ) -> Self {
        let counts = definition.value_claims().counts();
        let load_stack_stops =
            definition.discharge_counts().stack_stops + counts.condition_stack_stops;
        let hooked = definition
            .symbols()
            .values()
            .filter_map(|symbol| {
                let hook = symbol.attributes.hook.as_deref()?;
                IMPLEMENTATION_CHOSEN_HOOKS
                    .contains(&hook)
                    .then(|| (symbol.name.to_string(), hook.to_owned()))
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let roles = definition
            .symbols()
            .values()
            .filter_map(|symbol| symbol.attributes.collection.as_ref())
            .flat_map(|metadata| {
                let symbols = match metadata {
                    CollectionMetadata::Map(map) => &map.symbols,
                    CollectionMetadata::List(list) | CollectionMetadata::Set(list) => &list.symbols,
                };
                [
                    symbols.unit.to_string(),
                    symbols.element.to_string(),
                    symbols.concat.to_string(),
                ]
            })
            .collect::<BTreeSet<_>>();
        let mut implementation_chosen = BTreeSet::new();
        let mut role_rooted_axioms = BTreeSet::new();
        let mut preserves_definedness = BTreeSet::new();
        for module in &kore.modules {
            for sentence in &module.sentences {
                let (attributes, patterns, declared) = match sentence {
                    Sentence::Axiom {
                        pattern,
                        attributes,
                        ..
                    }
                    | Sentence::Claim {
                        pattern,
                        attributes,
                        ..
                    } => (attributes, vec![&**pattern], None),
                    Sentence::AliasDeclaration {
                        left,
                        right,
                        attributes,
                        ..
                    } => (attributes, vec![&**left, &**right], None),
                    Sentence::SymbolDeclaration {
                        symbol, attributes, ..
                    } => (attributes, Vec::new(), Some(symbol.name.as_str())),
                    Sentence::Import { .. } | Sentence::SortDeclaration { .. } => continue,
                };
                if let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                {
                    if attributes.has(KoreAttribute::PreservesDefinedness)
                        && let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId)
                    {
                        preserves_definedness.insert(id.to_owned());
                    }
                    if (attributes.has(KoreAttribute::Simplification)
                        || attributes.has(KoreAttribute::Symbolic))
                        && axiom_head(pattern).is_some_and(|head| roles.contains(head))
                    {
                        role_rooted_axioms.insert(sentence_name(attributes));
                    }
                }
                if !authored(attributes, builtin_prefixes) {
                    continue;
                }
                let mut referenced = BTreeSet::new();
                if let Some(name) = declared {
                    referenced.insert(name.to_owned());
                }
                for pattern in patterns {
                    walk::for_each_post_order(pattern, |node| {
                        if let Pattern::Application { symbol, .. } = node
                            && hooked.contains_key(symbol.name.as_str())
                        {
                            referenced.insert(symbol.name.clone());
                        }
                    });
                }
                for symbol in referenced {
                    if let Some(hook) = hooked.get(&symbol) {
                        implementation_chosen.insert(HookReference {
                            module: module.name.clone(),
                            sentence: sentence_name(attributes),
                            symbol,
                            hook: hook.clone(),
                        });
                    }
                }
            }
        }
        for violation in definition.value_claims().violations() {
            if let ViolationKind::IndexedAt(TermIndex::Map | TermIndex::List | TermIndex::Set) =
                &violation.kind
            {
                role_rooted_axioms.insert(violation.rule.as_ref().map_or_else(
                    || "an unnamed equation".to_owned(),
                    |rule| rule.attributes.unique_id.clone(),
                ));
            }
        }
        Self {
            load_stack_stops,
            implementation_chosen: implementation_chosen.into_iter().collect(),
            role_rooted_axioms: role_rooted_axioms.into_iter().collect(),
            preserves_definedness,
        }
    }

    /// The exclusions of a compiled side loaded for `module` (its encoded KORE name) on this
    /// thread, as kink-campaign's runner computes them for a side it prepares.
    pub fn of_validated(side: &crate::ValidatedDefinition, module: &str) -> Result<Self, String> {
        let kore = k_rust::kore::parser::parse_definition(&side.artifacts().definition_kore)
            .map_err(|error| error.to_string())?;
        let mut backend = k_rust::backend::Backend::from_definition(
            kore.clone(),
            module,
            k_rust::backend::BackendOptions::default(),
        )
        .map_err(|error| error.to_string())?;
        let selected = backend
            .select_definition(None)
            .map_err(|error| error.to_string())?;
        Ok(Self::of(
            &kore,
            &selected,
            &side.compile_options().builtin_source_prefixes,
        ))
    }

    /// The exclusion every run on this definition has, if any: a load stack stop first, then an
    /// implementation-chosen hook.
    #[must_use]
    pub fn definition_exclusion(&self) -> Option<Exclusion> {
        if self.load_stack_stops > 0 {
            Some(Exclusion::LoadStackStop)
        } else if !self.implementation_chosen.is_empty() {
            Some(Exclusion::ImplementationChosenHook)
        } else {
            None
        }
    }

    /// Whether a collection term of this definition can be a terminal value: no axiom is rooted
    /// at a collection role symbol (KINK-05's collection denotation contract, finding C-10).
    #[must_use]
    pub fn collections_trusted(&self) -> bool {
        self.role_rooted_axioms.is_empty()
    }

    /// The exclusion of `execution`, a run on this definition, if any (see the module
    /// documentation): the definition's own, then a stack stop, a contradicted claim and an
    /// allowance refusal, in that order. A timed-out run is a timeout before it is anything else,
    /// and is not asked.
    #[must_use]
    pub fn run_exclusion(&self, execution: &AdaptedExecution) -> Option<Exclusion> {
        if let Some(exclusion) = self.definition_exclusion() {
            return Some(exclusion);
        }
        if execution.stack_stops() > 0 {
            return Some(Exclusion::StackStop);
        }
        let leaves = execution.leaves();
        if leaves.iter().any(|leaf| self.contradicts_a_claim(leaf)) {
            return Some(Exclusion::ContradictedClaim);
        }
        if leaves.iter().any(allowance_refusal) {
            return Some(Exclusion::AllowanceRefusal);
        }
        None
    }

    /// Whether `leaf` is an undefined step that falsifies a trusted claim: k-rust names a
    /// contradicted `total` claim, or the leaf is `Trivial` and its rule carries
    /// `preserves-definedness`.
    #[must_use]
    pub fn contradicts_a_claim(&self, leaf: &AdaptedLeaf) -> bool {
        leaf.contradicted_total.is_some()
            || (leaf.halt == HaltClass::Trivial
                && leaf
                    .undefined_rule
                    .as_ref()
                    .is_some_and(|rule| self.preserves_definedness.contains(&rule.id)))
    }
}

/// Whether `leaf` reports an allowance hook left unevaluated, on the leaf, a candidate or the
/// remainder.
fn allowance_refusal(leaf: &AdaptedLeaf) -> bool {
    leaf.diagnostics
        .iter()
        .chain(leaf.candidate_diagnostics.iter().flatten())
        .chain(&leaf.remainder_diagnostics)
        .any(|diagnostic| {
            matches!(diagnostic, BackendDiagnosticOutput::UnsupportedHookUnevaluated { hook, .. }
                if ALLOWANCE_HOOKS.contains(&hook.as_str()))
        })
}

/// Whether `state`, a test's initial state, applies a symbol with an implementation-chosen hook
/// of `definition`: such a run evaluates a value the definition leaves open, whatever the
/// definition's own sentences say.
#[must_use]
pub fn state_references_implementation_chosen(
    definition: &BackendDefinition,
    state: &Pattern,
) -> bool {
    let mut found = false;
    walk::for_each_post_order(state, |node| {
        if let Pattern::Application { symbol, .. } = node {
            found |= definition
                .symbols()
                .get(symbol.name.as_str())
                .and_then(|symbol| symbol.attributes.hook.as_deref())
                .is_some_and(|hook| IMPLEMENTATION_CHOSEN_HOOKS.contains(&hook));
        }
    });
    found
}

/// Whether a sentence with `attributes` is the definition's own rather than the prelude's or
/// kompile's: it has a `Source` that does not start with a builtin prefix, or it has no `Source`
/// but a `UNIQUE_ID` (a sentence a patch inserted carries no position attribute, but every rule
/// compiles with an id). A sentence with neither is an axiom kompile derived from a declaration
/// (the `functional` axiom of a `total` builtin symbol is written into the main module that way),
/// which references only what the declaration declares.
fn authored(attributes: &Attributes, builtin_prefixes: &[String]) -> bool {
    match string_attribute(attributes, KoreAttribute::Source) {
        Some(source) => {
            let source = source
                .strip_prefix("Source(")
                .and_then(|source| source.strip_suffix(')'))
                .unwrap_or(source);
            !builtin_prefixes
                .iter()
                .any(|prefix| source.starts_with(prefix.as_str()))
        }
        None => string_attribute(attributes, KoreAttribute::UniqueId).is_some(),
    }
}

fn string_attribute(attributes: &Attributes, attribute: KoreAttribute) -> Option<&str> {
    attributes.string(attribute).ok().flatten()
}

/// A sentence's `UNIQUE_ID`, else its label, else its source and location, else `"<unnamed>"`.
fn sentence_name(attributes: &Attributes) -> String {
    if let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId) {
        return id.to_owned();
    }
    if let Some(label) = string_attribute(attributes, KoreAttribute::Label) {
        return label.to_owned();
    }
    match (
        string_attribute(attributes, KoreAttribute::Source),
        string_attribute(attributes, KoreAttribute::Location),
    ) {
        (Some(source), Some(location)) => format!("{source} {location}"),
        (Some(source), None) => source.to_owned(),
        _ => "<unnamed>".to_owned(),
    }
}

/// The head symbol of the left-hand side of an equation or rewrite axiom
/// (`\implies(requires, \equals(lhs, rhs))`, `\equals(lhs, rhs)`, `\rewrites(lhs, rhs)`, under
/// binders), when it is an application.
fn axiom_head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Implies { right, .. } => axiom_head(right),
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => axiom_head(body),
        Pattern::Equals { left, .. } | Pattern::Rewrites { left, .. } => term_head(left),
        _ => None,
    }
}

fn term_head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
        Pattern::And { arguments, .. } => arguments.iter().find_map(|argument| match argument {
            Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        }),
        _ => None,
    }
}
