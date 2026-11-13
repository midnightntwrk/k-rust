//! The scope every coverage family shares: which authored sentences are no obligation of any
//! family, and why (module documentation of [`crate::coverage`], "Families").
//!
//! An obligation is derived from the definition alone, so the scope is a function of the
//! definition and the front end's marks, never of what a program ran. A sentence is out of the
//! scope, in this order, when it is:
//!
//! - [`Excluded::OutOfScope`]: a simplification, a `symbolic` equation or a `#Ceil` equation,
//!   which states a fact of the definition's functions that the definition means the same
//!   without, so no step computes it;
//! - [`Excluded::NoCoverageSignal`]: a rule none of whose compiled ids k-rust's run coverage can
//!   name, so no program can be shown to reach it;
//! - [`Excluded::ClaimHelper`]: an equation of a function only claims apply
//!   ([`FlowManifest::is_claim_helper`]). No initializer, program production or sentence a run
//!   can take applies it, so a run reaches it only through an input that applies it, and an
//!   edit of it changes no step of any other run; the claims it serves are what tell its
//!   equations apart, and a proof of the claims checks them. Such a sentence is no obligation
//!   whatever the programs did: an item that became one because a program applied it would make
//!   the universe depend on the corpus;
//! - [`Excluded::Invariant`]: an equation of a function only the manifest's invariants reach
//!   (`[[coverage.invariant]]`, "Invariant-only functions" below). The invariant is read off a
//!   run's states by the argued items' checks, never applied by a step of a run, so its
//!   equations and those of the functions only it applies are no behaviour of the definition a
//!   program exercises, and an edit of them changes no step of any run that does not apply them
//!   through an input. As for a claim helper, such a sentence is no obligation whatever the
//!   programs did;
//! - [`Excluded::DeclaredEnd`]: an equation of a function only the definition's declared ends
//!   reach ([`FlowManifest::end_functions`], reached as the invariants' functions are, below). A
//!   declared end's function is applied to a run's last state by the front end that reads the
//!   class (`crate::evidence`, "Declared ends"), never by a step of a run, and the slots compare
//!   final configurations, not classes: an edit of such an equation changes no step and no end
//!   any slot compares, so no program can tell it apart, and it is no obligation whatever the
//!   programs did.
//!
//! # Invariant-only functions
//!
//! The reach is that of the compiled equations (kink-native
//! [`EquationReach`](kink_native::consistency::EquationReach), the relation the consistency gate
//! reads backwards): evaluating an application of a symbol can apply every symbol its equations
//! and lemmas apply in their sides and conditions, transitively, an overload family linked both
//! ways, and whatever an equation indexed at no symbol applies. A run of a result record can
//! evaluate everything that reach gives from `R`, the symbols:
//!
//! - every rewrite rule of the compiled definition applies in its sides and conditions (the
//!   authored rules, and the heating, cooling and stream rules the compile generates);
//! - of the initialization: `initGeneratedTopCell`, which every initial configuration applies, and
//!   every symbol the `configuration` sentences apply;
//! - of every production a program text can write: the labelled productions of the syntax module
//!   the loader parses programs in and of every module it imports;
//! - of every macro such a production declares (`macro`, `macro-rec`, `alias`, `alias-rec`):
//!   every symbol its rules apply, transitively through the macros those rules apply. A macro is
//!   expanded before the run into its rule's right-hand side and has no equations, so the reach
//!   of its label gives nothing, while every program that writes it applies what its expansion
//!   applies;
//! - of the front end's functions of an observer that a run's record holds the answers of: the
//!   `[stop] when` function and the `[observe]` views, components, filters and log elements, as
//!   the front end names them (kink-campaign `StopOracle::functions`,
//!   `ObservationFunctions::functions`). They are evaluated in an observer, never in the
//!   definition being run, so taking them in only keeps more sentences obligations; a front end
//!   that does not name them leaves the reach of a run unknown, and no sentence is then
//!   invariant-only.
//!
//! The invariant-only symbols are those the reach gives from the resolved invariants' functions
//! and not from `R`, and a sentence is invariant-only when every compiled id it authored is an
//! equation or lemma indexed at one of them. A function the semantics also applies (one a rule's
//! condition calls) is in the reach of `R`, so it stays an obligation. An invariant the front end
//! does not resolve adds nothing (`coverage` refuses it later, `invariant-unresolved`). What a
//! program's input applies is not read, as for a claim helper: the universe is a function of the
//! definition, the front end's marks and the manifest's `[[coverage.invariant]]` tables.
//!
//! Every family reads this one predicate: the rules family gives the sentence the exclusion's
//! status; the requirements, syntax, field-value and syntax paths families read those statuses
//! (a path or a joint field value is reached only through a fired instance of a sentence in
//! scope); the rule windows family keeps only sentences in scope as nodes of its may-follow
//! graph; and the flips
//! family moves a derived flip that changes only sentences outside the scope to
//! `not_generated`, and reads only the occurrences in scope of every other flip
//! ([`crate::flips::scoped`]).

use super::{
    CLAIM_HELPER, DECLARED_END, INVARIANT, InvariantResolver, NO_COVERAGE_SIGNAL, OUT_OF_SCOPE,
};
use crate::{admit::AdmittedSpec, manifest::FlowManifest, results::no_coverage_signal};
use k_rust::{
    definition::{AttributeKey, Definition, Sentence},
    kast::Term,
    kompile::encode_kore_label,
};
use kink_native::consistency::{EquationReach, mentioned};
use kink_native::coverage::RuleAuthors;
use kink_patch::SentenceRef;
use std::collections::{BTreeMap, BTreeSet};

/// Why a sentence is outside the scope of every coverage family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Excluded {
    /// A simplification, `symbolic` or ceil equation ([`OUT_OF_SCOPE`]).
    OutOfScope,
    /// A rule k-rust's run coverage cannot name ([`NO_COVERAGE_SIGNAL`]), with why.
    NoCoverageSignal(&'static str),
    /// An equation of a function only claims apply ([`CLAIM_HELPER`]).
    ClaimHelper,
    /// An equation of a function only the manifest's invariants reach ([`INVARIANT`]).
    Invariant,
    /// An equation of a function only the definition's declared ends reach ([`DECLARED_END`]).
    DeclaredEnd,
}

impl Excluded {
    /// The rules family's status of a sentence so excluded, and the `reason` of a flip moved to
    /// `not_generated` for it.
    pub(crate) fn status(self) -> &'static str {
        match self {
            Self::OutOfScope => OUT_OF_SCOPE,
            Self::NoCoverageSignal(_) => NO_COVERAGE_SIGNAL,
            Self::ClaimHelper => CLAIM_HELPER,
            Self::Invariant => INVARIANT,
            Self::DeclaredEnd => DECLARED_END,
        }
    }

    /// Why the sentence is no obligation, as a rules item's `reason` states it.
    pub(crate) fn reason(self) -> &'static str {
        match self {
            Self::OutOfScope => {
                "a simplification, symbolic or ceil equation states a fact of the definition's \
                 functions, which the definition means the same without: no step computes it"
            }
            Self::NoCoverageSignal(reason) => reason,
            Self::ClaimHelper => {
                "an equation of a function only claims apply: no run of the definition reaches it \
                 except through an input that applies it, and a proof of the claims it serves \
                 checks it"
            }
            Self::Invariant => {
                "an equation of a function only the manifest's invariants reach: no run of the \
                 definition applies it except through an input that applies it, since an \
                 invariant is read off a run's states, never applied by a step"
            }
            Self::DeclaredEnd => {
                "an equation of a function only the definition's declared ends reach: a declared \
                 end's function is applied to a run's last state to read its class, never by a \
                 step, and the slots compare final configurations, so no program can tell an \
                 edit of it apart"
            }
        }
    }
}

/// The scope of a specification under a manifest's front-end marks.
pub(crate) struct Scope<'m> {
    no_signal: BTreeMap<SentenceRef, &'static str>,
    manifest: &'m FlowManifest,
    /// The authored sentences only the manifest's invariants reach (module documentation,
    /// "Invariant-only functions").
    invariant_only: BTreeSet<SentenceRef>,
    /// The authored sentences only the definition's declared ends reach ([`Excluded::DeclaredEnd`]).
    end_only: BTreeSet<SentenceRef>,
    /// The reach of the compiled equations, where the input backend's definition was selected.
    reach: Option<EquationReach>,
}

impl<'m> Scope<'m> {
    /// The scope of `spec` with `manifest`'s claim helpers, and its `[[coverage.invariant]]`
    /// tables as `invariants` resolves them (`None`: the front end resolves none, and no sentence
    /// is invariant-only).
    pub(crate) fn of(
        spec: &AdmittedSpec,
        manifest: &'m FlowManifest,
        invariants: Option<&(dyn InvariantResolver + Sync)>,
    ) -> Self {
        let reach = spec
            .definition
            .as_ref()
            .ok()
            .map(|definition| EquationReach::of(definition));
        let invariant_only = reach
            .as_ref()
            .zip(invariants)
            .map(|(reach, resolver)| invariant_only(spec, manifest, reach, resolver))
            .unwrap_or_default();
        let end_only = reach
            .as_ref()
            .map(|reach| only_reached_from(spec, manifest, reach, manifest.end_functions.clone()))
            .unwrap_or_default();
        Self {
            no_signal: no_coverage_signal(spec),
            manifest,
            invariant_only,
            end_only,
            reach,
        }
    }

    /// Every symbol evaluating an application of a symbol of `seeds` can apply (kink-native
    /// [`EquationReach::closure`]), `seeds` included; `None` where the input backend's definition
    /// could not be selected.
    pub(crate) fn closure_of(&self, seeds: &BTreeSet<String>) -> Option<BTreeSet<String>> {
        Some(self.reach.as_ref()?.closure(seeds.iter().cloned()))
    }

    /// Why the authored `sentence` at `at` is outside the scope, in the order out-of-scope,
    /// no-coverage-signal, claim-helper, invariant; `None` where it is in scope. Only a rule can
    /// be excluded.
    pub(crate) fn excludes(&self, at: &SentenceRef, sentence: &Sentence) -> Option<Excluded> {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            return None;
        };
        if attributes.has(AttributeKey::Simplification)
            || attributes.has(AttributeKey::Symbolic)
            || ceil_left_side(body)
        {
            Some(Excluded::OutOfScope)
        } else if let Some(reason) = self.no_signal.get(at) {
            Some(Excluded::NoCoverageSignal(reason))
        } else if attributes
            .string(AttributeKey::Label)
            .is_some_and(|label| self.manifest.is_claim_helper(&at.module, label))
        {
            Some(Excluded::ClaimHelper)
        } else if self.invariant_only.contains(at) {
            Some(Excluded::Invariant)
        } else if self.end_only.contains(at) {
            Some(Excluded::DeclaredEnd)
        } else {
            None
        }
    }

    /// [`Self::excludes`] of the baseline sentence of `spec` at `at`; `None` where it is in
    /// scope or `spec` has no sentence there.
    pub(crate) fn excludes_at(&self, spec: &AdmittedSpec, at: &SentenceRef) -> Option<Excluded> {
        self.excludes(at, spec.loaded.baseline.sentence(at)?)
    }
}

/// The authored sentences of `spec` only `manifest`'s invariants reach, as `resolver` resolves
/// them, over `reach` (module documentation, "Invariant-only functions"): none where no invariant
/// resolves, or where a front end's function of an observer is not named.
fn invariant_only(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    reach: &EquationReach,
    resolver: &(dyn InvariantResolver + Sync),
) -> BTreeSet<SentenceRef> {
    let functions = manifest
        .coverage
        .invariants
        .iter()
        .filter_map(|invariant| resolver.resolve(spec, invariant).ok())
        .map(|resolved| resolved.symbol)
        .collect::<BTreeSet<_>>();
    only_reached_from(spec, manifest, reach, functions)
}

/// The authored sentences of `spec` that only `functions` (KORE symbols) reach over `reach`, and
/// not a run of a result record (module documentation, "Invariant-only functions"): each such
/// sentence's compiled ids are all equations or lemmas indexed at a symbol of that difference.
/// None where `functions` is empty, or where a front end's function of an observer is not named.
fn only_reached_from(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    reach: &EquationReach,
    functions: BTreeSet<String>,
) -> BTreeSet<SentenceRef> {
    if functions.is_empty() {
        return BTreeSet::new();
    }
    let Some(run) = run_seeds(spec, manifest) else {
        return BTreeSet::new();
    };
    let run = reach.closure(run);
    let only = reach
        .closure(functions)
        .difference(&run)
        .cloned()
        .collect::<BTreeSet<_>>();
    let authors = RuleAuthors::of(&spec.compiled);
    spec.loaded
        .baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .filter(|(at, _)| {
            let mut ids = authors.ids_of(at).peekable();
            ids.peek().is_some()
                && ids.all(|id| {
                    reach
                        .head(id)
                        .flatten()
                        .is_some_and(|head| only.contains(head))
                })
        })
        .map(|(at, _)| at)
        .collect()
}

/// The symbols a run of a result record evaluates directly, `R` of the module documentation
/// ("Invariant-only functions"), before the reach closes them; `None` where a front end's
/// function of an observer is not named.
fn run_seeds(spec: &AdmittedSpec, manifest: &FlowManifest) -> Option<BTreeSet<String>> {
    let definition = spec.definition.as_ref().ok()?;
    let mut seeds = BTreeSet::from(["LblinitGeneratedTopCell".to_owned()]);
    for rule in definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
    {
        seeds.extend(mentioned(&rule.rule));
    }
    let source = spec.loaded.baseline.definition();
    for module in &source.modules {
        for sentence in &module.local_sentences {
            if let Sentence::Configuration { body, ensures, .. } = &**sentence {
                applied(body, &mut seeds);
                applied(ensures, &mut seeds);
            }
        }
    }
    let mut written = BTreeSet::new();
    for module in imported(source, spec.loaded.syntax_module()) {
        for sentence in &module.local_sentences {
            if let Sentence::Production {
                label: Some(label), ..
            } = &**sentence
            {
                seeds.insert(encode_kore_label(label).name);
                written.insert(label.name.clone());
            }
        }
    }
    seeds.extend(expansions(source, written));
    if let Some(stop) = &manifest.stop_when.0 {
        seeds.extend(stop.functions()?);
    }
    if let Some(observe) = &manifest.observe_functions.0 {
        seeds.extend(observe.functions()?);
    }
    Some(seeds)
}

/// Every symbol, as a KORE symbol, the rules of the macros of `source` among the labels `written`
/// apply, and those of every macro such a rule applies, transitively (module documentation,
/// "Invariant-only functions"). A macro is a production with a macro-like attribute, and its rules
/// are those whose left-hand side it heads, or that carry such an attribute themselves; each rule
/// is read whole, its sides and conditions, which only adds seeds.
fn expansions(source: &Definition, written: BTreeSet<String>) -> BTreeSet<String> {
    let sentences = || {
        source
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
    };
    let macros = sentences()
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has_any(&AttributeKey::MACRO_LIKE) => Some(label.name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut rules = BTreeMap::<String, Vec<[&Term; 3]>>::new();
    for sentence in sentences() {
        if let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = &**sentence
            && let Some(head) = rule_head(body)
            && (macros.contains(head) || attributes.has_any(&AttributeKey::MACRO_LIKE))
        {
            rules
                .entry(head.to_owned())
                .or_default()
                .push([body, requires, ensures]);
        }
    }
    let mut seeds = BTreeSet::new();
    let mut expanded = BTreeSet::new();
    let mut pending = written
        .into_iter()
        .filter(|label| rules.contains_key(label))
        .collect::<Vec<_>>();
    while let Some(label) = pending.pop() {
        if !expanded.insert(label.clone()) {
            continue;
        }
        for term in rules.get(&label).into_iter().flatten().flatten() {
            term.visit_preorder(&mut |term| {
                if let Term::Apply { label, .. } | Term::InjectedLabel(label) = term {
                    seeds.insert(encode_kore_label(label).name);
                    if rules.contains_key(&label.name) && !expanded.contains(&label.name) {
                        pending.push(label.name.clone());
                    }
                }
            });
        }
    }
    seeds
}

/// The label heading the left-hand side of a rule's body: its top rewrite's left side, or the
/// body itself, through aliases and semantic casts.
fn rule_head(body: &Term) -> Option<&str> {
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left,
        body => body,
    };
    head(left)
}

/// The label heading `term`, through an alias and a semantic cast.
fn head(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::As { pattern, .. } => head(pattern),
        Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
            head(arguments.first()?)
        }
        Term::Apply { label, .. } => Some(&label.name),
        _ => None,
    }
}

/// Every symbol `term` applies, as KORE symbols.
fn applied(term: &Term, into: &mut BTreeSet<String>) {
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } | Term::InjectedLabel(label) = term {
            into.insert(encode_kore_label(label).name);
        }
    });
}

/// The module `name` of `definition` and every module it imports, transitively.
fn imported<'d>(
    definition: &'d Definition,
    name: &str,
) -> impl Iterator<Item = &'d k_rust::definition::FlatModule> {
    let mut seen = BTreeSet::new();
    let mut pending = vec![name.to_owned()];
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if let Some(module) = definition.modules.iter().find(|module| module.name == name) {
            pending.extend(module.imports.iter().map(|import| import.name.clone()));
        }
    }
    definition
        .modules
        .iter()
        .filter(move |module| seen.contains(&module.name))
}

/// Whether a rule's body rewrites a `#Ceil` application at its top.
fn ceil_left_side(body: &Term) -> bool {
    match body {
        Term::Annotated { term, .. } => ceil_left_side(term),
        Term::Rewrite { left, .. } => ceil_left_side(left),
        Term::Apply { label, .. } => label.name == "#Ceil",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// A claim helper is named by its module and its label, bare or qualified by that module,
    /// and matches a sentence of that module that writes its label either way; a sentence of
    /// another module does not, whether its label is bare or qualified by the helper's module.
    #[test]
    fn a_claim_helper_matches_its_label_bare_or_qualified() {
        let manifest = FlowManifest::decode(
            "[spec]\nentry = \"m.k\"\nmain_module = \"M\"\n[[program]]\nid = \"a\"\ntext = \"a\"\n",
            Path::new("corpus"),
        )
        .unwrap()
        .with_claim_helpers([
            ("M".to_owned(), "bare".to_owned()),
            ("M".to_owned(), "M.qualified".to_owned()),
        ]);
        for (module, label) in [
            ("M", "bare"),
            ("M", "M.bare"),
            ("M", "qualified"),
            ("M", "M.qualified"),
        ] {
            assert!(manifest.is_claim_helper(module, label), "{module} {label}");
        }
        assert!(!manifest.is_claim_helper("N", "bare"));
        assert!(!manifest.is_claim_helper("N", "M.bare"));
        assert!(!manifest.is_claim_helper("N", "M.qualified"));
        assert!(!manifest.is_claim_helper("M", "N.bare"));
        assert!(!manifest.is_claim_helper("M", "other"));
    }

    /// Each exclusion is its rules status, and a claim helper's reason says why it is no
    /// obligation.
    #[test]
    fn each_exclusion_names_its_rules_status() {
        assert_eq!(Excluded::OutOfScope.status(), OUT_OF_SCOPE);
        let silent = Excluded::NoCoverageSignal("compiles to no rule");
        assert_eq!(silent.status(), NO_COVERAGE_SIGNAL);
        assert_eq!(silent.reason(), "compiles to no rule");
        assert_eq!(Excluded::ClaimHelper.status(), CLAIM_HELPER);
        assert!(Excluded::ClaimHelper.reason().contains("only claims apply"));
        assert_eq!(Excluded::Invariant.status(), INVARIANT);
        assert!(
            Excluded::Invariant
                .reason()
                .contains("only the manifest's invariants reach")
        );
    }
}
