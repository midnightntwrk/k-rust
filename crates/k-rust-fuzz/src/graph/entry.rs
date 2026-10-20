//! The entry of a campaign and what is computed from it: the rules every case's first step may
//! apply, the reachable rules, the `statically-unreachable` warning and the self-check
//! (ARCHITECTURE 6.3).
//!
//! # One entry per campaign, from the hole template
//!
//! A hole value is data, but it can sit at a position the keys read: a configuration variable
//! that is the `<k>` cell, a literal at the head of the program, a value an initializer branches
//! on. The entry of one concrete configuration then says nothing about another case's: keyed on
//! the anchor `5`, `<k> $N:Int </k>` does not enable a rule for `0`, which the case `$N = 0`
//! applies at once. The entry is therefore computed once per campaign from the *hole template*,
//! the assembled configuration with each hole replaced by a variable of the hole's sort
//! ([`hole_template`]; a KORE-template program is already one). A variable keys nothing and
//! is filtered by its sort, so the template's entry covers every case's, and one entry serves
//! the warning and the self-check alike.
//!
//! # The state execution starts from
//!
//! The entry keys the state a case's execution starts from: [`RuleGraph::entry`] executes the
//! template with the campaign's request at depth 0 (Execution-mode simplification under the
//! case's iteration bound, module and definedness assumption) and keys every leaf. Keying the
//! assembled pattern itself would key the function `initGeneratedTopCell`, which enables every
//! rule; simplifying it otherwise (proof mode, no iteration bound) could evaluate further than a
//! case does and leave out a rule the case's matcher still tries.

use std::{collections::BTreeSet, fmt};

use k_rust::{
    backend::{Backend, BackendError, ExecuteRequest, ExecutionStrategy, ResultModalityOutput},
    k_rust_backend::{definition::BackendDefinition, term::Term},
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort, Variable as KoreVariable, VariableKind},
        codec,
    },
};

use super::{RuleGraph, Selection, shares_k};

/// The rules a campaign's initial configurations enable ([`RuleGraph::entry`]), tied to the
/// graph that computed it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Entry {
    /// [`RuleGraph::identity`] of the graph that computed it.
    graph: u64,
    nodes: BTreeSet<usize>,
    /// The configuration, or the definition, may hold more than one `<k>` cell: the
    /// `statically-unreachable` warning is withheld.
    withheld: bool,
}

/// An [`Entry`] was given to another graph than the one that computed it, such as the other
/// side's graph of a differential campaign.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ForeignEntry;

impl fmt::Display for ForeignEntry {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("the entry was computed by another rule graph")
    }
}

/// The self-check of one run's coverage `applied` ([`RuleGraph::unreachable_applied`]); each
/// list is sorted.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct AppliedCheck {
    /// Executable rewrite rules that are not reachable from the entry: engine defects, since
    /// the graph over-approximates every step.
    pub(crate) unreachable: Vec<String>,
    /// Ids that are neither an executable rewrite rule nor an equation of the graph's
    /// definition: a non-executable rule, or an id of another definition (a graph built on
    /// another route or module than the run). Engine defects.
    pub(crate) unknown: Vec<String>,
    /// Ids that name both a rewrite rule and an equation (the generated `UNKNOWN`, in caller
    /// KORE without ids): coverage cannot say which applied, so the check cannot judge them.
    pub(crate) ambiguous: Vec<String>,
}

impl AppliedCheck {
    /// Whether the check found nothing to report.
    pub(crate) fn is_clean(&self) -> bool {
        self.unreachable.is_empty() && self.unknown.is_empty() && self.ambiguous.is_empty()
    }

    /// One description per reported id, for `EngineDefect::description` (the ambiguous ids may
    /// be reported as warnings instead).
    pub(crate) fn descriptions(&self) -> Vec<String> {
        let unreachable = self
            .unreachable
            .iter()
            .map(|id| format!("rule {id} applied outside the rule graph"));
        let unknown = self.unknown.iter().map(|id| {
            format!(
                "applied id {id} is neither an executable rewrite rule nor an equation of the \
                 rule graph's definition"
            )
        });
        let ambiguous = self.ambiguous.iter().map(|id| {
            format!(
                "applied id {id} names both a rewrite rule and an equation; the rule graph \
                 cannot check it"
            )
        });
        unreachable.chain(unknown).chain(ambiguous).collect()
    }
}

/// `configuration` with the subterm at each hole's path replaced by an element variable of the
/// hole's KORE sort: the hole template. A path indexes the arguments of applications and of
/// `\and`/`\or` (the children `kore::walk::children` lists, which is how hole positions are
/// located; ARCHITECTURE 2.3). `None` when a path does not lead to a subterm through those,
/// in which case no template is known and the warning must be withheld.
pub(crate) fn hole_template(
    configuration: &KorePattern,
    holes: &[(Vec<usize>, KoreSort)],
) -> Option<KorePattern> {
    let mut template = configuration.clone();
    for (index, (path, sort)) in holes.iter().enumerate() {
        *subterm_mut(&mut template, path)? = KorePattern::Variable(KoreVariable {
            kind: VariableKind::Element,
            name: format!("VarFuzzHole{index}"),
            sort: sort.clone(),
        });
    }
    Some(template)
}

fn subterm_mut<'p>(pattern: &'p mut KorePattern, path: &[usize]) -> Option<&'p mut KorePattern> {
    let Some((step, rest)) = path.split_first() else {
        return Some(pattern);
    };
    let child = match pattern {
        KorePattern::Application { arguments, .. }
        | KorePattern::AssociativeApplication { arguments, .. }
        | KorePattern::And { arguments, .. }
        | KorePattern::Or { arguments, .. } => arguments.get_mut(*step)?,
        _ => return None,
    };
    subterm_mut(child, rest)
}

impl RuleGraph {
    /// The entry of a campaign: the rules enabled by the states its execution starts from.
    ///
    /// `request` is the campaign's case request ([`crate::exec`]'s request shape) whose
    /// `state` is the hole template ([`hole_template`]), so that the entry covers every case.
    /// The request is executed at depth 0 (`max_depth: Some(0)`, no work or breadth bound, every
    /// path, no stop rules, no coverage or trace), keeping its module, simplification bound and
    /// `assume_state_defined`, and every leaf's state is keyed. The run warms `backend`'s solver
    /// cache, so `backend` should be one no case uses (the graph's own), or the entry must be
    /// computed before the first case on every run of the campaign alike (ARCHITECTURE 5.4).
    ///
    /// # Errors
    ///
    /// When the template does not execute, or a leaf state does not decode or internalize. The
    /// caller then has no entry: it reports no warning and skips the self-check, and never
    /// aborts the campaign.
    pub(crate) fn entry(
        &self,
        backend: &mut Backend,
        request: ExecuteRequest,
    ) -> Result<Entry, BackendError> {
        let module = request.module_name.clone();
        let result = backend.execute(ExecuteRequest {
            max_depth: Some(0),
            max_work: None,
            max_breadth: None,
            strategy: ExecutionStrategy::All,
            stop_at_branch: false,
            cut_point_rules: Vec::new(),
            terminal_rules: Vec::new(),
            result_modality: ResultModalityOutput::PathSet,
            collect_coverage: false,
            collect_offered: false,
            trace: false,
            ..request
        })?;
        let states = result
            .leaves
            .iter()
            .map(|leaf| codec::from_value(&leaf.state))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| {
                BackendError::new(format!("an initial state does not decode: {error}"))
            })?;
        // A `\bottom` state denotes no configuration, so it enables nothing.
        let states: Vec<&KorePattern> = states
            .iter()
            .filter(|state| !matches!(state, KorePattern::Bottom { .. }))
            .collect();
        backend.with_solver_over(module.as_deref(), &states, |definition, _| {
            let terms = states
                .iter()
                .map(|state| {
                    definition
                        .admit_unverified(state, &[])
                        .internalize_pattern()
                        .map(|pattern| pattern.term)
                        .map_err(|error| {
                            BackendError::new(format!(
                                "an initial state does not internalize: {error}"
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(self.entry_of(definition, &terms))
        })
    }

    /// The rules the configurations `terms` of `definition` enable, as their states.
    pub(crate) fn entry_of(&self, definition: &BackendDefinition, terms: &[Term]) -> Entry {
        let withheld = self.shared_k || terms.iter().any(shares_k);
        let mut selection = Selection::new(definition, withheld);
        let mut nodes = BTreeSet::new();
        for term in terms {
            let subject = selection.subject(term);
            for target in &self.targets {
                if !nodes.contains(&target.node) && selection.enables(&subject, target) {
                    nodes.insert(target.node);
                }
            }
        }
        Entry {
            graph: self.identity,
            nodes,
            withheld,
        }
    }

    /// The ids of the rules `entry` holds.
    ///
    /// # Errors
    ///
    /// [`ForeignEntry`] when another graph computed `entry`.
    pub(crate) fn entry_rules(&self, entry: &Entry) -> Result<BTreeSet<String>, ForeignEntry> {
        self.own(entry)?;
        Ok(self.named(&entry.nodes))
    }

    /// The rules reachable from `entry`'s rules, those included.
    ///
    /// # Errors
    ///
    /// [`ForeignEntry`] when another graph computed `entry`.
    pub(crate) fn reachable(&self, entry: &Entry) -> Result<BTreeSet<String>, ForeignEntry> {
        Ok(self.named(&self.reachable_nodes(entry)?))
    }

    /// The `statically-unreachable` warning for `target` (ARCHITECTURE 6.3): `Some` when
    /// `target` is a rule of the graph that is not reachable from `entry`'s rules. Withheld
    /// (`None`) when more than one `<k>` cell may exist. A warning, never a refusal; `entry`
    /// must come from the hole template ([`Self::entry`]), not from one case.
    ///
    /// # Errors
    ///
    /// [`ForeignEntry`] when another graph computed `entry`.
    pub(crate) fn statically_unreachable(
        &self,
        entry: &Entry,
        target: &str,
    ) -> Result<Option<String>, ForeignEntry> {
        let reachable = self.reachable_nodes(entry)?;
        let Some(node) = self.nodes.get(target) else {
            return Ok(None);
        };
        Ok((!entry.withheld && !reachable.contains(node)).then(|| {
            format!(
                "statically-unreachable: rule {target} is not reachable in the rule graph from \
                 the rules the initial configuration enables"
            )
        }))
    }

    /// The self-check (ARCHITECTURE 6.3) of a run's coverage `applied` against the campaign's
    /// entry: the executable rewrite rules not reachable from it, the ids the definition does
    /// not know, and the ids shared by a rewrite rule and an equation. Equation ids are not
    /// checked: coverage records an equation wherever any evaluation used it.
    ///
    /// The check is as strong as coverage allows, a set of rules without their order, and it is
    /// weak where some reachable rule's right-hand side leaves a bare continuation in `<k>`
    /// (`<k> X => .K ... </k>` leaves `REST`, which keys nothing and enables every rule): every
    /// rule is then reachable. The graph's edges are checked step by step only by the tests, on
    /// traces.
    ///
    /// # Errors
    ///
    /// [`ForeignEntry`] when another graph computed `entry`.
    pub(crate) fn unreachable_applied<'a>(
        &self,
        entry: &Entry,
        applied: impl IntoIterator<Item = &'a str>,
    ) -> Result<AppliedCheck, ForeignEntry> {
        let reachable = self.reachable_nodes(entry)?;
        let applied: BTreeSet<&str> = applied.into_iter().collect();
        let mut check = AppliedCheck::default();
        for id in applied {
            let equation = self.equation_ids.contains(id);
            match (self.nodes.get(id), equation) {
                (Some(_), true) => check.ambiguous.push(id.to_owned()),
                (Some(node), false) => {
                    if !reachable.contains(node) {
                        check.unreachable.push(id.to_owned());
                    }
                }
                (None, true) => {}
                (None, false) => check.unknown.push(id.to_owned()),
            }
        }
        Ok(check)
    }

    fn own(&self, entry: &Entry) -> Result<(), ForeignEntry> {
        if entry.graph == self.identity {
            Ok(())
        } else {
            Err(ForeignEntry)
        }
    }

    fn reachable_nodes(&self, entry: &Entry) -> Result<BTreeSet<usize>, ForeignEntry> {
        self.own(entry)?;
        let mut reached = entry.nodes.clone();
        let mut pending: Vec<usize> = entry.nodes.iter().copied().collect();
        while let Some(node) = pending.pop() {
            for &next in &self.successors[node] {
                if reached.insert(next) {
                    pending.push(next);
                }
            }
        }
        Ok(reached)
    }
}
