//! Observer targets: a client's deterministic [`Observer`] decides whether the steps of a case
//! reach the target (ARCHITECTURE 4.1, 9.2). Owner: FZ-10.
//!
//! Until the rewrite loop has a per-step hook (gap G-9), observers are fed after each case. An
//! observer case runs once, through `Backend::execute_observed` ([`Executor::run_observed`]),
//! under the same cancellation scope, per-case safety limit and work budget as every case. The
//! observed run answers the leaves `Backend::execute` would, in the same order, and adds, per
//! leaf, the committed transitions of its path (`branch`) and their observation events
//! (`ObservationEventOutput::Transition`, which carry the configuration each step leaves from).
//! The leaves are judged as every case's are; the observer then walks the same leaves' paths.
//! Observed execution carries two full configurations per step, so it runs only for an observer
//! target.
//!
//! The leaves' paths share their prefixes: under all paths every leaf reports its whole path
//! from the initial state. The paths are merged into a tree keyed by transition identity, and
//! the observer walks the tree: [`Observer::start`] at the root, [`Observer::step`] on every
//! edge, from one normalized configuration to the next (`walk_paths`), and
//! [`Observer::branch`] for each successor of a state with several. A leaf *reaches* the target
//! when some step on its path answered [`ObserverVerdict::Hit`].
//!
//! A `work-bound`, `timeout` or `cancelled` leaf holds the stopped, unnormalised state the
//! worklist held, not a reached configuration (`classify`'s cut-leaf contract, review 2 S1). The
//! observer is never shown that state, so the step into it gives no verdict: such a leaf reaches
//! only when a step before it, between normalized configurations, answered `Hit`, as a rule
//! target reaches such a leaf only from its `rewrites`, which leave the last step out. A leaf
//! whose state is not shown for this reason is not a configuration the observer missed: the
//! leaf takes its halt's class.
//!
//! The case is then classed by [`crate::exec::classify`] like every other target: a hit needs a
//! reaching leaf that is clean (ARCHITECTURE 5.2) and, under `run-to-completion`, a natural end,
//! and a reaching leaf that is not clean is never a `miss`. A configuration of the tree that the
//! observer cannot be shown (its transition has no observation event, or it does not decode)
//! may lead to the target, so the case is then `unsupported` unless some leaf is a hit.
//!
//! An observer hit rests on one leaf's own path, and the facts of a path (chosen values,
//! contradicted claims) are that leaf's diagnostics. So the refusal of hits on run facts that no
//! leaf carries (D18), which exists for coverage hits that cannot be attributed to a leaf, is
//! not needed here; `classify`'s rule that such facts turn `miss` and `stuck` into
//! `unsupported` still applies.

use std::{any::Any, collections::BTreeSet, fmt, rc::Rc, sync::Arc};

use k_rust::{
    backend::{
        CancellationToken, CompiledRuleKind, ExecutionLeaf, ObservationEventOutput,
        TransitionIdOutput,
    },
    k_rust_backend::transition::ObservationOptions,
    kast::identifier::encode_label,
    kore::{ast::Pattern as KorePattern, codec, walk},
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{HitSite, Judgement, Resolved, ResolvedTarget};
use crate::{
    error::{CampaignError, TargetProblem},
    exec::{self, Abort, CaseRequestShape, CaseResult, DeterminismBreak, Executor, OutcomeClass},
    report::EngineDefect,
};

#[cfg(test)]
#[path = "observer_tests.rs"]
mod tests;

/// A client's acceptor over the steps of a run (ARCHITECTURE 9.2), for example kink's step
/// events and sequence-pattern monitor.
///
/// The methods take `&self`, and everything an observer learns about a path lives in
/// [`Self::State`]: one observer is shared by every case of a campaign, by its confirmations and
/// by every clone of the specification, so verdicts must be a function of the configurations
/// shown since [`Self::start`]. Confirmation re-runs the observer on a fresh executor
/// (ARCHITECTURE 7, R-24); interior mutability that changes verdicts breaks the determinism
/// contract (ARCHITECTURE 5.4).
///
/// A hit still needs its leaf to end cleanly. Observers are fed after the run, which has no
/// early stop for them, so a path the observer accepted keeps running: if it is then cut by a
/// bound, the case is `unsupported` without `run-to-completion` (a target-reaching leaf that is
/// not clean, D18) and `reached-unfinished` with it, never a hit. An observer cannot accept the
/// initial configuration: a case without a step never calls [`Self::step`].
pub trait Observer {
    /// The observer's state on one path.
    type State: Clone;

    /// The state at the initial configuration of a case.
    fn start(&self) -> Self::State;

    /// The state of one successor of a configuration that has several, derived from the state
    /// at that configuration. Called once for every successor, in the backend's order, before
    /// any step of that successor's path, whether or not that path can be shown.
    fn branch(&self, state: &Self::State) -> Self::State;

    /// Advance over one committed rewrite step from `pre` to `post`. After a
    /// [`ObserverVerdict::Hit`] the path has reached the target, and the observer is not called
    /// again on that path or its successors.
    fn step(
        &self,
        state: &mut Self::State,
        pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict;
}

/// What an observer says about one step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ObserverVerdict {
    /// The path has reached the target.
    Hit,
    /// The path is closer to acceptance (larger is closer, for example the number of monitor
    /// events matched); a signal for directed proposers (ARCHITECTURE 6.2, 6.4), which do not
    /// read it yet.
    Progress(u32),
    /// Nothing to report.
    Nothing,
}

/// A configuration as an observer sees it: the KORE pattern the backend reports, after
/// k-rust's normalization, conjoined with its constraints when it has any (a case's concrete
/// configurations have none).
///
/// KORE is the definition's own external format, so the view does not depend on the backend's
/// internal terms, which carry no stability promise (`crates/k-rust/src/lib.rs`). The view is
/// k-rust's externalization: map and set elements come in k-rust's order, which the definition
/// does not fix, so an observer that reads element order depends on the k-rust revision, which
/// the report records.
#[derive(Clone, Debug, PartialEq)]
pub struct ConfigurationView {
    pattern: KorePattern,
}

impl ConfigurationView {
    /// The view of `pattern`.
    #[must_use]
    pub fn new(pattern: KorePattern) -> Self {
        Self { pattern }
    }

    /// The configuration's KORE pattern.
    #[must_use]
    pub fn pattern(&self) -> &KorePattern {
        &self.pattern
    }

    /// The first cell `<name>` of the configuration, in pre-order (the outermost, then the
    /// leftmost): the application of the cell's KORE symbol (`Lbl'-LT-'k'-GT-'` for `k`), whose
    /// arguments are the cell's contents.
    #[must_use]
    pub fn cell(&self, name: &str) -> Option<&KorePattern> {
        let symbol = encode_label(&format!("<{name}>"));
        let mut work = vec![&self.pattern];
        while let Some(pattern) = work.pop() {
            if let KorePattern::Application { symbol: head, .. } = pattern
                && head.name == symbol
            {
                return Some(pattern);
            }
            work.extend(walk::children(pattern).into_iter().rev());
        }
        None
    }
}

/// Whether `pattern` contains an application of the KORE symbol named `symbol` (`Lblcount` for
/// a production with `symbol(count)`).
#[must_use]
pub fn contains_symbol(pattern: &KorePattern, symbol: &str) -> bool {
    let mut work = vec![pattern];
    while let Some(pattern) = work.pop() {
        match pattern {
            KorePattern::Application { symbol: head, .. }
            | KorePattern::AssociativeApplication { symbol: head, .. }
                if head.name == symbol =>
            {
                return true;
            }
            _ => work.extend(walk::children(pattern)),
        }
    }
    false
}

/// [`Observer`] with its state type erased, so that a target can hold any observer.
trait ErasedObserver: Send + Sync {
    fn start(&self) -> Box<dyn Any>;
    fn branch(&self, state: &dyn Any) -> Box<dyn Any>;
    fn step(
        &self,
        state: &mut dyn Any,
        pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict;
}

const STATE_TYPE: &str = "an observer state is created by the same observer";

impl<O> ErasedObserver for O
where
    O: Observer + Send + Sync,
    O::State: 'static,
{
    fn start(&self) -> Box<dyn Any> {
        Box::new(Observer::start(self))
    }

    fn branch(&self, state: &dyn Any) -> Box<dyn Any> {
        let state = state.downcast_ref::<O::State>().expect(STATE_TYPE);
        Box::new(Observer::branch(self, state))
    }

    fn step(
        &self,
        state: &mut dyn Any,
        pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict {
        let state = state.downcast_mut::<O::State>().expect(STATE_TYPE);
        Observer::step(self, state, pre, post)
    }
}

/// The observer an [`ObserverTarget`] carries: a shared client object, absent in a target read
/// back from JSON. Two handles are equal when they hold the same observer or are both absent.
#[derive(Clone, Default)]
pub struct ObserverHandle(Option<Arc<dyn ErasedObserver>>);

impl ObserverHandle {
    /// A handle on `observer`.
    pub fn new<O>(observer: O) -> Self
    where
        O: Observer + Send + Sync + 'static,
        O::State: 'static,
    {
        Self(Some(Arc::new(observer)))
    }

    /// Whether the handle holds an observer.
    #[must_use]
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
}

impl fmt::Debug for ObserverHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(if self.is_present() {
            "ObserverHandle(present)"
        } else {
            "ObserverHandle(absent)"
        })
    }
}

impl PartialEq for ObserverHandle {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }
}

impl Eq for ObserverHandle {}

/// The observer target (ARCHITECTURE 4.1, 9.2): a client observer accepts some path of the
/// case.
///
/// Observers are library-only (findings OD-2), and the observer itself is not serialized: it is
/// identified by assertion, through [`Self::name`]. A target read back from JSON carries no
/// observer, and [`crate::Campaign::new`] refuses it. Two targets with the same name and
/// different observers have the same report identity but compare unequal.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct ObserverTarget {
    /// The observer's identity as the client states it, for example its name and version. It is
    /// the only part of the observer in the report's target digest and so in any cache key built
    /// from the report's identity (ARCHITECTURE 5.4, 9.3): the client must change it whenever the
    /// observer's verdicts can change. An empty or blank name is refused.
    pub name: String,
    /// The observer.
    #[serde(skip)]
    pub observer: ObserverHandle,
}

impl ObserverTarget {
    /// The target `name` accepted by `observer`.
    pub fn new<O>(name: impl Into<String>, observer: O) -> Self
    where
        O: Observer + Send + Sync + 'static,
        O::State: 'static,
    {
        Self {
            name: name.into(),
            observer: ObserverHandle::new(observer),
        }
    }
}

/// Resolve an observer target for `executor`'s definition: refuse a target without its observer
/// or with a blank name, and choose the observation filter.
///
/// Observation events are kept only for the definition's executable rewrite rules, so that the
/// observed run does not also encode a configuration pair for every equation it evaluates; when
/// the backend does not accept that filter, every event is kept and only transitions are read.
/// Under the filter a committed remainder transition has no event, so its path cannot be shown
/// and the case is `unsupported`; a concrete run commits no remainder, since a remainder beside
/// an applied rule needs an undecided condition.
///
/// # Errors
///
/// [`TargetProblem::Unsupported`] for a target without its observer or with a blank name;
/// [`CampaignError::Definition`] when the rule catalog is not available.
pub(super) fn resolve(
    target: &ObserverTarget,
    executor: &mut Executor,
) -> Result<Resolved, CampaignError> {
    if target.name.trim().is_empty() {
        return Err(CampaignError::Target(TargetProblem::Unsupported(
            "an observer target needs a name: it is the observer's identity in the report"
                .to_owned(),
        )));
    }
    if !target.observer.is_present() {
        return Err(CampaignError::Target(TargetProblem::Unsupported(format!(
            "the observer target `{}` carries no observer: an observer is a client object, which \
             a target read from JSON cannot hold",
            target.name
        ))));
    }
    let catalog =
        executor
            .backend_mut()
            .rule_catalog(None)
            .map_err(|error| CampaignError::Definition {
                message: format!("the rule catalog is not available: {error}"),
            })?;
    let rewrites: BTreeSet<String> = catalog
        .into_iter()
        .filter(|entry| entry.kind == CompiledRuleKind::Rewrite && entry.executable)
        .map(|entry| entry.id)
        .collect();
    let accepted = executor
        .backend_mut()
        .with_solver(None, |definition, _solver| {
            Ok::<_, CampaignError>(
                ObservationOptions::with_rules(definition, rewrites.iter().cloned()).is_ok(),
            )
        })?;
    Ok(Resolved::Observer {
        rules: accepted.then(|| rewrites.into_iter().collect()),
    })
}

impl ResolvedTarget {
    /// Whether this target is judged from observed execution ([`Self::run_and_judge`]).
    pub(crate) fn observes(&self) -> bool {
        matches!(self.resolved, Resolved::Observer { .. })
    }

    /// Run one case with `executor` and judge it: [`Executor::run`] with this target's matchers,
    /// then [`Self::judge`], or for an observer target [`Executor::run_observed`] and the
    /// observer's walk over the leaves' paths (module documentation). The engine's entry point
    /// for rule, pattern and observer targets.
    ///
    /// An observer case runs once, through `Backend::execute_observed`, under the same
    /// cancellation scope, per-case safety limit and work budget as every other case, so its
    /// [`CaseResult::work`] is that one run's.
    ///
    /// The observer is not walked over a case it cannot judge: a failed run is classed by its
    /// failure, and a case outside the determinism contract (ARCHITECTURE 5.4: the safety limit,
    /// a clock cut, a stack stop, an undecided solver answer, an allowance refusal) or whose
    /// `cancel` is cancelled by the time it is judged is classed with no leaf reaching the
    /// target, and lifted to `timeout` (a clock was involved) or `unsupported` unless that
    /// already gives one of those or `rejected`: never a hit or a `miss`, since a path such a
    /// stop cut, or whose facts were not decided, may hide a configuration the observer would
    /// accept.
    ///
    /// # Errors
    ///
    /// [`Abort`] for a failed solver prelude. The judgement is an [`EngineDefect`] as for
    /// [`Self::judge`], and when the observed leaves are not the judged result's.
    pub(crate) fn run_and_judge(
        &self,
        executor: &mut Executor,
        initial: &KorePattern,
        shape: &CaseRequestShape,
        cancel: Option<&CancellationToken>,
    ) -> Result<(CaseResult, Result<Judgement, EngineDefect>), Abort> {
        match &self.resolved {
            Resolved::Observer { rules } => {
                let (result, leaves) = executor.run_observed(
                    initial,
                    shape,
                    &self.matchers(),
                    cancel,
                    rules.clone(),
                )?;
                let judgement = self.judge_observed(&result, &leaves, cancel);
                Ok((result, judgement))
            }
            Resolved::Rule { .. } | Resolved::PatternFinal | Resolved::Differential => {
                let result = executor.run(initial, shape, &self.matchers(), cancel)?;
                let judgement = self.judge(&result);
                Ok((result, judgement))
            }
        }
    }

    /// Judge an observer case from its judged `result` and the raw observed `leaves` of the
    /// same run ([`Self::run_and_judge`]).
    fn judge_observed(
        &self,
        result: &CaseResult,
        leaves: &[ExecutionLeaf],
        cancel: Option<&CancellationToken>,
    ) -> Result<Judgement, EngineDefect> {
        let run_to_completion = self.target.run_to_completion;
        if result.failure.is_some() {
            // A failed run is classed by its failure alone.
            return exec::classify(result, &[], run_to_completion).map(plain);
        }
        let cancelled = cancel.is_some_and(CancellationToken::is_cancelled);
        let breaks = result.determinism_breaks();
        if result.safety_limit_hit || !breaks.is_empty() || cancelled {
            let clock =
                result.safety_limit_hit || breaks.contains(&DeterminismBreak::Clock) || cancelled;
            return unobserved(result, run_to_completion, clock);
        }
        let super::TargetKind::Observer(target) = &self.target.kind else {
            return Err(defect("an observer resolution of another target kind"));
        };
        let Some(handle) = &target.observer.0 else {
            return Err(defect("an observer target resolved without its observer"));
        };
        if leaves.len() != result.leaves.len() {
            return Err(defect(&format!(
                "the observed run returned {} leaves where its judged result has {}",
                leaves.len(),
                result.leaves.len()
            )));
        }
        let paths = walk_paths(&**handle, leaves);
        let class = exec::classify(result, &paths.reached, run_to_completion)?;
        if class != OutcomeClass::Hit && paths.unobservable {
            // A configuration the observer could not be shown may lead to the target: never a
            // `miss`.
            return Ok(plain(OutcomeClass::Unsupported));
        }
        let hit_site = if class == OutcomeClass::Hit {
            let leaf = result
                .leaves
                .iter()
                .zip(&paths.reached)
                .position(|(leaf, reached)| {
                    *reached && leaf.is_clean() && (!run_to_completion || leaf.natural_end)
                });
            let Some(leaf) = leaf else {
                return Err(defect(
                    "a case classed `hit` has no clean leaf that reaches the target",
                ));
            };
            Some(HitSite::Leaf(leaf))
        } else {
            None
        };
        Ok(Judgement {
            class,
            hit_site,
            blocked: false,
        })
    }
}

/// The judgement of a class with no hit site and no blocked rule.
fn plain(class: OutcomeClass) -> Judgement {
    Judgement {
        class,
        hit_site: None,
        blocked: false,
    }
}

/// The class of a case the observer is not walked over ([`ResolvedTarget::run_and_judge`]):
/// [`exec::classify`] with no leaf reaching the target, lifted to `timeout` when a clock was
/// involved and to `unsupported` otherwise, since a leaf the observer was not shown may reach
/// the target.
fn unobserved(
    result: &CaseResult,
    run_to_completion: bool,
    clock: bool,
) -> Result<Judgement, EngineDefect> {
    let unreached = vec![false; result.leaves.len()];
    let class = exec::classify(result, &unreached, run_to_completion)?;
    Ok(plain(match class {
        OutcomeClass::Unsupported | OutcomeClass::Rejected | OutcomeClass::Timeout => class,
        _ if clock => OutcomeClass::Timeout,
        _ => OutcomeClass::Unsupported,
    }))
}

fn defect(description: &str) -> EngineDefect {
    EngineDefect {
        case: None,
        description: description.to_owned(),
    }
}

/// What the observer's walk found, per leaf of the observed result.
struct ObservedPaths {
    /// Some step on the leaf's path answered [`ObserverVerdict::Hit`].
    reached: Vec<bool>,
    /// Some configuration on a path, before any hit, could not be shown to the observer: no
    /// complete observation of a path through it, or it does not decode.
    unobservable: bool,
}

/// One edge of the path tree: a committed transition, and the node it leads to.
struct Edge<'a> {
    id: &'a TransitionIdOutput,
    child: usize,
}

/// One configuration of the path tree.
#[derive(Default)]
struct Node<'a> {
    /// The configuration after normalization: the `before` of the transitions that leave it,
    /// or the state of a leaf that ends here; `None` when only paths without complete
    /// observation events pass through it.
    configuration: Option<&'a Value>,
    /// The successors, in the order the leaves first reach them.
    edges: Vec<Edge<'a>>,
    /// The leaves that end here.
    leaves: Vec<usize>,
    /// A `work-bound`, `timeout` or `cancelled` leaf ends here: the node's state is the stopped,
    /// unnormalised state, which the observer is never shown (module documentation).
    stopped: bool,
}

/// The configuration each transition of `leaf`'s path leaves from, aligned with its `branch`,
/// when every committed transition has its observation event, in order. A path with missing
/// events gives none: with an identity repeated on the path, the events could not be placed.
fn befores(leaf: &ExecutionLeaf) -> Option<Vec<&Value>> {
    let transitions: Vec<_> = leaf
        .observations
        .iter()
        .filter_map(|event| match event {
            ObservationEventOutput::Transition { id, before, .. } => Some((id, before)),
            ObservationEventOutput::Evaluation { .. }
            | ObservationEventOutput::Uncommitted { .. } => None,
        })
        .collect();
    let complete = transitions.len() == leaf.branch.len()
        && transitions
            .iter()
            .zip(&leaf.branch)
            .all(|((id, _), committed)| *id == committed);
    complete.then(|| transitions.into_iter().map(|(_, before)| before).collect())
}

/// A position of the walk: a node of the path tree, the configuration it was entered from (none
/// at the root), and the observer's state there (none below a hit).
struct Frame {
    node: usize,
    pre: Option<Rc<ConfigurationView>>,
    state: Option<Box<dyn Any>>,
    hit: bool,
}

/// Merge the leaves' paths into a tree and walk it with `observer` (module documentation).
///
/// A node where a `work-bound`, `timeout` or `cancelled` leaf ends takes no configuration from
/// that leaf, and the walk does not step into it: its leaves reach only when a step above it
/// answered `Hit` (the cut-leaf contract of [`crate::exec::classify`]).
///
/// The tree's shape comes from every leaf's committed transition identities, which the backend
/// reports whatever the observation filter, so `branch` is called where the run branched. Its
/// configurations come from the observation events of the paths that have them all, and from
/// the leaves' states; a node without one cannot be shown, and its subtree stays unreached.
///
/// A step is shown from one normalized configuration to the next: a transition's `after` is
/// the rewrite's successor before its functions are evaluated, which denotes the same
/// configuration as the normalized one but is written differently (`3 +Int 1` for `4`), so the
/// observer is shown the configuration the next transition leaves from, or the leaf's state.
fn walk_paths(observer: &dyn ErasedObserver, leaves: &[ExecutionLeaf]) -> ObservedPaths {
    let mut reached = vec![false; leaves.len()];
    let mut unobservable = false;
    let mut nodes = vec![Node::default()];
    for (index, leaf) in leaves.iter().enumerate() {
        let befores = befores(leaf);
        let mut node = 0;
        for (position, id) in leaf.branch.iter().enumerate() {
            if let Some(befores) = &befores {
                nodes[node].configuration.get_or_insert(befores[position]);
            }
            node = if let Some(edge) = nodes[node].edges.iter().find(|edge| edge.id == id) {
                edge.child
            } else {
                let child = nodes.len();
                nodes.push(Node::default());
                nodes[node].edges.push(Edge { id, child });
                child
            };
        }
        if exec::stopped_state(leaf.reason) {
            nodes[node].stopped = true;
        } else {
            nodes[node].configuration.get_or_insert(&leaf.state);
        }
        nodes[node].leaves.push(index);
    }
    let mut work = vec![Frame {
        node: 0,
        pre: None,
        state: Some(observer.start()),
        hit: false,
    }];
    while let Some(Frame {
        node,
        pre,
        state,
        mut hit,
    }) = work.pop()
    {
        let current = &nodes[node];
        let mut view = None;
        let mut state = state;
        if !hit && current.stopped && current.edges.is_empty() {
            // The stopped state reached no configuration: the step into it gives no verdict,
            // and its leaves keep the reach of the steps before it (unreached here).
            for &leaf in &current.leaves {
                reached[leaf] = false;
            }
            continue;
        }
        if !hit && (pre.is_some() || !current.edges.is_empty()) {
            let decoded = current.configuration.map(codec::from_value);
            let Some(Ok(pattern)) = decoded else {
                // The observer cannot be shown this configuration: the leaves below stay
                // unreached.
                unobservable = true;
                continue;
            };
            let post = Rc::new(ConfigurationView::new(pattern));
            if let (Some(pre), Some(state)) = (&pre, state.as_deref_mut()) {
                hit = observer.step(state, pre, &post) == ObserverVerdict::Hit;
            }
            view = Some(post);
        }
        for &leaf in &current.leaves {
            reached[leaf] = hit;
        }
        if hit {
            work.extend(current.edges.iter().map(|edge| Frame {
                node: edge.child,
                pre: None,
                state: None,
                hit: true,
            }));
            continue;
        }
        let mut frames: Vec<Frame> = Vec::with_capacity(current.edges.len());
        if let [only] = current.edges.as_slice() {
            frames.push(Frame {
                node: only.child,
                pre: view,
                state,
                hit,
            });
        } else {
            for successor in &current.edges {
                frames.push(Frame {
                    node: successor.child,
                    pre: view.clone(),
                    state: state.as_deref().map(|state| observer.branch(state)),
                    hit,
                });
            }
        }
        // The first successor is walked first.
        work.extend(frames.into_iter().rev());
    }
    ObservedPaths {
        reached,
        unobservable,
    }
}
