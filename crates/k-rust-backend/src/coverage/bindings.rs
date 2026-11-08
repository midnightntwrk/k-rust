//! Bindings of fired instances: for each axiom, the symbols a request names that were the head
//! of a value an instance of it took as an operand, the values selected template binders were
//! bound to, and, for an axiom with several alternatives, the ones its instances took.
//!
//! A run that collects coverage and asks for bindings (`rewrite::ExecutionOptions::
//! collect_bindings`, a [`BindingCollection`]) reads, at every fired instance, the substitution
//! its match produced:
//! - a rewrite rule's instance is fired where the run committed to its successor, the site of
//!   `committed` (`rewrite::execute`'s `note_committed`): the substitution is read where the step
//!   built the successor (`rewrite::apply`'s `apply_rhs_alternative`), carried with the
//!   successor, and recorded only when its own normalization showed it defined, so a candidate
//!   the step rolled back, an undefined-step entry, a cut-point rule's proposed successor and a
//!   successor a stop or the work budget cut before its normalization finished record nothing;
//! - a term equation's instance (function, `anywhere`, overload or simplification) is fired
//!   where it gave a result, at the sites of `applied` that have its substitution: the
//!   simplifier's equation result (`simplify::equation_instance_result`, including a subject
//!   stated empty by a refuted binding obligation and a `\bottom` result), and the definedness
//!   decisions' one function-equation step that gave a value or decided an operand
//!   (`deferred`: D1 and D4).
//!
//! Ceil, predicate and `#Top` equations record nothing: they state a predicate about a term
//! (its definedness or its truth), not a step of its evaluation. A matched instance whose
//! condition was refuted, left undecided or stopped gave no result and records nothing.
//!
//! Nor do the equations that discharged a rewrite rule's definedness when the definition was
//! loaded (`ComputedRuleAttributes::discharged_by`), which a run reports to `applied` where it
//! builds a right-hand side alternative of the rule (`super::replay`). Their instances were
//! evaluated at load, on the rule's own terms: what such an instance took as an operand is a
//! subterm of the rule, an application the rule writes, which is part of what the rule's own
//! instance builds or inspects, or a variable of the rule, whose value in the run is an operand
//! of the rule's own instance and is recorded where that instance fires. No instance of the run
//! bound anything for them, so there is nothing of theirs to read.
//!
//! # Operand heads
//!
//! For each variable `x` the left-hand side binds (a variable of the axiom that is not among
//! the ones only its condition, right-hand side or `ensures` mention) and some other part of the
//! axiom reads, the head of `θ(x)` is read through injections: the symbol of the first
//! application below any number of `inj{_, _}`. It is recorded for the axiom when the
//! collection names it ([`BindingCollection::symbols`]). A variable the axiom reads is one that
//! occurs in its right-hand side, `requires` or `ensures`, twice in its left-hand side (the
//! match compares the two values), or under a concreteness attribute. Any other variable
//! (`ComputedRuleAttributes::unread_variables`, decided per axiom when it is loaded), such as
//! `_` in a cell the rule overwrites (`<c> _ => v </c>`), binds a value the step never uses: the
//! instance is the same whatever it holds, so the value was carried past or dropped, not taken
//! as an operand, and its head is not recorded. A domain value, a variable, a collection or a term-level
//! conjunction has no head and records nothing. A continuation variable binds a sequence, whose
//! head is the sequence's own constructor, so the rest of a program is never recorded unless
//! the request names that constructor.
//!
//! # Alternatives
//!
//! An axiom whose left-hand side is a disjunction, or a function equation with several
//! readings, is loaded as one rule per alternative, all under its `UNIQUE_ID`
//! (`RewriteRule::lhs_alternative`), and a rewrite rule with a disjunctive right-hand side
//! builds one successor per alternative of it. `applied` and `committed` name the axiom, so
//! they cannot tell which alternative an instance took; a fired instance of such an axiom
//! records the one it took ([`FiredAlternative`]): its rule's left-hand side alternative, and
//! the right-hand side alternative whose successor the run committed to. So what an alternative
//! inspects and builds is a fact of the run only where an instance took that alternative.
//!
//! # Template binder values
//!
//! A request selects binders as (axiom, variable, cap) ([`BindingCollection::binders`]): the
//! axiom by its `UNIQUE_ID` or label, the variable by its name as the definition writes it
//! (`term::names::rule_variable_definition_name`: without the marker of a rule's or an
//! equation's own variable and without the suffix of a renaming apart from a subject). A
//! binder is a variable of one axiom, whatever name selects the axiom, so it is reported under
//! the axiom's `UNIQUE_ID` ([`BinderValues::binder`]), once: where two selections name one
//! binder (by `UNIQUE_ID` and by label), it keeps the larger cap
//! ([`BindingCollection::selected_twice`] finds them, for a caller that refuses them). At a
//! fired instance of the axiom, an `Int` literal bound to the variable (through injections) is
//! inserted into the binder's set; any other value
//! (a term with variables or applications, or a value of another sort) sets
//! [`BinderValues::nonliteral`]. The set keeps the least `cap` values in the order of the
//! integers and [`BinderValues::truncated`] says whether a further value was left out, so what
//! is kept is a function of the full set, never of the order the instances came in.
//!
//! # Syntax paths
//!
//! A collection with a depth `D` above 1 ([`BindingCollection::depth`]) also records, per axiom,
//! the syntax paths of length `2..=D` its fired instances touched ([`RunBindings::paths`]). A
//! *path* of length `n` is a sequence `(P1, i1, P2, ..., Pn)` of symbols the collection names, each
//! `P(j+1)` the head, through injections, of argument `ij` (0-based) of `Pj`'s application. The
//! terms an instance touched are its left-hand side and its right-hand side alternative (for an
//! equation, its whole right-hand side) under its substitution, `Lθ` and `Rθ`, read as the depth-1
//! record reads them: the instance inspected the left-hand side's own positions, built the
//! right-hand side's, and took as an operand the value of each variable it reads (the same
//! unread-variable rule as the operand heads, decided per axiom when it is loaded). So a path is
//! touched when it starts at a position the depth-1 record counts as touched, a non-variable
//! position of the left-hand or right-hand side or the root of a read variable's value, and
//! descends through argument positions of `Lθ` or `Rθ`. Its first symbol is a position the instance
//! touched, and every later one lies below it within the path's length, so a value is walked to
//! `D - 1` positions below its root, and below the variable's position only.
//!
//! A position whose head is not a named symbol (a function application, a cell, a `K` sequence,
//! a collection, a domain value, a variable without a value) breaks a path: in the axiom's own
//! text a path may start again below it, at an application of a named symbol, since the instance
//! touched every position of its text; in a value no path starts below the value's root, since
//! the instance touched the root only, so the walk of a value stops there. A collection's elements
//! are thus items of their own, at depth 1, where the text writes them, and a value's are not
//! walked. A term-level conjunction in the text is read as both its conjuncts at its position.
//!
//! The paths are a function of the instance alone, so the set inherits the contract of the
//! operand heads: a union over the fired instances, independent of their order and multiplicity.
//! A path is recorded once per axiom, under its `UNIQUE_ID`, whatever alternative touched it.
//! Each length is read the same way at every `D`, so a collection at `D` holds every path of
//! length up to `D` that a collection at a smaller depth holds, and no other path of those
//! lengths.
//!
//! # Determinism and cost
//!
//! Every field is a union over the run's fired instances of a function of the instance, so it
//! depends on neither the multiplicity nor the order of the instances, and it is a deterministic
//! function of the same inputs as `applied` and `committed`. What a memo serves records as
//! `applied` does: a condition verdict the memo of verdicts serves (`simplify::ConditionMemo`,
//! which keeps only refuted and undecided verdicts, and none in an execution) records nothing
//! of the equations its decision applied, which recorded when the verdict was decided in the
//! same scope.
//!
//! The collection adds no evaluation: it reads the substitution the step's match already made
//! and evaluates, simplifies, matches and decides nothing. Per fired equation instance, and per
//! candidate a rewrite step builds (also one later rolled back, whose reading is dropped), it
//! costs one pass over the substitution: for each binding, two lookups in the axiom's variable
//! sets, a walk down injections, and one hash lookup of the head; for a selected binder, one
//! insert into its ordered set, O(log cap). That is at most linear in the bindings the run's
//! matches produced, so the collection's cost is bounded by a constant factor of the run's
//! matching work. With a depth `D` above 1, each such instance also walks its axiom's text, once
//! per alternative's first fired instance for the paths the text holds by itself, and, at each
//! occurrence of a read variable, the variable's value to `D - 1` positions below its root: at
//! most `a^(D-1)` positions of a value whose applications have at most `a` arguments, each
//! giving at most `D - 1` paths of at most `D` symbols, one hash insert each. Without a depth,
//! nothing of this is done. Asking for bindings changes no other field of the result.

use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    num::NonZeroUsize,
    sync::Arc,
};

use num_bigint::BigInt;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    definition::BackendDefinition,
    rule::{ComputedRuleAttributes, RewriteRule, RuleAttributes, RuleRhs},
    substitution::Substitution,
    term::{DomainKind, Name, Term, TermKind, names::rule_variable_definition_name},
};

/// What a run's binding collection records: the symbols whose occurrence as the head of an
/// operand is recorded, and the selected template binders with their caps.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BindingCollection {
    /// The symbols recorded as operand heads, by KORE name (`Lbl...`).
    pub symbols: BTreeSet<String>,
    /// The selected binders, each with the most values it keeps.
    pub binders: BTreeMap<BinderKey, usize>,
    /// The longest syntax path recorded ([`RunBindings::paths`], module documentation, "Syntax
    /// paths"); `None` records none, and so does a depth of 1, whose paths are the operand heads
    /// and the axioms' own symbols.
    pub depth: Option<NonZeroUsize>,
}

impl BindingCollection {
    /// The symbols `symbols`, with no binder selected and no path recorded.
    pub fn new<S: Into<String>>(symbols: impl IntoIterator<Item = S>) -> Self {
        Self {
            symbols: symbols.into_iter().map(Into::into).collect(),
            binders: BTreeMap::new(),
            depth: None,
        }
    }

    /// Record the syntax paths of length up to `depth` ([`RunBindings::paths`]).
    #[must_use]
    pub const fn with_depth(mut self, depth: NonZeroUsize) -> Self {
        self.depth = Some(depth);
        self
    }

    /// Select the binder `variable` of `axiom`, keeping its least `cap` values.
    #[must_use]
    pub fn with_binder(
        mut self,
        axiom: impl Into<String>,
        variable: impl Into<String>,
        cap: usize,
    ) -> Self {
        self.binders.insert(
            BinderKey {
                axiom: axiom.into(),
                variable: variable.into(),
            },
            cap,
        );
        self
    }

    /// Two selections that name one binder: one variable of an axiom of `definition`, the
    /// axiom named once by its `UNIQUE_ID` and once by its label, the first by `UNIQUE_ID`;
    /// `None` when every binder is selected once.
    #[must_use]
    pub fn selected_twice(&self, definition: &BackendDefinition) -> Option<(BinderKey, BinderKey)> {
        if self.binders.len() < 2 {
            return None;
        }
        let mut by_name = BTreeMap::<&str, Vec<&BinderKey>>::new();
        for binder in self.binders.keys() {
            by_name
                .entry(binder.axiom.as_str())
                .or_default()
                .push(binder);
        }
        for axiom in definition.classified_axioms() {
            let attributes = axiom.attributes();
            let by_id = by_name.get(attributes.unique_id.as_str());
            let by_label = attributes
                .label
                .as_deref()
                .filter(|label| *label != attributes.unique_id)
                .and_then(|label| by_name.get(label));
            let (Some(by_id), Some(by_label)) = (by_id, by_label) else {
                continue;
            };
            for first in by_id {
                if let Some(second) = by_label.iter().find(|b| b.variable == first.variable) {
                    return Some(((*first).clone(), (*second).clone()));
                }
            }
        }
        None
    }
}

/// A template binder: a variable of an axiom.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderKey {
    /// The axiom: in a selection by its `UNIQUE_ID` or its label, in what a run reports by its
    /// `UNIQUE_ID`.
    pub axiom: String,
    /// The variable, by its name as the definition writes it.
    pub variable: String,
}

/// What a run's fired instances bound ([`super::RunCoverage::bindings`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[non_exhaustive]
pub struct RunBindings {
    /// Per axiom with at least one recorded head, the named symbols that were the head of an
    /// operand of a fired instance of it, sorted by axiom id.
    pub operands: Vec<AxiomOperands>,
    /// Per selected binder bound at some fired instance, the values it took, sorted by binder
    /// (the axiom's `UNIQUE_ID`, then the variable).
    pub binders: Vec<BinderValues>,
    /// The alternatives of an axiom with several that some fired instance took, sorted
    /// ([`FiredAlternative`]).
    pub alternatives: Vec<FiredAlternative>,
    /// Per axiom with at least one, the syntax paths of length `2..=D` its fired instances
    /// touched, sorted by axiom id (module documentation, "Syntax paths"); present exactly when
    /// the collection set a depth `D` ([`BindingCollection::depth`]).
    pub paths: Option<Vec<AxiomPaths>>,
}

/// The syntax paths one axiom's fired instances touched ([`RunBindings::paths`]).
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct AxiomPaths {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The paths, each of length at least 2.
    pub paths: BTreeSet<SyntaxPath>,
}

/// A syntax path `(P1, i1, P2, ..., Pn)` (module documentation, "Syntax paths"): `symbols` are
/// `P1, ..., Pn` by KORE name, and `positions` the 0-based argument positions `i1, ..., i(n-1)`,
/// `symbols[j + 1]` being the head, through injections, of argument `positions[j]` of
/// `symbols[j]`'s application.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SyntaxPath {
    /// The symbols, outermost first.
    pub symbols: Vec<String>,
    /// The argument positions between them.
    pub positions: Vec<usize>,
}

/// An alternative of an axiom with several that a fired instance took: the axiom's rules share
/// its `UNIQUE_ID`, one per alternative of its left-hand side (`RewriteRule::lhs_alternative`,
/// a rewrite rule's disjunct or a function equation's reading), and a rewrite rule with a
/// disjunctive right-hand side builds one successor per alternative of it. The step of a
/// fired instance took one left-hand side alternative and, for a rewrite rule, built the one
/// successor the run committed to. An axiom with one alternative of each is never listed.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FiredAlternative {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The left-hand side alternative, by its position among the axiom's disjuncts or readings;
    /// `None` when the left-hand side has one.
    pub lhs: Option<usize>,
    /// The right-hand side alternative of a rewrite rule, by its position in the disjunction;
    /// `None` when the right-hand side is no disjunction, and for an equation, whose instance
    /// gives its whole right-hand side.
    pub rhs: Option<usize>,
}

/// The operand heads of one axiom's fired instances.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct AxiomOperands {
    /// The axiom's `UNIQUE_ID`.
    pub axiom: String,
    /// The named symbols that were the head of a value bound to a left-hand-side variable.
    pub symbols: BTreeSet<String>,
}

/// The values one selected binder took at the fired instances of its axiom.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub struct BinderValues {
    /// The binder: the axiom by its `UNIQUE_ID`, whatever name selected it, and the variable.
    pub binder: BinderKey,
    /// The `Int` literals bound to it: the least `cap` of them, ascending.
    pub values: Vec<BigInt>,
    /// Whether a further literal was bound that the cap left out.
    pub truncated: bool,
    /// Whether some fired instance bound it to a value that is no `Int` literal.
    pub nonliteral: bool,
}

/// What one fired instance bound, read from its substitution ([`read`]) and recorded once the
/// instance fired ([`note`]): the named heads of its operands and the values of its selected
/// binders, each by its position among its axiom's binders ([`Sink::binders_of`]).
#[derive(Debug)]
pub(crate) struct Fired {
    heads: Vec<Name>,
    values: Vec<(usize, Option<BigInt>)>,
    /// The alternative the instance took, `(lhs, rhs)`, when its axiom has several
    /// ([`FiredAlternative`]).
    alternative: Option<(Option<usize>, Option<usize>)>,
    /// The syntax paths the instance touched, under a collection with a depth above 1.
    paths: Vec<Path>,
    /// The alternative whose paths in its own text `paths` holds, `(lhs, rhs)`: set where its
    /// text was walked for them, the first time an instance of it was read before one fired.
    statics: Option<(Option<usize>, Option<usize>)>,
}

/// A syntax path as the collection keeps it ([`SyntaxPath`]).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Path {
    symbols: Box<[Name]>,
    positions: Box<[u32]>,
}

/// A fired instance's reading carried with a rewrite step's successor until the run commits to
/// it (`rewrite::AppliedRule`). It describes how the run was observed, not the step: equality
/// ignores it, so collecting bindings changes no compared field.
#[derive(Clone, Default)]
pub(crate) struct CarriedBindings(pub(crate) Option<Arc<Fired>>);

impl PartialEq for CarriedBindings {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for CarriedBindings {}

impl std::fmt::Debug for CarriedBindings {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(if self.0.is_some() { "Some(..)" } else { "None" })
    }
}

thread_local! {
    /// Whether the innermost open coverage collection collects bindings.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
    /// What it has collected.
    static SINK: RefCell<Option<Sink>> = const { RefCell::new(None) };
}

/// The bindings of one collection.
pub(super) struct Sink {
    symbols: FxHashSet<String>,
    /// The selected binders, as the collection names them, with their caps.
    binders: BTreeMap<BinderKey, usize>,
    /// The binders of an axiom, by `UNIQUE_ID`, resolved on its first fired instance: each
    /// variable a selection names for it once, with the largest cap a selection of it asks for.
    resolved: FxHashMap<String, Arc<[(String, usize)]>>,
    operands: FxHashMap<String, FxHashSet<Name>>,
    /// What each binder's instances bound so far, by the binder under its axiom's `UNIQUE_ID`.
    values: BTreeMap<BinderKey, Slot>,
    alternatives: BTreeSet<FiredAlternative>,
    /// The longest syntax path recorded; `None` below 2.
    depth: Option<NonZeroUsize>,
    /// The syntax paths of each axiom's fired instances, by `UNIQUE_ID`.
    paths: FxHashMap<String, FxHashSet<Path>>,
    /// The alternatives, `(UNIQUE_ID, lhs, rhs)`, whose paths in their own text are recorded.
    statics: FxHashSet<(String, Option<usize>, Option<usize>)>,
}

/// What a binder's instances bound so far.
#[derive(Default)]
struct Slot {
    values: BTreeSet<BigInt>,
    truncated: bool,
    nonliteral: bool,
}

impl Sink {
    pub(super) fn new(collection: BindingCollection) -> Self {
        Self {
            symbols: collection.symbols.into_iter().collect(),
            binders: collection.binders,
            resolved: FxHashMap::default(),
            operands: FxHashMap::default(),
            values: BTreeMap::new(),
            alternatives: BTreeSet::new(),
            depth: collection.depth,
            paths: FxHashMap::default(),
            statics: FxHashSet::default(),
        }
    }

    pub(super) fn finish(self) -> RunBindings {
        let mut operands = self
            .operands
            .into_iter()
            .filter(|(_, symbols)| !symbols.is_empty())
            .map(|(axiom, symbols)| AxiomOperands {
                axiom,
                symbols: symbols.iter().map(|symbol| symbol.to_string()).collect(),
            })
            .collect::<Vec<_>>();
        operands.sort_by(|left, right| left.axiom.cmp(&right.axiom));
        let binders = self
            .values
            .into_iter()
            .map(|(binder, slot)| BinderValues {
                binder,
                values: slot.values.into_iter().collect(),
                truncated: slot.truncated,
                nonliteral: slot.nonliteral,
            })
            .collect();
        let paths = self.depth.map(|_| {
            let mut paths = self
                .paths
                .into_iter()
                .filter(|(_, paths)| !paths.is_empty())
                .map(|(axiom, paths)| AxiomPaths {
                    axiom,
                    paths: paths
                        .into_iter()
                        .map(|path| SyntaxPath {
                            symbols: path
                                .symbols
                                .iter()
                                .map(|symbol| symbol.to_string())
                                .collect(),
                            positions: path
                                .positions
                                .iter()
                                .map(|position| *position as usize)
                                .collect(),
                        })
                        .collect(),
                })
                .collect::<Vec<_>>();
            paths.sort_by(|left, right| left.axiom.cmp(&right.axiom));
            paths
        });
        RunBindings {
            operands,
            binders,
            alternatives: self.alternatives.into_iter().collect(),
            paths,
        }
    }

    /// The depth at which the collection records syntax paths, when it is above 1.
    fn path_depth(&self) -> Option<usize> {
        self.depth.map(NonZeroUsize::get).filter(|depth| *depth > 1)
    }

    /// The binders of the axiom `attributes` names: each variable some selection names for it
    /// by its `UNIQUE_ID` or its label, once, with the largest cap asked for it; `None` when
    /// the collection selects no binder.
    fn binders_of(&mut self, attributes: &RuleAttributes) -> Option<Arc<[(String, usize)]>> {
        if self.binders.is_empty() {
            return None;
        }
        if let Some(binders) = self.resolved.get(&attributes.unique_id) {
            return Some(Arc::clone(binders));
        }
        let mut variables = BTreeMap::<&str, usize>::new();
        for (binder, cap) in &self.binders {
            if binder.axiom == attributes.unique_id
                || attributes.label.as_deref() == Some(binder.axiom.as_str())
            {
                let kept = variables.entry(binder.variable.as_str()).or_default();
                *kept = (*kept).max(*cap);
            }
        }
        let binders = variables
            .into_iter()
            .map(|(variable, cap)| (variable.to_owned(), cap))
            .collect::<Arc<[(String, usize)]>>();
        self.resolved
            .insert(attributes.unique_id.clone(), Arc::clone(&binders));
        Some(binders)
    }

    fn note(&mut self, axiom: &str, fired: &Fired) {
        if let Some((lhs, rhs)) = fired.alternative {
            let alternative = FiredAlternative {
                axiom: axiom.to_owned(),
                lhs,
                rhs,
            };
            if !self.alternatives.contains(&alternative) {
                self.alternatives.insert(alternative);
            }
        }
        if let Some((lhs, rhs)) = fired.statics {
            self.statics.insert((axiom.to_owned(), lhs, rhs));
        }
        if !fired.paths.is_empty() {
            let paths = if let Some(paths) = self.paths.get_mut(axiom) {
                paths
            } else {
                self.paths.entry(axiom.to_owned()).or_default()
            };
            for path in &fired.paths {
                if !paths.contains(path) {
                    paths.insert(path.clone());
                }
            }
        }
        if !fired.heads.is_empty() {
            let heads = if let Some(heads) = self.operands.get_mut(axiom) {
                heads
            } else {
                self.operands.entry(axiom.to_owned()).or_default()
            };
            for head in &fired.heads {
                if !heads.contains(head) {
                    heads.insert(Arc::clone(head));
                }
            }
        }
        if fired.values.is_empty() {
            return;
        }
        let Some(binders) = self.resolved.get(axiom).map(Arc::clone) else {
            return;
        };
        for (position, value) in &fired.values {
            let (variable, cap) = &binders[*position];
            let cap = *cap;
            let slot = self
                .values
                .entry(BinderKey {
                    axiom: axiom.to_owned(),
                    variable: variable.clone(),
                })
                .or_default();
            match value {
                None => slot.nonliteral = true,
                Some(value) => {
                    if slot.values.contains(value) {
                        continue;
                    }
                    slot.values.insert(value.clone());
                    if slot.values.len() > cap {
                        slot.values.pop_last();
                        slot.truncated = true;
                    }
                }
            }
        }
    }
}

/// Install `sink` as the innermost collection's bindings, returning the enclosing one's.
pub(super) fn replace(sink: Option<Sink>) -> Option<Sink> {
    RECORDING.set(sink.is_some());
    SINK.replace(sink)
}

/// Whether the innermost open collection collects bindings.
#[inline]
pub(super) fn recording() -> bool {
    RECORDING.get()
}

/// Read what an instance of `rule`, which built its right-hand side alternative `rhs` (`None`
/// for a right-hand side that is no disjunction, and for an equation), bound under
/// `substitution`: the named heads of its operands, the values of its selected binders, and
/// the alternative it took when the rule has several. `None` when it bound nothing the
/// collection records. The caller has checked that the open collection collects bindings.
pub(super) fn read(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    rhs: Option<usize>,
    substitution: &Substitution,
) -> Option<Fired> {
    let attributes = &rule.attributes;
    let computed = &rule.computed_attributes;
    SINK.with_borrow_mut(|sink| {
        let sink = sink.as_mut()?;
        let binders = sink.binders_of(attributes);
        let mut heads = Vec::new();
        let mut values = Vec::new();
        for (variable, value) in substitution {
            if !computed.variables.contains(variable)
                || computed.unbound_variables.contains(variable)
            {
                continue;
            }
            // A variable no other part of the rule reads was carried past or dropped, not
            // taken as an operand; a selected binder is read whatever the rule does with it.
            if !computed.unread_variables.contains(variable)
                && let Some(head) = head(value)
                && sink.symbols.contains(&**head)
            {
                heads.push(Arc::clone(head));
            }
            let Some(binders) = binders.as_deref().filter(|binders| !binders.is_empty()) else {
                continue;
            };
            let written = rule_variable_definition_name(&variable.name);
            if let Some(position) = binders.iter().position(|(name, _)| *name == written) {
                values.push((position, int_literal(definition, value)));
            }
        }
        let alternative = (rule.lhs_alternative.is_some() || rhs.is_some())
            .then_some((rule.lhs_alternative, rhs));
        let mut paths = Vec::new();
        let mut statics = None;
        if let Some(depth) = sink.path_depth() {
            let key = (attributes.unique_id.clone(), rule.lhs_alternative, rhs);
            let walk_statics = !sink.statics.contains(&key);
            let mut walk = PathWalk {
                symbols: &sink.symbols,
                depth,
                substitution,
                computed,
                statics: walk_statics,
                chain: Vec::new(),
                paths: FxHashSet::default(),
            };
            walk.text(&rule.lhs);
            match (&rule.rhs, rhs) {
                (RuleRhs::Term(term), _) => walk.text(term),
                (RuleRhs::Disjunction(alternatives), Some(index)) => {
                    if let Some(alternative) = alternatives.get(index) {
                        walk.text(&alternative.term);
                    }
                }
                // An equation's instance gives its whole right-hand side.
                (RuleRhs::Disjunction(alternatives), None) => {
                    for alternative in alternatives {
                        walk.text(&alternative.term);
                    }
                }
                (RuleRhs::Top | RuleRhs::Bottom | RuleRhs::Predicates(_), _) => {}
            }
            paths = walk.paths.into_iter().collect();
            statics = walk_statics.then_some((rule.lhs_alternative, rhs));
        }
        (!heads.is_empty()
            || !values.is_empty()
            || alternative.is_some()
            || !paths.is_empty()
            || statics.is_some())
        .then_some(Fired {
            heads,
            values,
            alternative,
            paths,
            statics,
        })
    })
}

/// The walk of an instance's touched terms for its syntax paths (module documentation, "Syntax
/// paths").
struct PathWalk<'a> {
    symbols: &'a FxHashSet<String>,
    /// The longest path, at least 2.
    depth: usize,
    substitution: &'a Substitution,
    computed: &'a ComputedRuleAttributes,
    /// Whether the paths that lie in the axiom's own text are recorded.
    statics: bool,
    /// The named applications above the current position along consecutive argument positions,
    /// outermost first, each with the argument the walk went down.
    chain: Vec<(Name, u32)>,
    paths: FxHashSet<Path>,
}

impl PathWalk<'_> {
    /// The named symbol `term` applies, through injections, and its arguments.
    fn named<'t>(&self, term: &'t Term) -> Option<(&'t Name, &'t [Term])> {
        match uninjected(term).kind() {
            TermKind::Application {
                symbol, arguments, ..
            } if self.symbols.contains(&*symbol.name) => Some((&symbol.name, arguments)),
            _ => None,
        }
    }

    /// Record the paths that end at an application of `symbol` below the chain, each starting
    /// at one of the chain's last `from..` positions or deeper: `from` of them at least, so that
    /// a path through a value starts at or above its root.
    fn end_at(&mut self, symbol: &Name, from: usize) {
        let longest = self.chain.len().min(self.depth - 1);
        for length in from.max(1)..=longest {
            let start = self.chain.len() - length;
            let part = &self.chain[start..];
            let mut symbols = part
                .iter()
                .map(|(symbol, _)| Arc::clone(symbol))
                .collect::<Vec<_>>();
            symbols.push(Arc::clone(symbol));
            let path = Path {
                symbols: symbols.into_boxed_slice(),
                positions: part.iter().map(|(_, position)| *position).collect(),
            };
            if !self.paths.contains(&path) {
                self.paths.insert(path);
            }
        }
    }

    /// Walk a position of the axiom's own text, the chain above it.
    fn text(&mut self, term: &Term) {
        match term.kind() {
            TermKind::Injection { term: inner, .. } => self.text(inner),
            TermKind::And(left, right) => {
                self.text(left);
                self.text(right);
            }
            TermKind::Variable(variable) => {
                if self.computed.variables.contains(variable)
                    && !self.computed.unbound_variables.contains(variable)
                    && !self.computed.unread_variables.contains(variable)
                    && let Some(value) = self.substitution.get(variable)
                {
                    self.value(value, 0);
                }
            }
            TermKind::Application {
                symbol, arguments, ..
            } if self.symbols.contains(&*symbol.name) => {
                if self.statics {
                    self.end_at(&symbol.name, 1);
                }
                for (position, argument) in arguments.iter().enumerate() {
                    self.chain.push((
                        Arc::clone(&symbol.name),
                        u32::try_from(position).unwrap_or(u32::MAX),
                    ));
                    self.text(argument);
                    self.chain.pop();
                }
            }
            // A position no named symbol heads breaks the paths through it; its subterms are
            // positions of the text, where paths start again.
            _ => {
                let chain = std::mem::take(&mut self.chain);
                visit_subterms(term, &mut |subterm| self.text(subterm));
                self.chain = chain;
            }
        }
    }

    /// Walk a position of a read variable's value `inside` positions below its root, the chain
    /// above it: a path through it starts at or above the root.
    fn value(&mut self, term: &Term, inside: usize) {
        let Some((symbol, arguments)) = self.named(term) else {
            return;
        };
        self.end_at(symbol, inside);
        // A path through an argument holds the root, this position and the argument.
        if inside + 2 > self.depth {
            return;
        }
        for (position, argument) in arguments.iter().enumerate() {
            self.chain.push((
                Arc::clone(symbol),
                u32::try_from(position).unwrap_or(u32::MAX),
            ));
            self.value(argument, inside + 1);
            self.chain.pop();
        }
    }
}

/// Call `visit` on each immediate subterm of `term`: an application's arguments, a conjunction's
/// conjuncts, an injection's term, a collection's elements, keys, values and rest.
fn visit_subterms(term: &Term, visit: &mut impl FnMut(&Term)) {
    match term.kind() {
        TermKind::Application { arguments, .. } => arguments.iter().for_each(visit),
        TermKind::And(left, right) => {
            visit(left);
            visit(right);
        }
        TermKind::Injection { term, .. } => visit(term),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                visit(key);
                visit(value);
            }
            rest.iter().for_each(visit);
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().for_each(&mut *visit);
            if let Some((middle, tails)) = rest {
                visit(middle);
                tails.iter().for_each(visit);
            }
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().for_each(&mut *visit);
            rest.iter().for_each(visit);
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
}

/// The term below `term`'s injections.
fn uninjected(mut term: &Term) -> &Term {
    while let TermKind::Injection { term: inner, .. } = term.kind() {
        term = inner;
    }
    term
}

/// Record `fired`, read from an instance of the axiom `axiom` that fired, into the open
/// collection.
pub(super) fn note(axiom: &str, fired: &Fired) {
    SINK.with_borrow_mut(|sink| {
        if let Some(sink) = sink.as_mut() {
            sink.note(axiom, fired);
        }
    });
}

/// The head of `term` through injections: the symbol of its first application below them.
fn head(term: &Term) -> Option<&Name> {
    let mut term = term;
    loop {
        match term.kind() {
            TermKind::Injection { term: inner, .. } => term = inner,
            TermKind::Application { symbol, .. } => return Some(&symbol.name),
            _ => return None,
        }
    }
}

/// The integer `term` is through injections, when it is an `Int` literal.
fn int_literal(definition: &BackendDefinition, term: &Term) -> Option<BigInt> {
    let mut term = term;
    loop {
        match term.kind() {
            TermKind::Injection { term: inner, .. } => term = inner,
            TermKind::DomainValue { sort, value }
                if definition.domain_kind(sort) == Some(DomainKind::Int) =>
            {
                return std::str::from_utf8(value.as_bytes()).ok()?.parse().ok();
            }
            _ => return None,
        }
    }
}
