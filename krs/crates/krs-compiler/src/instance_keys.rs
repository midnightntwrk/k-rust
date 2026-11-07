//! The instance keys of functions whose context reads one instance of a Map collection.
//!
//! A function context typed by a cell group reads the group's cells in the configuration the
//! function is evaluated in. Where the group sits in a Map collection's instance, that is the one
//! instance the evaluating sentence is about. A function has one value for its arguments, so
//! the instance must be one of its arguments: the function receives, after its own arguments,
//! one hidden key per Map collection on the path of the cells it reads, outermost first. An
//! optional (`?`) holder holds at most one instance, so it adds no key.
//!
//! - An equation with such a context names the instance by its keys: its head receives them,
//!   and its context matches the key cell of each holder with the same key, so it matches at
//!   most one instance.
//! - An equation without a context of its own is evaluated where its caller is, so it receives
//!   the keys of every function it reaches and passes them on.
//! - Every other sentence that applies such a function passes the keys of the instance it is
//!   about: a rule about one instance holds the key cell of its own instance and of every
//!   enclosing one, and binds each key with the pattern it already writes for that cell, or
//!   with a key cell KRS adds.
//! - A term rule that is not `anywhere` runs at the head of the main cell, so it is about the
//!   instances holding the main cell: it is written as a clause of the main cell, beside the key
//!   cells KRS adds, as a `for Sort` clause is.
//! - A sentence that rewrites wherever its left-hand side occurs (a simplification, an
//!   `anywhere` rule, a desugar) is evaluated in no instance of its own, so the keys its
//!   right-hand side and its conditions pass are those its left-hand side's applications
//!   receive.
//!
//! A function is applied where a sentence evaluates it ([`evaluated_terms`]): an equation's or a
//! simplification's left-hand side and a function context's cells are patterns, which evaluate
//! nothing. The keys a function receives, and the callers semantic analysis judges, follow the
//! same applications.
//!
//! Lowering ([`crate::lowering`]) emits the keys from this analysis, and semantic analysis
//! ([`crate::semantic`]) refuses, with the reason, every sentence whose keys it cannot bind
//! ([`KeyRefusal`]), so lowering sees only sentences it can emit.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, CellAttribute, CellCollectionType, CellMultiplicity, ConfigurationClause,
    FixedCell, FixedCellContent, SemanticId, SentenceKind, StableItemId,
};
use krs_ir_levels::{
    IrCondition, RuleBodyRef, SemanticModule, SemanticRule, SemanticSortRef, SemanticTerm,
    SemanticTermKind,
};

/// A Map collection cell whose instances a function may be evaluated in.
#[derive(Clone, Debug)]
pub(crate) struct Holder {
    /// The collection cell's K name.
    pub(crate) name: String,
    /// The key cell of each instance: its first child.
    pub(crate) key: SemanticId,
    /// The key cell's K name.
    pub(crate) key_name: String,
    /// The key cell's content sort; `None` for a key that is a group of cells.
    pub(crate) sort: Option<SemanticSortRef>,
}

impl Holder {
    /// The variable KRS binds this holder's key to where no pattern of the sentence binds it.
    pub(crate) fn variable(&self) -> SemanticId {
        SemanticId::new(self.field()).expect("a cell name makes a path-free semantic identity")
    }

    /// The name of the hidden argument a function receives this holder's key in.
    pub(crate) fn field(&self) -> String {
        krs_ir_levels::k_surface::instance_key_field(&self.name)
    }
}

/// The term a sentence passes for one holder's key.
#[derive(Clone, Debug)]
pub(crate) enum KeyTerm<'a> {
    /// A variable the sentence binds, its own or [`Holder::variable`].
    Variable(SemanticId),
    /// The literal the sentence matches the key cell with.
    Token(&'a SemanticTerm),
}

/// How a sentence passes one holder's key.
#[derive(Clone, Debug)]
pub(crate) struct KeyBinding<'a> {
    /// The Map collection cell.
    pub(crate) holder: SemanticId,
    /// What the sentence passes.
    pub(crate) term: KeyTerm<'a>,
    /// Where the sentence binds [`Holder::variable`] to the instance's key cell, which no
    /// pattern of it binds: in the cells it matches (a clause, or a function context's cell);
    /// `false` where the variable is a head argument (an equation's) or the term is bound by
    /// the sentence's own pattern.
    pub(crate) bind: bool,
    /// The wildcard the sentence writes as that key cell, where it binds the variable there:
    /// the variable names the value the wildcard matches, so it takes the wildcard's place and
    /// the wildcard is no longer a variable of the sentence.
    pub(crate) replaces: Option<SemanticId>,
}

/// Why a sentence's keys cannot be passed.
#[derive(Clone, Debug)]
pub(crate) enum KeyRefusal<'a> {
    /// A sentence that rewrites wherever its left-hand side occurs (a simplification, an
    /// `anywhere` rule, a desugar) applies `function`, which needs the key of `holder`, outside
    /// its left-hand side, and no application its left-hand side matches receives it.
    Unbound {
        function: &'a StableItemId,
        application: &'a SemanticTerm,
        holder: SemanticId,
    },
    /// The sentence matches the key cell of `holder` with `pattern`, which is no variable, no
    /// literal and no wildcard, so no one term of it is the key.
    Pattern {
        holder: SemanticId,
        pattern: &'a SemanticTerm,
    },
    /// The instances of a holder whose key the sentence passes are keyed by a group of cells
    /// ([`InstanceKeys::group_key`] names the first such holder of the definition).
    GroupKey,
    /// The sentence writes `function`, which needs the key of `holder`, in a pattern (an
    /// equation's left-hand side or its function context), which evaluates nothing, and the
    /// equation receives no such key from what it evaluates.
    InPattern {
        function: &'a StableItemId,
        application: &'a SemanticTerm,
        holder: SemanticId,
    },
    /// The sentence runs at the main cell, which lies in no instance of `holder`, and applies
    /// `function`, which needs its key.
    Outside {
        function: &'a StableItemId,
        application: &'a SemanticTerm,
        holder: SemanticId,
    },
    /// The sentence is a `#[k::context]` that names no cell, emitted as K's `context`, which
    /// binds no key cell, and applies `function`, which needs the key of `holder`.
    Context {
        function: &'a StableItemId,
        application: &'a SemanticTerm,
        holder: SemanticId,
    },
}

/// Where a term rule completed to the main cell is written: the configuration, its main cell,
/// and its leaf cells in declaration order.
#[derive(Debug)]
pub(crate) struct MainCell {
    /// The configuration's semantic identity.
    pub(crate) configuration: SemanticId,
    /// The main cell.
    pub(crate) cell: SemanticId,
    /// Every leaf cell of the configuration, in declaration order.
    pub(crate) leaves: Vec<SemanticId>,
}

/// The instance keys of a definition's functions.
#[derive(Debug, Default)]
pub(crate) struct InstanceKeys {
    /// Each cell's optional and collection cells strictly above it, outermost first.
    chains: BTreeMap<SemanticId, Vec<SemanticId>>,
    /// The Map collection cells, by cell.
    holders: BTreeMap<SemanticId, Holder>,
    /// Each Map collection cell's position in the configuration, which orders keys.
    order: BTreeMap<SemanticId, usize>,
    /// Each function that receives keys, and its holders in order.
    functions: BTreeMap<StableItemId, Vec<SemanticId>>,
    /// Each holder whose instances a function context reads, and the first equation whose own
    /// context reads them.
    readers: BTreeMap<SemanticId, StableItemId>,
    /// The main cell, where the configuration has one.
    main: Option<MainCell>,
}

impl InstanceKeys {
    /// The keys of the functions of `modules`, against the configuration one of them holds.
    pub(crate) fn of<'m>(modules: impl IntoIterator<Item = &'m SemanticModule> + Clone) -> Self {
        let mut keys = Self::default();
        let Some(configuration) = modules
            .clone()
            .into_iter()
            .find_map(SemanticModule::configuration)
        else {
            return keys;
        };
        let mut leaves = Vec::new();
        keys.walk(configuration.cells(), &mut Vec::new(), &mut leaves);
        if keys.holders.is_empty() {
            return keys;
        }
        keys.main = krs_ir_levels::k_surface::main_cell(configuration)
            .cell()
            .map(|cell| MainCell {
                configuration: configuration.id().clone(),
                cell: cell.id().clone(),
                leaves,
            });
        let rules = modules
            .into_iter()
            .flat_map(SemanticModule::rules)
            .collect::<Vec<_>>();
        // Each equation's function, the holders its own context reads, and the functions it
        // applies.
        let equations = rules
            .iter()
            .filter_map(|rule| {
                let function = defined_function(rule)?;
                let own = rule
                    .function_context()
                    .map(|context| {
                        keys.map_holders(
                            &keys.chain(
                                context
                                    .cells()
                                    .cells()
                                    .iter()
                                    .map(krs_ir::FixedCellPattern::cell),
                            ),
                        )
                    })
                    .unwrap_or_default();
                let applied = evaluated_applications(rule)
                    .into_iter()
                    .map(|(applied, _)| applied)
                    .collect::<BTreeSet<_>>();
                Some((rule, function, own, applied))
            })
            .collect::<Vec<_>>();
        for (rule, _, own, _) in &equations {
            for holder in own {
                keys.readers
                    .entry(holder.clone())
                    .or_insert_with(|| rule.id().clone());
            }
        }
        let mut functions = BTreeMap::<&StableItemId, BTreeSet<SemanticId>>::new();
        loop {
            let mut changed = false;
            for (_, function, own, applied) in &equations {
                let mut reached = own.iter().cloned().collect::<BTreeSet<_>>();
                for callee in applied {
                    reached.extend(functions.get(callee).into_iter().flatten().cloned());
                }
                let known = functions.entry(function).or_default();
                if !reached.is_subset(known) {
                    known.extend(reached);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        keys.functions = functions
            .into_iter()
            .filter(|(_, holders)| !holders.is_empty())
            .map(|(function, holders)| (function.clone(), keys.ordered(holders)))
            .collect();
        keys
    }

    /// Indexes `cells` below the holders `chain`, and lists their leaf cells in `leaves`.
    fn walk(
        &mut self,
        cells: &[FixedCell<SemanticSortRef, SemanticId>],
        chain: &mut Vec<SemanticId>,
        leaves: &mut Vec<SemanticId>,
    ) {
        for cell in cells {
            self.chains.insert(cell.id().clone(), chain.clone());
            if matches!(cell.content(), FixedCellContent::Term { .. }) {
                leaves.push(cell.id().clone());
            }
            let multiplicity = cell
                .attributes()
                .iter()
                .find_map(|attribute| match attribute {
                    CellAttribute::Multiplicity { value, .. } => Some(*value),
                    _ => None,
                });
            let map = cell.attributes().iter().any(|attribute| {
                matches!(
                    attribute,
                    CellAttribute::CollectionType {
                        value: CellCollectionType::Map,
                        ..
                    }
                )
            });
            let FixedCellContent::Children { children } = cell.content() else {
                continue;
            };
            if multiplicity == Some(CellMultiplicity::Star)
                && map
                && let Some(key) = children.first()
            {
                self.order.insert(cell.id().clone(), self.order.len());
                self.holders.insert(
                    cell.id().clone(),
                    Holder {
                        name: cell.name().to_owned(),
                        key: key.id().clone(),
                        key_name: key.name().to_owned(),
                        sort: match key.content() {
                            FixedCellContent::Term { sort, .. } => Some(sort.clone()),
                            FixedCellContent::Children { .. } => None,
                        },
                    },
                );
            }
            if multiplicity.is_some() {
                chain.push(cell.id().clone());
                self.walk(children, chain, leaves);
                chain.pop();
            } else {
                self.walk(children, chain, leaves);
            }
        }
    }

    /// The instances a sentence naming `cells` is about, outermost first ([`rule_instances`]
    /// over each cell's holders); none for cells off one chain of nested instances, which
    /// semantic analysis refuses in a sentence that passes keys.
    fn chain<'c>(&self, cells: impl IntoIterator<Item = &'c SemanticId>) -> Vec<SemanticId> {
        rule_instances(
            cells
                .into_iter()
                .filter_map(|cell| self.chains.get(cell).cloned()),
        )
        .unwrap_or_default()
    }

    /// The instances a configuration rule with `clauses` is about, outermost first
    /// ([`entry_instances`] over each clause's instance path, and the holder whose one instance
    /// an entry steps).
    fn configuration_chain(
        &self,
        clauses: &[ConfigurationClause<SemanticId, SemanticTerm>],
    ) -> Vec<SemanticId> {
        entry_instances(clauses.iter().filter_map(|clause| {
            let path = self.chains.get(clause.cell())?.clone();
            let stepped = match clause {
                ConfigurationClause::Instances(entry) if entry.stepped_instance().is_some() => {
                    Some(entry.cell().clone())
                }
                _ => None,
            };
            Some((path, stepped))
        }))
        .unwrap_or_default()
    }

    /// The Map collection cells of `chain`.
    fn map_holders(&self, chain: &[SemanticId]) -> Vec<SemanticId> {
        chain
            .iter()
            .filter(|cell| self.holders.contains_key(*cell))
            .cloned()
            .collect()
    }

    /// `holders` in configuration order.
    fn ordered(&self, holders: impl IntoIterator<Item = SemanticId>) -> Vec<SemanticId> {
        let mut holders = holders.into_iter().collect::<Vec<_>>();
        holders.sort_by_key(|holder| self.order.get(holder).copied());
        holders.dedup();
        holders
    }

    /// The Map collection cell `cell`.
    pub(crate) fn holder(&self, cell: &SemanticId) -> Option<&Holder> {
        self.holders.get(cell)
    }

    /// The Map collection cell whose instances `key` is the key cell of.
    pub(crate) fn key_holder(&self, key: &SemanticId) -> Option<&SemanticId> {
        self.holders
            .iter()
            .find(|(_, holder)| holder.key == *key)
            .map(|(cell, _)| cell)
    }

    /// The holders whose keys `function` receives after its own arguments, outermost first;
    /// empty for a function that receives none.
    pub(crate) fn function(&self, function: &StableItemId) -> &[SemanticId] {
        self.functions.get(function).map_or(&[], Vec::as_slice)
    }

    /// Whether any function receives keys.
    pub(crate) fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// The main cell a term rule that passes keys is written at ([`Self::completes`]).
    pub(crate) fn main(&self) -> Option<&MainCell> {
        self.main.as_ref()
    }

    /// The first holder keyed by a group of cells whose key some function receives, with the
    /// first equation whose own context reads its instances.
    pub(crate) fn group_key(&self) -> Option<(&SemanticId, &StableItemId)> {
        self.functions
            .values()
            .flatten()
            .find(|holder| self.holders[*holder].sort.is_none())
            .and_then(|holder| Some((holder, self.readers.get(holder)?)))
    }

    /// Whether `rule` is a term rule that runs at the head of the main cell (a transition that
    /// is not `anywhere`) and passes keys, so lowering writes it as a clause of the main cell
    /// beside the key cells it binds.
    pub(crate) fn completes(&self, rule: &SemanticRule) -> bool {
        at_main_cell(rule) && !self.sentence(rule).is_empty()
    }

    /// The holders whose keys `rule` passes: its function's for an equation, and otherwise
    /// those of every function it applies.
    fn sentence(&self, rule: &SemanticRule) -> Vec<SemanticId> {
        if let Some(function) = defined_function(rule) {
            return self.function(function).to_vec();
        }
        self.ordered(
            applications(rule)
                .into_iter()
                .flat_map(|(applied, _)| self.function(applied).iter().cloned()),
        )
    }

    /// How `rule` passes each key it passes ([`Self::sentence`]), in holder order.
    ///
    /// # Errors
    ///
    /// The first [`KeyRefusal`] of the sentence.
    pub(crate) fn bindings<'r>(
        &self,
        rule: &'r SemanticRule,
    ) -> Result<Vec<KeyBinding<'r>>, KeyRefusal<'r>> {
        let holders = self.sentence(rule);
        // An application in an equation's pattern is evaluated nowhere, so it passes the keys
        // the equation receives from what it evaluates, which must include its own.
        if defined_function(rule).is_some()
            && let Some((function, application, holder)) =
                self.missing(applications(rule), |holder| !holders.contains(holder))
        {
            return Err(KeyRefusal::InPattern {
                function,
                application,
                holder,
            });
        }
        if holders.is_empty() {
            return Ok(Vec::new());
        }
        if holders
            .iter()
            .any(|holder| self.holders[holder].sort.is_none())
        {
            return Err(KeyRefusal::GroupKey);
        }
        let fresh = |holder: &SemanticId, bind: bool| self.fresh(holder, bind);
        // A key cell the sentence writes with a wildcard, or not at all, binds the variable.
        let bind_fresh = |holder: &SemanticId, pattern: Option<&SemanticTerm>| KeyBinding {
            replaces: pattern.and_then(wildcard),
            ..self.fresh(holder, true)
        };
        match rule.relational_body() {
            RuleBodyRef::Configuration { body, .. } => {
                let chain = self.configuration_chain(body.clauses());
                holders
                    .iter()
                    .map(|holder| {
                        let key = &self.holders[holder].key;
                        // The key cell lies in the holder's instance: a clause of its own where
                        // the rule names that instance's cells, or a child of the instance an
                        // entry of the holder steps.
                        let pattern = body
                            .fixed_clauses()
                            .chain(stepped_children(body.clauses(), holder))
                            .find(|clause| clause.cell() == key)
                            .map(krs_ir::FixedCellClause::before);
                        Self::bound(holder, pattern, chain.contains(holder))
                            .map(|bound| bound.unwrap_or_else(|| bind_fresh(holder, pattern)))
                    })
                    .collect()
            }
            RuleBodyRef::Term(_) if rule.kind() == SentenceKind::Equation => {
                let Some(context) = rule.function_context() else {
                    return Ok(holders.iter().map(|holder| fresh(holder, false)).collect());
                };
                let cells = context.cells().cells();
                let chain = self.chain(cells.iter().map(krs_ir::FixedCellPattern::cell));
                holders
                    .iter()
                    .map(|holder| {
                        if !chain.contains(holder) {
                            // A key of another equation's context: a head argument only.
                            return Ok(fresh(holder, false));
                        }
                        let key = &self.holders[holder].key;
                        let pattern = cells
                            .iter()
                            .find(|cell| cell.cell() == key)
                            .map(krs_ir::FixedCellPattern::pattern);
                        Self::bound(holder, pattern, true)
                            .map(|bound| bound.unwrap_or_else(|| bind_fresh(holder, pattern)))
                    })
                    .collect()
            }
            // A term rule at the head of the main cell is about the instances holding it.
            RuleBodyRef::Term(_) if at_main_cell(rule) => self.at_main(rule, &holders),
            // A `#[k::context]` that names no cell is K's `context`, which binds no cell.
            RuleBodyRef::Term(_) if rule.kind() == SentenceKind::Context => {
                let (function, application, holder) = self
                    .missing(applications(rule), |_| true)
                    .expect("a sentence that passes a key applies a function receiving it");
                Err(KeyRefusal::Context {
                    function,
                    application,
                    holder,
                })
            }
            // A sentence that rewrites wherever its left-hand side occurs.
            RuleBodyRef::Term(_) | RuleBodyRef::Predicate(_) => self.anywhere(rule, &holders),
        }
    }

    /// [`Self::bindings`] of a term rule at the head of the main cell: the keys of the
    /// instances holding the main cell, from key cells KRS adds.
    fn at_main<'r>(
        &self,
        rule: &'r SemanticRule,
        holders: &[SemanticId],
    ) -> Result<Vec<KeyBinding<'r>>, KeyRefusal<'r>> {
        let chain = self
            .main
            .as_ref()
            .and_then(|main| self.chains.get(&main.cell))
            .map_or(&[][..], Vec::as_slice);
        if let Some((function, application, holder)) =
            self.missing(applications(rule), |holder| !chain.contains(holder))
        {
            return Err(KeyRefusal::Outside {
                function,
                application,
                holder,
            });
        }
        Ok(holders
            .iter()
            .map(|holder| self.fresh(holder, true))
            .collect())
    }

    /// [`Self::bindings`] of a sentence that rewrites wherever its left-hand side occurs: the
    /// keys its left-hand side's applications receive, which it matches.
    fn anywhere<'r>(
        &self,
        rule: &'r SemanticRule,
        holders: &[SemanticId],
    ) -> Result<Vec<KeyBinding<'r>>, KeyRefusal<'r>> {
        let matched = left_terms(rule)
            .into_iter()
            .flat_map(|term| {
                let mut applied = Vec::new();
                term_applications(term, &mut applied);
                applied
            })
            .flat_map(|(applied, _)| self.function(applied).iter().cloned())
            .collect::<BTreeSet<_>>();
        if let Some((function, application, holder)) = self
            .missing(evaluated_applications(rule), |holder| {
                !matched.contains(holder)
            })
        {
            return Err(KeyRefusal::Unbound {
                function,
                application,
                holder,
            });
        }
        Ok(holders
            .iter()
            .map(|holder| self.fresh(holder, false))
            .collect())
    }

    /// The binding of `holder`'s key to [`Holder::variable`], which a key cell KRS adds binds
    /// where `bind`.
    fn fresh<'r>(&self, holder: &SemanticId, bind: bool) -> KeyBinding<'r> {
        KeyBinding {
            holder: holder.clone(),
            term: KeyTerm::Variable(self.holders[holder].variable()),
            bind,
            replaces: None,
        }
    }

    /// The first of `applications` whose function receives the key of a holder `missing` holds
    /// for: the function, its application and the holder.
    fn missing<'r>(
        &self,
        applications: Vec<(&'r StableItemId, &'r SemanticTerm)>,
        missing: impl Fn(&SemanticId) -> bool,
    ) -> Option<(&'r StableItemId, &'r SemanticTerm, SemanticId)> {
        applications.into_iter().find_map(|(applied, at)| {
            self.function(applied)
                .iter()
                .find(|holder| missing(holder))
                .map(|holder| (applied, at, holder.clone()))
        })
    }

    /// The binding of `holder`'s key by the sentence's own `pattern` for its key cell: the
    /// variable or literal it matches, or `None` where it writes none or a wildcard, which KRS
    /// replaces by [`Holder::variable`]. A pattern outside the sentence's instances (`inside`
    /// false) binds nothing.
    fn bound<'r>(
        holder: &SemanticId,
        pattern: Option<&'r SemanticTerm>,
        inside: bool,
    ) -> Result<Option<KeyBinding<'r>>, KeyRefusal<'r>> {
        let Some(pattern) = pattern.filter(|_| inside) else {
            return Ok(None);
        };
        let term = match key_term(pattern) {
            KeyPattern::Term(term) => term,
            KeyPattern::Wildcard => return Ok(None),
            KeyPattern::Other => {
                return Err(KeyRefusal::Pattern {
                    holder: holder.clone(),
                    pattern,
                });
            }
        };
        Ok(Some(KeyBinding {
            holder: holder.clone(),
            term,
            bind: false,
            replaces: None,
        }))
    }
}

/// The instances a rule that matches cells with the instance paths `paths` is a local step of,
/// outermost first, where it is evaluated: the deepest path, which holds every other one as a
/// prefix; `None` where two paths are not on one chain of nested instances. A path is the
/// optional (`?`) and collection (`*`) cells strictly above a cell, outermost first; a holder's
/// own entry (an instance list, an optional cell's state) matches the holder whole, in none of
/// its instances, so its path stops above it, except an instance list that steps one instance
/// ([`entry_instances`]).
///
/// A matched cell is in one instance of each holder on its path, and the rule's cells are
/// matched together: the emitted rule writes each clause inside the cells of the instances it
/// lies in, one nesting of instance cells for the whole rule
/// ([`DefinitionIndex::sentence_instances`](krs_ir_levels::k_surface::DefinitionIndex::sentence_instances)),
/// so every cell the rule matches below one holder lies in the same instance of it. Matching a
/// cell of a thread therefore fixes one thread, in the one hart that holds it, and the rule is a
/// step of that thread as much as of that hart: a function it evaluates whose context reads
/// that thread is evaluated in it, and receives both keys. The prefix the paths share would
/// instead place a rule that matches a hart's computation and a cell of one of its threads in
/// the hart alone, and refuse the thread's function although the rule determines the thread.
///
/// Several instances of one holder are matched only through the holder's instance list, whose
/// entry then stops above the holder, so they never make the path ambiguous: such a rule is
/// about the holder whole, and a function evaluated in one of its instances is refused from it.
///
/// Two paths off one chain (a hart's cell and a cell of a device beside the harts) name
/// instances of holders neither of which holds the other, so no one instance of each holder on
/// one path holds the rule, and the rule is about no one instance a function could be evaluated
/// in.
pub(crate) fn rule_instances<T: PartialEq + Clone>(
    paths: impl IntoIterator<Item = Vec<T>>,
) -> Option<Vec<T>> {
    let paths = paths.into_iter().collect::<Vec<_>>();
    let deepest = paths
        .iter()
        .max_by_key(|path| path.len())
        .cloned()
        .unwrap_or_default();
    paths
        .iter()
        .all(|path| deepest.starts_with(path))
        .then_some(deepest)
}

/// The instances a rule is a local step of ([`rule_instances`]), where an entry of a holder
/// that matches one instance and carries the rest unchanged
/// ([`krs_ir::InstancesClause::stepped_instance`]) is a step of that instance. Each matched cell
/// is given as its instance path and, for such an entry, the holder whose instance it steps,
/// which extends the path by one.
///
/// The entry matches the holder's collection only through that one instance: the other
/// instances are framed and carried unchanged, so what the step reads and writes are that
/// instance's cells, and its key cell is matched, so the key is determined. An entry that
/// matches several instances, creates or removes one, or names every instance is about the
/// holder whole, and its path stops above the holder.
///
/// Where the instances the entries step and the cells lie in are on no one chain (one thread and
/// one job of a core, each through its entry), the rule is a step of the instances its cells
/// lie in and its entries stop above their holders, as for an entry about the holder whole:
/// stepping both instances would leave it about no one instance, although the core is
/// determined.
pub(crate) fn entry_instances<T: PartialEq + Clone>(
    paths: impl IntoIterator<Item = (Vec<T>, Option<T>)>,
) -> Option<Vec<T>> {
    let paths = paths.into_iter().collect::<Vec<_>>();
    rule_instances(paths.iter().map(|(path, stepped)| {
        let mut path = path.clone();
        path.extend(stepped.iter().cloned());
        path
    }))
    .or_else(|| rule_instances(paths.into_iter().map(|(path, _)| path)))
}

/// The children of the instance the entry of `holder` among `clauses` steps
/// ([`krs_ir::InstancesClause::stepped_instance`]); none where no entry of `holder` steps one.
pub(crate) fn stepped_children<'c, C: PartialEq, T>(
    clauses: &'c [ConfigurationClause<C, T>],
    holder: &C,
) -> impl Iterator<Item = &'c krs_ir::FixedCellClause<C, T>> {
    clauses
        .iter()
        .filter_map(move |clause| match clause {
            ConfigurationClause::Instances(entry) if entry.cell() == holder => {
                match entry.stepped_instance()? {
                    krs_ir::InstanceClause::Kept { children, .. } => Some(children.iter()),
                    _ => None,
                }
            }
            _ => None,
        })
        .flatten()
}

/// What a key cell's pattern binds the key to.
enum KeyPattern<'a> {
    /// The one term it binds, a variable or a literal.
    Term(KeyTerm<'a>),
    /// Nothing: a wildcard.
    Wildcard,
    /// No one term: a pattern that is no variable, alias, literal or wildcard.
    Other,
}

/// What `pattern`, a key cell's, binds the key to. A rewrite that keeps the key (`me => me`)
/// binds what it matches.
fn key_term(pattern: &SemanticTerm) -> KeyPattern<'_> {
    match pattern.kind() {
        SemanticTermKind::Variable { variable }
            if variable.kind() == krs_ir::SemanticIdKind::Wildcard =>
        {
            KeyPattern::Wildcard
        }
        SemanticTermKind::Variable { variable }
        | SemanticTermKind::As {
            alias: variable, ..
        } => KeyPattern::Term(KeyTerm::Variable(variable.clone())),
        SemanticTermKind::Token { .. } => KeyPattern::Term(KeyTerm::Token(pattern)),
        SemanticTermKind::Rewrite { from, .. } => match key_term(from) {
            KeyPattern::Term(term) => KeyPattern::Term(term),
            KeyPattern::Wildcard | KeyPattern::Other => KeyPattern::Other,
        },
        _ => KeyPattern::Other,
    }
}

/// The wildcard `pattern` is, if it is one.
fn wildcard(pattern: &SemanticTerm) -> Option<SemanticId> {
    match pattern.kind() {
        SemanticTermKind::Variable { variable }
            if variable.kind() == krs_ir::SemanticIdKind::Wildcard =>
        {
            Some(variable.clone())
        }
        _ => None,
    }
}

/// The function an equation defines: the declared head of its left-hand side.
pub(crate) fn defined_function(rule: &SemanticRule) -> Option<&StableItemId> {
    if rule.kind() != SentenceKind::Equation {
        return None;
    }
    let RuleBodyRef::Term(body) = rule.relational_body() else {
        return None;
    };
    match body.from().kind() {
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(function),
            ..
        } => Some(function),
        _ => None,
    }
}

/// Whether `rule` is a term rule that runs at the head of the main cell: a transition that is
/// not `anywhere`, which K completes to the head of the computation.
fn at_main_cell(rule: &SemanticRule) -> bool {
    rule.kind() == SentenceKind::Transition
        && rule.anywhere().is_none()
        && matches!(rule.relational_body(), RuleBodyRef::Term(_))
}

/// The terms `rule` evaluates functions in: an equation's or a simplification's right-hand side
/// and conditions, since its left-hand side is the pattern it is about, not an application it
/// evaluates; every term of any other sentence but its function context, whose cells are a
/// pattern too.
pub(crate) fn evaluated_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    let pattern_left = matches!(
        rule.kind(),
        SentenceKind::Equation | SentenceKind::Simplification
    );
    let mut terms = match rule.relational_body() {
        RuleBodyRef::Term(body) if pattern_left => vec![body.to()],
        RuleBodyRef::Term(body) => vec![body.from(), body.to()],
        RuleBodyRef::Predicate(body) if pattern_left => body.rhs().terms(),
        RuleBodyRef::Predicate(body) => body
            .lhs()
            .terms()
            .into_iter()
            .chain(body.rhs().terms())
            .collect(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .flat_map(krs_ir::ClausePart::terms)
            .collect(),
    };
    terms.extend(rule.requires().into_iter().flat_map(IrCondition::terms));
    terms.extend(rule.ensures().into_iter().flat_map(IrCondition::terms));
    terms
}

/// Every declared application `rule` evaluates ([`evaluated_terms`]), in its terms' order.
pub(crate) fn evaluated_applications(rule: &SemanticRule) -> Vec<(&StableItemId, &SemanticTerm)> {
    let mut applied = Vec::new();
    for term in evaluated_terms(rule) {
        term_applications(term, &mut applied);
    }
    applied
}

/// Every declared application in `rule`, in its terms' order, but an equation's own head:
/// its rewrite, its function context, its conditions; the applications lowering writes.
fn applications(rule: &SemanticRule) -> Vec<(&StableItemId, &SemanticTerm)> {
    let head = defined_function(rule).and_then(|_| match rule.relational_body() {
        RuleBodyRef::Term(body) => Some(body.from()),
        _ => None,
    });
    let mut terms = match rule.relational_body() {
        RuleBodyRef::Term(body) => match body.local_term() {
            Some(local) => vec![local],
            None => vec![body.from(), body.to()],
        },
        RuleBodyRef::Predicate(body) => body
            .lhs()
            .terms()
            .into_iter()
            .chain(body.rhs().terms())
            .collect(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .flat_map(krs_ir::ClausePart::terms)
            .collect(),
    };
    if let Some(context) = rule.function_context() {
        terms.extend(
            context
                .cells()
                .cells()
                .iter()
                .map(krs_ir::FixedCellPattern::pattern),
        );
    }
    terms.extend(rule.requires().into_iter().flat_map(IrCondition::terms));
    terms.extend(rule.ensures().into_iter().flat_map(IrCondition::terms));
    let mut applied = Vec::new();
    for term in terms {
        match head {
            // The head is the function the equation defines, not an application of it.
            Some(head) if std::ptr::eq(term, head) => {
                for argument in term.children() {
                    term_applications(argument, &mut applied);
                }
            }
            _ => term_applications(term, &mut applied),
        }
    }
    applied
}

/// The left-hand side of a sentence that rewrites wherever it matches.
fn left_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.from()],
        RuleBodyRef::Predicate(body) => body.lhs().terms(),
        RuleBodyRef::Configuration { .. } => Vec::new(),
    }
}

/// Every declared application at or below `term`, in preorder.
pub(crate) fn term_applications<'a>(
    term: &'a SemanticTerm,
    output: &mut Vec<(&'a StableItemId, &'a SemanticTerm)>,
) {
    if let SemanticTermKind::Application {
        application: ApplicationRef::Declared(production),
        ..
    } = term.kind()
    {
        output.push((production, term));
    }
    for child in term.children() {
        term_applications(child, output);
    }
}
