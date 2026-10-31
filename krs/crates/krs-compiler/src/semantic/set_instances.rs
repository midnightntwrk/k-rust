//! A Set cell collection's computed instance, looked up (decision NT-Q6).
//!
//! A Set collection (`#[k::cell(multiplicity = "*", cell_type = "Set",
//! nested)]`) is a set of its instances, and a pattern looks it up by an
//! instance as it looks a set up by an element: an instance whose every cell
//! is written and computed from names the pattern binds elsewhere denotes the
//! one instance it computes, and the rule applies when the collection holds
//! that instance ([`super::function_patterns`] judges the reading).
//!
//! K writes an instance as the cells it holds, and both K frontends check a
//! rule's left side before they make the instance an element of the cell
//! set: a function there is refused as a function in a pattern, and no
//! frontend reads the set's element symbol inside a cell. So the lowering
//! keeps the instance's cells and writes each construct the instance computes
//! (a function's application, an operator, a sort test) as a fresh variable,
//! which a guard of the rule equates with the value the construct computes:
//! `Obj { oid: n + 1, hits: 0 }` is `<obj> <oid> V </oid> <hits> 0 </hits>
//! </obj>` with `requires V ==K N +Int 1`, ahead of the author's condition,
//! which reads the lookup's result. The two denote the same rule:
//!
//! - matching binds `V` to the cell's value in an instance of the
//!   collection, and the guard holds exactly when that value is the computed
//!   one, so the rule applies to a configuration exactly when the collection
//!   holds the computed instance, with the same substitution of the rule's
//!   own names;
//! - a set holds an element once, and every cell of the instance is written,
//!   so at most one instance passes the guard: the choice of an instance that
//!   matching makes is no choice, the lookup of one element;
//! - `==K` is K's equality of terms, the one a match decides, at every sort.
//!
//! A selection instance (one that holds a name nothing else binds, `_`, an
//! alias, alternatives, an open record or `..`) holds no construct that
//! computes ([`super::function_patterns`] refuses one), so only a computed
//! instance has guards.
//!
//! A key a pattern looks up (decision D2) is guarded too, where it holds a
//! sort projection or a collection read KRS projects below the `KItem` K's
//! read returns (finding NT-11-1). `{t}:>S` denotes `t` where `t` has sort
//! `S`, and nothing otherwise, so the guard states that `t` has sort `S`
//! wherever the projection stands, and no guard holds a projection:
//!
//! - at the key's root the key is `t` with the guard `isS(t)`: a map's key is
//!   a `KItem`, so the entry at `t` is looked up exactly when the projection
//!   is defined, and its value is the one the projection computes;
//! - at a matched position below a constructor, where the key's sort `S` is
//!   needed and `t` need not have it, the projection is a fresh variable `V`
//!   of sort `S` with the guard `V ==K t`: `V`'s sort already tests `t`, so
//!   the guard holds exactly when `t` is the `S` the entry's key holds there,
//!   and `==K` is defined on every pair of terms;
//! - below a function's application the key is computed, the projection is
//!   read by value as the function's argument, and it is defined only where
//!   `isS(t)` holds, which the guard states.
//!
//! The guards are conjoined ahead of the sentence's condition, so a sentence
//! that has no condition to hold them cannot look such a key up: its lowering
//! receives the guards and refuses them ([`SentenceGuards`]).
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, DescriptorTerm, GeneratedOperation, NodeOrigin,
    ProvenanceKey, SemanticId, SourceMapKey,
};
use krs_ir_levels::{
    SemanticCondition, SemanticRuleCondition, SemanticSortRef, SemanticTerm, SemanticVariable,
};

use super::error::DescriptorLoweringError;
use super::function_patterns::{Applied, applied_function};
use super::infer::StructuredTermBuilder;
use super::origin::semantic_origin;

/// The guards of the computed instances one sentence looks up, and of the
/// projections in the keys it looks up.
#[derive(Debug, Default)]
pub(super) struct InstanceGuards {
    /// The number of guards the sentence's earlier builders made, which
    /// numbers this builder's fresh variables after theirs.
    offset: usize,
    guards: Vec<Guard>,
    /// Whether a looked-up instance's cell is being lowered: a readable
    /// rule's one builder keeps the rule's guards from its first instance to
    /// its condition, and guards only while it lowers such a cell.
    active: bool,
    /// How many constructs that compute enclose the term being lowered in a
    /// looked-up key: below one a term is computed, not matched, and a
    /// projection there is read by value as the construct's operand.
    computed: usize,
}

/// One construct an instance or a key computes: the fresh variable written in
/// its place, and the guard `variable ==K value`; or, for a key that is a
/// projection, no variable and the guard that the projection is defined.
#[derive(Debug)]
pub(super) struct Guard {
    variable: Option<SemanticVariable>,
    equation: SemanticTerm,
    /// The construct's node, where the guard's conjunction is anchored.
    key: ProvenanceKey,
}

impl InstanceGuards {
    /// Guards numbered after the sentence's first `offset`.
    pub(super) const fn after(offset: usize) -> Self {
        Self {
            offset,
            guards: Vec::new(),
            active: false,
            computed: 0,
        }
    }

    /// Whether a looked-up instance's cell is being lowered, where a
    /// construct that computes is guarded.
    pub(super) const fn active(&self) -> bool {
        self.active
    }

    /// Sets whether a looked-up instance's cell is being lowered, where what
    /// it computes is guarded.
    pub(super) fn activate(&mut self, active: bool) {
        self.active = active;
    }

    /// Enters (`true`) or leaves the operands of a construct that computes.
    pub(super) fn compute(&mut self, entering: bool) {
        if entering {
            self.computed += 1;
        } else {
            self.computed -= 1;
        }
    }

    /// Whether no construct that computes encloses the term being lowered.
    pub(super) const fn matched(&self) -> bool {
        self.computed == 0
    }

    /// The number of guards made.
    pub(super) fn len(&self) -> usize {
        self.offset + self.guards.len()
    }

    /// The guards made.
    pub(super) fn into_guards(self) -> Vec<Guard> {
        self.guards
    }
}

/// The guards one sentence's pattern made, which its condition must hold:
/// the only ways to spend them are [`guarded_requires`] and
/// [`SentenceGuards::refuse`], so a sentence's lowering cannot drop one.
#[derive(Debug, Default)]
#[must_use = "a sentence's guards are its lookup: conjoin them with its condition or refuse them"]
pub(super) struct SentenceGuards(Vec<Guard>);

impl SentenceGuards {
    /// Adds the guards one builder made.
    pub(super) fn extend(&mut self, guards: Vec<Guard>) {
        self.0.extend(guards);
    }

    /// The number of guards.
    pub(super) fn len(&self) -> usize {
        self.0.len()
    }

    /// `Ok` when there are no guards; otherwise `refusal` of the construct
    /// the first guard is anchored at, a sentence `sentence` names, which has
    /// no condition to hold them.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidSortTest`] at the construct.
    pub(super) fn refuse(
        self,
        descriptor: &krs_ir::Descriptor,
        sentence: &str,
    ) -> Result<(), DescriptorLoweringError> {
        let Some(first) = self.0.into_iter().next() else {
            return Ok(());
        };
        Err(DescriptorLoweringError::InvalidSortTest {
            item: Box::new(descriptor.id().clone()),
            reason: format!(
                "this key holds a sort projection, or a read projected to a sort below `KItem`, which denotes a value only where its operand has that sort; a pattern that looks the key up must also require that, and {sentence} has no condition to hold it: bind the key's name at its sort instead (`x: Term<Int>`), so the key is matched at that sort"
            ),
            range: descriptor
                .provenance()
                .origin_for(&first.key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        })
    }
}

impl Guard {
    /// The fresh variable, which the sentence declares, if the guard has one.
    pub(super) fn variable(&self) -> Option<SemanticVariable> {
        self.variable.clone()
    }
}

impl StructuredTermBuilder<'_> {
    /// Whether `term` computes a value: a function's application (an
    /// operator, a method and an index included) or a sort test. A record
    /// update is a constructor's application over the matched record's
    /// fields (F5), a pattern as any constructor's.
    pub(super) fn computes(&self, term: &DescriptorTerm) -> bool {
        match term {
            DescriptorTerm::Application { reference, .. } => matches!(
                applied_function(&reference.application, self.catalog),
                Applied::Function(_)
            ),
            DescriptorTerm::SortTest { .. } => true,
            _ => false,
        }
    }

    /// `term`, a construct a looked-up instance computes, written as a fresh
    /// variable whose guard equates it with the value `term` computes, built
    /// from the sentence's names.
    pub(super) fn guarded(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let key = match term {
            DescriptorTerm::Application { reference, .. } => reference.key.clone(),
            DescriptorTerm::SortTest { key, .. } => key.clone(),
            _ => unreachable!("only a construct that computes is guarded"),
        };
        // Below the construct every position is built.
        let guards = self.instance_guards.take();
        let value = self.lower(term, expected_sort, subject);
        self.instance_guards = guards;
        let value = value?;
        let sort = value.sort().clone();
        self.guard_equal(key, sort, value)
    }

    /// A fresh variable of `sort` whose guard equates it with `value`, a
    /// construct's lowered value, anchored at `key`.
    pub(super) fn guard_equal(
        &mut self,
        key: ProvenanceKey,
        sort: SemanticSortRef,
        value: SemanticTerm,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let guards = self
            .instance_guards
            .as_mut()
            .expect("a guarded construct stands in a looked-up instance or key");
        let ordinal = guards.len();
        let id = SemanticId::new(format!("{}instance{ordinal}", krs_ir::ir::RESERVED_MARKER))?;
        let descriptor = self.descriptor;
        let read = SemanticTerm::variable(
            semantic_origin(descriptor, key.clone(), "instance-guard-variable")?,
            sort.clone(),
            id.clone(),
        );
        let equation = SemanticTerm::application(
            semantic_origin(descriptor, key.clone(), "instance-guard")?,
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(BuiltinOperation::KEqualEq),
            vec![read, value],
        );
        guards.guards.push(Guard {
            variable: Some(SemanticVariable::new(id.clone(), sort.clone())),
            equation,
            key: key.clone(),
        });
        Ok(SemanticTerm::variable(
            semantic_origin(descriptor, key, "instance-guard-match")?,
            sort,
            id,
        ))
    }

    /// Adds the guard `isS(operand)`, `S` being `sort`, anchored at the
    /// projection `key` names: the projection of `operand` to `S` is defined.
    /// The guard reads a copy of `operand` under source-map keys of its own,
    /// since `operand` stands in the key too.
    pub(super) fn require_sort(
        &mut self,
        key: ProvenanceKey,
        sort: SemanticSortRef,
        operand: &SemanticTerm,
    ) -> Result<(), DescriptorLoweringError> {
        let guards = self
            .instance_guards
            .as_mut()
            .expect("a key's projection is guarded where the sentence gathers guards");
        let suffix = format!("~key-guard-{}", guards.len());
        let tested = operand.map_origins(&mut |origin| suffixed(origin, &suffix));
        let defined = SemanticTerm::application(
            semantic_origin(self.descriptor, key.clone(), "key-projection-guard")?,
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Generated(GeneratedOperation::SortPredicate(sort)),
            vec![tested],
        );
        guards.guards.push(Guard {
            variable: None,
            equation: defined,
            key,
        });
        Ok(())
    }
}

/// `origin` under the source-map key extended by `suffix`, which no node of
/// the sentence has.
fn suffixed(origin: &NodeOrigin, suffix: &str) -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new(format!("{}{suffix}", origin.key().as_str()))
            .expect("a source-map key extended by a separator-free suffix is a key"),
        origin.origin().clone(),
    )
}

/// `requires` with the guards of the sentence's looked-up instances before
/// it: the guards, then the author's condition, joined by `andThenBool`. The
/// guards are the lookup, which the author's condition reads the result of,
/// so it is evaluated only once they hold, as after a lookup's match.
///
/// # Errors
///
/// Returns an internal error for a matching-logic condition, which no
/// sentence that looks an instance up has (a transition's condition is a
/// Bool), and an origin's error.
pub(super) fn guarded_requires(
    descriptor: &krs_ir::Descriptor,
    requires: Option<SemanticCondition>,
    guards: impl Into<SentenceGuards>,
) -> Result<Option<SemanticCondition>, DescriptorLoweringError> {
    let SentenceGuards(guards) = guards.into();
    let Some(first) = guards.first() else {
        return Ok(requires);
    };
    let origin = semantic_origin(descriptor, first.key.clone(), "instance-guard-condition")?;
    let (origin, author) = match requires {
        None => (origin, None),
        Some(SemanticCondition::Bool(condition)) => {
            (condition.origin().clone(), Some(condition.term().clone()))
        }
        Some(SemanticCondition::Predicate(_)) => {
            return Err(DescriptorLoweringError::invalid_term(
                descriptor.id(),
                "a sentence that looks a Set collection's instance or a guarded key up has a Bool condition",
            ));
        }
    };
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    let mut conjuncts = guards
        .into_iter()
        .map(|guard| (Some(guard.key), guard.equation))
        .chain(author.map(|term| (None, term)))
        .collect::<Vec<_>>();
    let (_, mut term) = conjuncts.pop().expect("a guard was given");
    while let Some((key, conjunct)) = conjuncts.pop() {
        let key = key.expect("only the last conjunct is the author's");
        term = SemanticTerm::application(
            semantic_origin(descriptor, key, "instance-guard-and")?,
            bool_sort.clone(),
            ApplicationRef::Builtin(BuiltinOperation::BoolAndThen),
            vec![conjunct, term],
        );
    }
    Ok(Some(SemanticCondition::Bool(SemanticRuleCondition::new(
        origin, term,
    ))))
}

impl From<Vec<Guard>> for SentenceGuards {
    fn from(guards: Vec<Guard>) -> Self {
        Self(guards)
    }
}
