use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CollectionApplication, CollectionOperandSort,
    CollectionResultSort, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorIndex, DescriptorPayload, DescriptorTerm, GeneratedOperation, ListNotation,
    ListOperation, OperationSort, ProductionFieldId, ProtocolCellContent, ProvenanceKey,
    SemanticId, SortTestKind, StableItemId,
};
use krs_ir_levels::{
    ListOperands, MapOperands, SemanticSortRef, SemanticTerm, SemanticVariable, SetOperands,
};

use super::catalog::{
    ProductionSignature, semantic_is_subsort, semantic_sort_closure, semantic_sort_ref,
};
use super::collection_types::{CollectionTyping, share_a_sort};
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};
use super::record_updates::Fill;

/// The reason given for `A | B` outside a left-hand side (KF-030).
const PATTERN_OR_OUTSIDE_LHS: &str = "`|` is a pattern alternative (K's #Or) and occurs only on a left-hand side; for Bool disjunction use `||`, bool::or, or k::or_bool!";

pub(super) struct StructuredTermBuilder<'a> {
    pub(super) descriptor: &'a Descriptor,
    pub(super) catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    pub(super) declarations: Option<&'a DescriptorIndex<'a>>,
    pub(super) k_item_sort: Option<SemanticSortRef>,
    pub(super) sort_parents: &'a BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    pub(super) binding_names: &'a BTreeSet<String>,
    pub(super) pattern_key: Option<&'a ProvenanceKey>,
    /// Finalized inferred sorts.
    pub(super) binding_sorts: BTreeMap<String, SemanticSortRef>,
    /// Author-declared and occurrence-derived upper-bound constraints.
    pub(super) binding_constraints: BTreeMap<String, BTreeSet<SemanticSortRef>>,
    /// The provenance key of each variable's first occurrence in the
    /// subject, where a diagnostic about its sort points.
    pub(super) subject_keys: BTreeMap<String, ProvenanceKey>,
    /// Typed binders of a term-shaped rule fn (KF-009): the declared sort,
    /// which every occurrence must accept, and its parameter-type key.
    pub(super) declared_binders: BTreeMap<String, (SemanticSortRef, ProvenanceKey)>,
    pub(super) wildcard_offset: usize,
    /// Generated variables of the sentence: wildcards, then (KF-031) the
    /// local binders of `k::matches!` patterns.
    pub(super) wildcards: Vec<SemanticVariable>,
    /// Whether wildcards may occur outside the subject: the result of a
    /// desugar clause that lists `_` in `unbound_variables` (KF-046).
    pub(super) result_wildcards: bool,
    /// Scopes of `k::matches!` local binders (BIND-1).
    pub(super) locals: LocalBinders,
    /// Whether the next term lowered is the head of an equation or rule,
    /// whose parametric instance its turbofish fixes (KF-027).
    pub(super) head_pending: bool,
    /// The builtin domain chosen for each operator (`a + b`).
    pub(super) operators: super::operators::OperatorInference,
    /// The sentence's record updates `Ctor { f: e, ..t }` (F5).
    pub(super) record_updates: super::record_updates::RecordUpdateState,
    /// The element types of the sentence's typed collections.
    pub(super) collections: CollectionUse<'a>,
}

/// The element types a builder infers against ([`CollectionTyping`]), and
/// the binders it reads from a typed collection, which are checked once
/// their sorts are resolved.
pub(super) struct CollectionUse<'a> {
    typing: &'a CollectionTyping,
    reads: Vec<(String, ProvenanceKey)>,
}

impl<'a> CollectionUse<'a> {
    pub(super) const fn new(typing: &'a CollectionTyping) -> Self {
        Self {
            typing,
            reads: Vec::new(),
        }
    }

    /// No typed collection: a sentence with no typed position.
    pub(super) fn none() -> Self {
        Self::new(CollectionTyping::empty())
    }

    /// The sort an element of a typed collection is inferred at, when
    /// `term` stands at an element position.
    pub(super) fn element_sort(&self, term: &DescriptorTerm) -> Option<SemanticSortRef> {
        self.typing.element(term).map(|site| site.sort.clone())
    }

    /// The element sort a projecting read returns, by its application key.
    pub(super) fn projection(
        &self,
        key: &ProvenanceKey,
    ) -> Option<&'a super::collection_types::ElementSite> {
        self.typing.projection(key)
    }
}

/// The local binders of a sentence's `k::matches!` patterns (BIND-1, KF-031).
#[derive(Default)]
pub(super) struct LocalBinders {
    /// The names of the pattern being inferred, if any.
    inferring: Option<BTreeSet<String>>,
    /// The inferred sort of each local binder, per `k::matches!` key.
    sorts: BTreeMap<ProvenanceKey, BTreeMap<String, SemanticSortRef>>,
    /// The identity and sort of each local binder of the pattern being
    /// lowered, if any.
    scope: Option<BTreeMap<String, (SemanticId, SemanticSortRef)>>,
    /// The sort of each local binder of a `let` pattern (KF-032), per `let`
    /// key; `None` is the value's sort (`let x = v`), known once lowered.
    let_sorts: BTreeMap<ProvenanceKey, BTreeMap<String, Option<SemanticSortRef>>>,
    /// The names bound by the enclosing `let` statements while inferring,
    /// innermost last.
    let_names: Vec<BTreeSet<String>>,
    /// The identity and sort of each name bound by the enclosing `let`
    /// statements while lowering, innermost last.
    let_scopes: Vec<BTreeMap<String, (SemanticId, SemanticSortRef)>>,
}

/// Whether a record may leave fields out, and why: a pattern's omitted
/// fields are unconstrained, and an update's are its base's (F5).
#[derive(Clone, Copy)]
pub(super) struct Partial<'a> {
    pub(super) subject: bool,
    pub(super) update: Option<&'a DescriptorTerm>,
    /// Whether the record is a pattern ending in `..`, which may name no
    /// field at all, `Ctor { .. }`.
    pub(super) open: bool,
}

impl<'a> Partial<'a> {
    pub(super) const fn new(subject: bool, update: Option<&'a DescriptorTerm>, open: bool) -> Self {
        Self {
            subject,
            update,
            open,
        }
    }

    /// The record's arguments in field order, a field it leaves out `None`.
    fn ordered<'b>(
        self,
        arguments: &'b krs_ir::Arguments<krs_ir::DescriptorStage>,
        fields: &[(ProductionFieldId, SemanticSortRef)],
    ) -> Result<Vec<Option<&'b DescriptorTerm>>, String> {
        order_record_arguments(
            arguments,
            fields,
            self.subject || self.update.is_some(),
            self.update.is_some() || (self.subject && self.open),
        )
    }
}

/// The record a term lowers: in a pattern the alias it is the record of,
/// if that alias is a record update's base, and in a result its update's
/// base (F5).
pub(super) struct RecordContext<'a> {
    pub(super) alias: Option<String>,
    pub(super) update: Option<&'a DescriptorTerm>,
    pub(super) subject: bool,
    /// Whether the record is a pattern ending in `..` ([`Partial::open`]).
    pub(super) open: bool,
}

impl RecordContext<'_> {
    /// The record's arguments in field order, a field it leaves out `None`.
    fn ordered<'a>(
        &self,
        arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
        fields: &[(ProductionFieldId, SemanticSortRef)],
    ) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
        order_record_arguments(
            arguments,
            fields,
            self.subject || self.update.is_some(),
            self.update.is_some() || (self.subject && self.open),
        )
    }
}

/// The reason given for a `let` block in a pattern (KF-032).
const LET_IN_PATTERN: &str =
    "a `let` block (K's #let) is a term; it cannot appear on a left-hand side or inside a pattern";

impl StructuredTermBuilder<'_> {
    /// Infers the sorts of `term`'s binders against `expected_sort`
    /// ([`Self::infer_term`]), locating an invalid-term error at the
    /// innermost term with an authored range.
    pub(super) fn infer(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        self.check_element(term)?;
        self.infer_term(term, expected_sort, subject)
            .map_err(|error| self.locate(error, term))
    }

    /// Rejects a term stored in a typed collection whose stated sort is not
    /// the element sort. A binder's sort is inferred with its other
    /// occurrences instead, and [`Self::resolve_binding_sorts`] names the
    /// element position when they disagree.
    fn check_element(&self, term: &DescriptorTerm) -> Result<(), DescriptorLoweringError> {
        let Some(site) = self.collections.typing.element(term) else {
            return Ok(());
        };
        if matches!(term, DescriptorTerm::Variable { .. })
            || matches!(term, DescriptorTerm::Rewrite { .. })
        {
            return Ok(());
        }
        match self.stated_sort(term) {
            Some(stated) if !semantic_is_subsort(&stated, &site.sort, self.sort_parents) => {
                Err(super::collection_types::element_mismatch(
                    self.descriptor,
                    site,
                    &super::collection_types::spelling(term),
                    &super::overload::sort_name(&stated),
                    Self::term_key(term),
                ))
            }
            _ => Ok(()),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive inference over the closed descriptor term sum."
    )]
    fn infer_term(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        match term {
            // A name an enclosing `let` binds is local (KF-032): its sort is
            // checked when it is lowered.
            DescriptorTerm::Variable { name, .. }
                if !self.is_inferring_local(name) && self.is_let_local(name) => {}
            DescriptorTerm::Variable { key, name, .. } => {
                if !self.binding_names.contains(name) && !self.is_inferring_local(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                if subject {
                    self.subject_keys
                        .entry(name.clone())
                        .or_insert_with(|| key.clone());
                }
                if let Some(expected) = expected_sort {
                    self.check_declared_binder(name, expected)?;
                    self.binding_constraints
                        .entry(name.clone())
                        .or_default()
                        .insert(expected.clone());
                }
            }
            DescriptorTerm::Wildcard { .. } => {
                if !subject && !self.result_wildcards {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                if expected_sort.is_none() {
                    return Err(self.invalid_term("wildcard has no expected production-field sort"));
                }
            }
            DescriptorTerm::Literal { literal, .. } => {
                let (sort, spelling) = match literal {
                    krs_ir::DescriptorLiteral::Int(value) => (BuiltinSort::Int, value.clone()),
                    krs_ir::DescriptorLiteral::Bool(value) => {
                        (BuiltinSort::Bool, value.to_string())
                    }
                    krs_ir::DescriptorLiteral::String(value) => {
                        (BuiltinSort::String, format!("{value:?}"))
                    }
                    krs_ir::DescriptorLiteral::Float(token) => (BuiltinSort::Float, token.clone()),
                };
                let sort = SemanticSortRef::Builtin(sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "literal `{spelling}` of sort {sort} is not admissible at sort {expected}"
                    )));
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                instance,
                update,
                open,
                ..
            } => self.infer_application(
                reference,
                arguments,
                instance,
                expected_sort,
                Partial::new(subject, update.as_deref(), *open),
            )?,
            DescriptorTerm::BuiltinToken { sort, .. } => {
                let sort = SemanticSortRef::Builtin(*sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("builtin token has an incompatible sort"));
                }
            }
            DescriptorTerm::Anonymous { sort, .. } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("anonymous occurrence has an incompatible sort"));
                }
            }
            DescriptorTerm::Lexeme { key, sort, text } => {
                let sort = self.lexeme_sort(key, sort, text)?;
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "`k::lexeme!` token {text:?} has sort {sort}, which is not admissible at sort {expected}"
                    )));
                }
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                if arguments.len() < 2 {
                    return Err(self.invalid_term("or_bool requires at least two operands"));
                }
                let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&bool_sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term("or_bool is not admissible at the expected sort"));
                }
                for argument in arguments {
                    self.infer(argument, Some(&bool_sort), subject)?;
                }
            }
            DescriptorTerm::Cell {
                declaration,
                fields,
                open,
                update,
                ..
            } => {
                let k_item = self.cell_k_item_sort()?;
                let whole_group = expected_sort.is_some_and(|expected| {
                    *expected == SemanticSortRef::Cell(declaration.clone())
                });
                if let Some(expected) = expected_sort
                    && !whole_group
                    && !semantic_is_subsort(&k_item, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(
                        "complete cell term is not admissible at the expected sort",
                    ));
                }
                // A `..` pattern leaves children unconstrained, and an update
                // takes them from its base (F5).
                let partial = *open || update.is_some();
                self.infer_cell_fields(declaration, fields, subject, partial)?;
            }
            DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand,
            } => {
                let result = self.sort_test_result(key, *kind, sort, subject)?;
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&result, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "{} has sort {result}, which is not admissible at sort {expected}",
                        sort_test_macro(*kind)
                    )));
                }
                let operand_sort = self.sort_test_operand_sort(operand);
                self.infer(operand, operand_sort.as_ref(), subject)?;
            }
            DescriptorTerm::As {
                key, name, pattern, ..
            } => {
                if !subject {
                    return Err(self.invalid_pattern_as(
                        key,
                        format!(
                            "`{name} @ ..` binds only on a left-hand side (K's #as is LHS-only); refer to `{name}` here without `@`"
                        ),
                    ));
                }
                if !self.binding_names.contains(name) && !self.is_inferring_local(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                if let Some(expected) = expected_sort {
                    self.check_declared_binder(name, expected)?;
                    self.binding_constraints
                        .entry(name.clone())
                        .or_default()
                        .insert(expected.clone());
                }
                // The alias names the term the pattern matched, so it is
                // bounded by the pattern's own sort as well as the position's.
                if let Some(sort) = self.pattern_head_sort(pattern) {
                    self.binding_constraints
                        .entry(name.clone())
                        .or_default()
                        .insert(sort);
                }
                self.infer(pattern, expected_sort, subject)?;
            }
            DescriptorTerm::Or { key, alternatives } => {
                self.infer_pattern_or(key, alternatives, expected_sort, subject)?;
            }
            DescriptorTerm::Matches {
                key,
                subject: tested,
                pattern,
            } => self.infer_matches(key, tested, pattern, expected_sort, subject)?,
            DescriptorTerm::Let {
                key,
                pattern,
                sort,
                value,
                body,
            } => self.infer_let(
                key,
                pattern,
                sort.as_ref(),
                value,
                body,
                expected_sort,
                subject,
            )?,
            // A closure is only the operand of `ml::exists`, which
            // `infer_predicate` reads (KF-039).
            DescriptorTerm::Closure { key, .. } => {
                return Err(self.invalid_ml(
                    key,
                    "closures introduce quantified binders only inside ml::exists".to_owned(),
                ));
            }
            DescriptorTerm::Rewrite { key, from, to, .. } => {
                if !subject {
                    return Err(self.invalid_local_rewrite(
                        key,
                        "`k::rewrite!` (K's local =>) occurs only in a single-body rule's subject"
                            .to_owned(),
                    ));
                }
                // Both images are inferred: the left side binds like the
                // subject, the right side uses its bindings (KF-011).
                let (from_sort, to_sort) =
                    self.rewrite_side_sorts(expected_sort, from, to.as_deref());
                self.infer(from, from_sort.as_ref(), true)?;
                if let Some(to) = to {
                    self.infer(to, to_sort.as_ref(), false)?;
                }
            }
        }
        Ok(())
    }

    /// Whether an enclosing `let` or `ml::exists` binds `name`, while
    /// inferring or lowering.
    pub(super) fn is_let_local_name(&self, name: &str) -> bool {
        self.is_let_local(name) || self.let_local(name).is_some()
    }

    /// Enters the scope of local binder names while inferring: a `let`
    /// body's, or an `ml::exists` closure's (KF-039).
    pub(super) fn push_let_names(&mut self, names: BTreeSet<String>) {
        self.locals.let_names.push(names);
    }

    /// Leaves the innermost scope [`Self::push_let_names`] entered.
    pub(super) fn pop_let_names(&mut self) {
        self.locals.let_names.pop();
    }

    /// Enters the scope of local binders while lowering.
    pub(super) fn push_let_scope(
        &mut self,
        scope: BTreeMap<String, (SemanticId, SemanticSortRef)>,
    ) {
        self.locals.let_scopes.push(scope);
    }

    /// Leaves the innermost scope [`Self::push_let_scope`] entered.
    pub(super) fn pop_let_scope(&mut self) {
        self.locals.let_scopes.pop();
    }

    /// The sorts the sides of a `k::rewrite!` are inferred at (KF-011): the
    /// position's when it has one; otherwise each side has its own sort, and
    /// a bare `_` on the left takes the sort the right side states, as in
    /// `name -> k::rewrite!(_ => value)`.
    fn rewrite_side_sorts(
        &self,
        expected_sort: Option<&SemanticSortRef>,
        from: &DescriptorTerm,
        to: Option<&DescriptorTerm>,
    ) -> (Option<SemanticSortRef>, Option<SemanticSortRef>) {
        if let Some(expected) = expected_sort {
            return (Some(expected.clone()), Some(expected.clone()));
        }
        let from_sort = matches!(from, DescriptorTerm::Wildcard { .. })
            .then(|| to.and_then(|to| self.stated_sort(to)))
            .flatten();
        (from_sort, None)
    }

    /// The sort a term states without inference: a binder's declared or
    /// already-resolved sort, a declared constructor's result, or a literal's.
    fn stated_sort(&self, term: &DescriptorTerm) -> Option<SemanticSortRef> {
        match term {
            DescriptorTerm::Variable { name, .. } => self
                .declared_binders
                .get(name)
                .map(|(sort, _)| sort.clone())
                .or_else(|| self.binding_sorts.get(name).cloned())
                .or_else(|| {
                    self.binding_constraints
                        .get(name)
                        .filter(|sorts| sorts.len() == 1)
                        .and_then(|sorts| sorts.first().cloned())
                }),
            DescriptorTerm::Literal { literal, .. } => {
                Some(SemanticSortRef::Builtin(match literal {
                    krs_ir::DescriptorLiteral::Int(_) => BuiltinSort::Int,
                    krs_ir::DescriptorLiteral::Bool(_) => BuiltinSort::Bool,
                    krs_ir::DescriptorLiteral::String(_) => BuiltinSort::String,
                    krs_ir::DescriptorLiteral::Float(_) => BuiltinSort::Float,
                }))
            }
            _ => self.pattern_head_sort(term),
        }
    }

    /// Lowers `k::rewrite!(from => to)` (KF-011) at the join of its sides'
    /// sorts; `()` on the right is `.K`, which removes a K-sequence item and
    /// keeps the item's sort.
    fn lower_rewrite(
        &mut self,
        key: &ProvenanceKey,
        to_key: &ProvenanceKey,
        from: &DescriptorTerm,
        to: Option<&DescriptorTerm>,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let (from_sort, to_sort) = self.rewrite_side_sorts(expected_sort, from, to);
        let from = self.lower(from, from_sort.as_ref(), true)?;
        let (sort, to) = match to {
            Some(to) => {
                let to = self.lower(to, to_sort.as_ref(), false)?;
                let sort = match expected_sort {
                    Some(expected) => expected.clone(),
                    None => self.join_sort(from.sort(), to.sort()).ok_or_else(|| {
                        self.invalid_local_rewrite(
                            key,
                            format!(
                                "the sides of `k::rewrite!` have sorts `{}` and `{}`, which share no sort",
                                super::overload::sort_name(from.sort()),
                                super::overload::sort_name(to.sort())
                            ),
                        )
                    })?,
                };
                (sort, to)
            }
            None => (
                from.sort().clone(),
                SemanticTerm::k_sequence(
                    semantic_origin(self.descriptor, to_key.clone(), "rule-local-rewrite-dot-k")?,
                    SemanticSortRef::k_sequence(),
                    Vec::new(),
                ),
            ),
        };
        Ok(SemanticTerm::rewrite(
            semantic_origin(self.descriptor, key.clone(), "rule-local-rewrite")?,
            sort,
            from,
            to,
        )?)
    }

    /// The least sort both `left` and `right` inject into, if there is one.
    fn join_sort(
        &self,
        left: &SemanticSortRef,
        right: &SemanticSortRef,
    ) -> Option<SemanticSortRef> {
        let mut common = semantic_sort_closure(left, self.sort_parents);
        let right = semantic_sort_closure(right, self.sort_parents);
        common.retain(|sort| right.contains(sort));
        let least = common
            .iter()
            .filter(|candidate| {
                !common.iter().any(|other| {
                    other != *candidate && semantic_is_subsort(other, candidate, self.sort_parents)
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        match least.as_slice() {
            [sort] => Some(sort.clone()),
            _ => None,
        }
    }

    fn invalid_local_rewrite(
        &self,
        key: &ProvenanceKey,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidLocalRewrite {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    /// Whether an enclosing `let` statement binds `name` (KF-032).
    fn is_let_local(&self, name: &str) -> bool {
        self.locals
            .let_names
            .iter()
            .any(|names| names.contains(name))
    }

    /// Infers one `let pattern = value;` statement and the rest of its block
    /// (K's `#let`, KF-032), a term at its body's sort outside every
    /// pattern. The pattern's names are local binders (BIND-1) scoped over
    /// the pattern and the body; the value is outside their scope. A bare
    /// `let x = v` (or `let _ = v`) takes the ascribed sort or the value's;
    /// a constructor pattern's names take their sorts from the pattern.
    #[expect(
        clippy::too_many_arguments,
        reason = "One `let` statement has five parts besides the builder state."
    )]
    fn infer_let(
        &mut self,
        key: &ProvenanceKey,
        pattern: &DescriptorTerm,
        sort: Option<&krs_ir::DescriptorSortReference>,
        value: &DescriptorTerm,
        body: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if subject || self.locals.inferring.is_some() || self.locals.scope.is_some() {
            return Err(self.invalid_let(key, LET_IN_PATTERN.to_owned()));
        }
        let ascribed = sort.map(|sort| semantic_sort_ref(&sort.sort));
        let mut occurrences = Vec::new();
        pattern_names(pattern, &mut occurrences);
        let names = occurrences
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let mut sorts = BTreeMap::new();
        if is_bare_let_pattern(pattern) {
            for name in &names {
                sorts.insert(name.clone(), ascribed.clone());
            }
        } else {
            let outer = std::mem::take(&mut self.binding_constraints);
            self.locals.inferring = Some(names.clone());
            let inferred = self.infer(pattern, ascribed.as_ref(), true);
            self.locals.inferring = None;
            let constraints = std::mem::replace(&mut self.binding_constraints, outer);
            inferred?;
            for name in &names {
                let candidates = constraints
                    .get(name)
                    .map(|constraints| {
                        most_specific_common_descendants(constraints, self.sort_parents)
                    })
                    .unwrap_or_default();
                let [sort] = candidates.as_slice() else {
                    return Err(self.invalid_let(
                        key,
                        format!("`{name}` in this `let` pattern has no single sort its occurrences share"),
                    ));
                };
                sorts.insert(name.clone(), Some(sort.clone()));
            }
        }
        self.locals.let_sorts.insert(key.clone(), sorts);
        self.infer(value, None, false)?;
        self.locals.let_names.push(names);
        let inferred = self.infer(body, expected_sort, false);
        self.locals.let_names.pop();
        inferred
    }

    /// Lowers one `let` statement with fresh identities for the pattern's
    /// local binders, which join the sentence's variables, so a name that
    /// shadows an outer binder is a distinct variable.
    fn lower_let(
        &mut self,
        key: &ProvenanceKey,
        pattern: &DescriptorTerm,
        sort: Option<&krs_ir::DescriptorSortReference>,
        value: &DescriptorTerm,
        body: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let value = self.lower(value, None, false)?;
        let ascribed = sort.map(|sort| semantic_sort_ref(&sort.sort));
        let sorts = self.locals.let_sorts.get(key).cloned().unwrap_or_default();
        let mut occurrences = Vec::new();
        pattern_names(pattern, &mut occurrences);
        let mut scope = BTreeMap::new();
        let mut binds = Vec::new();
        for (name, _) in occurrences {
            if scope.contains_key(&name) {
                continue;
            }
            let sort = sorts
                .get(&name)
                .cloned()
                .flatten()
                .unwrap_or_else(|| value.sort().clone());
            let id = SemanticId::local(&name, self.wildcard_offset + self.wildcards.len())?;
            self.wildcards
                .push(SemanticVariable::new(id.clone(), sort.clone()));
            binds.push(id.clone());
            scope.insert(name, (id, sort));
        }
        let pattern_sort =
            ascribed.or_else(|| is_bare_let_pattern(pattern).then(|| value.sort().clone()));
        self.locals.scope = Some(scope.clone());
        let lowered = self.lower(pattern, pattern_sort.as_ref(), true);
        self.locals.scope = None;
        let lowered = lowered?;
        let meets = most_specific_common_descendants(
            &BTreeSet::from([value.sort().clone(), lowered.sort().clone()]),
            self.sort_parents,
        );
        if meets.is_empty() {
            return Err(self.invalid_let(
                key,
                format!(
                    "the pattern has sort `{}` and the value has sort `{}`, which share no subsort, so this `let` is always undefined",
                    super::overload::sort_name(lowered.sort()),
                    super::overload::sort_name(value.sort())
                ),
            ));
        }
        self.locals.let_scopes.push(scope);
        let body = self.lower(body, expected_sort, false);
        self.locals.let_scopes.pop();
        let body = body?;
        Ok(SemanticTerm::let_binding(
            semantic_origin(self.descriptor, key.clone(), "term-let")?,
            body.sort().clone(),
            lowered,
            value,
            body,
            binds,
        ))
    }

    /// The identity and sort of `name` if an enclosing `let` binds it.
    fn let_local(&self, name: &str) -> Option<(SemanticId, SemanticSortRef)> {
        self.locals
            .let_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    fn invalid_let(&self, key: &ProvenanceKey, reason: String) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidLet {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    pub(super) fn is_inferring_local(&self, name: &str) -> bool {
        self.locals
            .inferring
            .as_ref()
            .is_some_and(|names| names.contains(name))
    }

    /// Infers `k::matches!(subject, pattern)` (K's `:=K`, KF-031): a Bool
    /// outside every pattern. The pattern's names are local binders
    /// (BIND-1): none may be a rule binder, which K would silently shadow,
    /// and each must be read twice (a name read once is `_`). Their sorts
    /// are inferred from the pattern alone.
    fn infer_matches(
        &mut self,
        key: &ProvenanceKey,
        tested: &DescriptorTerm,
        pattern: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if subject || self.locals.inferring.is_some() || self.locals.scope.is_some() {
            return Err(self.invalid_matches(
                key,
                "`k::matches!` is a Bool test (K's :=K); it cannot appear on a left-hand side or inside a pattern".to_owned(),
            ));
        }
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&bool_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "`k::matches!` has sort Bool, which is not admissible at sort {expected}"
            )));
        }
        self.infer(tested, None, false)?;
        let mut occurrences = Vec::new();
        pattern_names(pattern, &mut occurrences);
        let mut counts = BTreeMap::<&str, usize>::new();
        for (name, _) in &occurrences {
            *counts.entry(name.as_str()).or_default() += 1;
        }
        for (name, occurrence) in &occurrences {
            if self.binding_names.contains(name)
                || self.declared_binders.contains_key(name)
                || self.is_let_local(name)
                || self.let_local(name).is_some()
            {
                return Err(self.invalid_matches(
                    occurrence,
                    format!(
                        "`{name}` in k::matches! binds a new variable; it does not compare with the rule's `{name}`. Use int::eq/bool::eq, or write `_`"
                    ),
                ));
            }
        }
        for (name, occurrence) in &occurrences {
            if counts.get(name.as_str()) == Some(&1) {
                return Err(
                    self.invalid_matches(occurrence, format!("`{name}` is never read; write `_`"))
                );
            }
        }
        let names = counts
            .keys()
            .map(|name| (*name).to_owned())
            .collect::<BTreeSet<_>>();
        let outer = std::mem::take(&mut self.binding_constraints);
        self.locals.inferring = Some(names.clone());
        let inferred = self.infer(pattern, None, true);
        self.locals.inferring = None;
        let constraints = std::mem::replace(&mut self.binding_constraints, outer);
        inferred?;
        let mut sorts = BTreeMap::new();
        for name in names {
            let candidates = constraints
                .get(&name)
                .map(|constraints| most_specific_common_descendants(constraints, self.sort_parents))
                .unwrap_or_default();
            let [sort] = candidates.as_slice() else {
                return Err(self.invalid_matches(
                    key,
                    format!("`{name}` in k::matches! has no single sort its occurrences share"),
                ));
            };
            sorts.insert(name, sort.clone());
        }
        self.locals.sorts.insert(key.clone(), sorts);
        Ok(())
    }

    /// Lowers `k::matches!(subject, pattern)` with fresh identities for the
    /// pattern's local binders, which join the sentence's variables.
    fn lower_matches(
        &mut self,
        key: &ProvenanceKey,
        tested: &DescriptorTerm,
        pattern: &DescriptorTerm,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let tested = self.lower(tested, None, false)?;
        let sorts = self.locals.sorts.get(key).cloned().unwrap_or_default();
        let mut occurrences = Vec::new();
        pattern_names(pattern, &mut occurrences);
        let mut scope = BTreeMap::new();
        let mut binds = Vec::new();
        for (name, _) in occurrences {
            if scope.contains_key(&name) {
                continue;
            }
            let sort = sorts.get(&name).cloned().ok_or_else(|| {
                self.invalid_term(format!("local binder {name:?} has no inferred sort"))
            })?;
            let id = SemanticId::local(&name, self.wildcard_offset + self.wildcards.len())?;
            self.wildcards
                .push(SemanticVariable::new(id.clone(), sort.clone()));
            binds.push(id.clone());
            scope.insert(name, (id, sort));
        }
        self.locals.scope = Some(scope);
        let lowered = self.lower(pattern, None, true);
        self.locals.scope = None;
        let lowered = lowered?;
        let meets = most_specific_common_descendants(
            &BTreeSet::from([tested.sort().clone(), lowered.sort().clone()]),
            self.sort_parents,
        );
        if meets.is_empty() {
            return Err(self.invalid_matches(
                key,
                format!(
                    "the pattern has sort `{}` and the subject has sort `{}`, which share no subsort, so this test is always false",
                    super::overload::sort_name(lowered.sort()),
                    super::overload::sort_name(tested.sort())
                ),
            ));
        }
        Ok(SemanticTerm::matches(
            semantic_origin(self.descriptor, key.clone(), "term-matches")?,
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            tested,
            lowered,
            binds,
        ))
    }

    fn invalid_matches(&self, key: &ProvenanceKey, reason: String) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidMatches {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    /// Infers `A | B | ..` (K's `#Or`, KF-030): every alternative sits at
    /// the or-pattern's position, and a name every alternative binds must
    /// have the same sort in each of them.
    fn infer_pattern_or(
        &mut self,
        key: &ProvenanceKey,
        alternatives: &krs_ir::AtLeastTwo<DescriptorTerm>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if !subject {
            return Err(self.invalid_pattern_or(key, PATTERN_OR_OUTSIDE_LHS.to_owned()));
        }
        let outer = std::mem::take(&mut self.binding_constraints);
        let mut per_alternative = Vec::with_capacity(alternatives.len());
        for alternative in alternatives {
            let inferred = self.infer(alternative, expected_sort, subject);
            per_alternative.push(std::mem::take(&mut self.binding_constraints));
            if let Err(error) = inferred {
                self.binding_constraints = outer;
                return Err(error);
            }
        }
        self.binding_constraints = outer;
        for constraints in &per_alternative {
            for (name, sorts) in constraints {
                self.binding_constraints
                    .entry(name.clone())
                    .or_default()
                    .extend(sorts.iter().cloned());
            }
        }
        let (first, rest) = per_alternative
            .split_first()
            .expect("an or-pattern has at least two alternatives");
        for other in rest {
            for (name, sorts) in first {
                let Some(other_sorts) = other.get(name) else {
                    continue;
                };
                let here = most_specific_common_descendants(sorts, self.sort_parents);
                let there = most_specific_common_descendants(other_sorts, self.sort_parents);
                if here != there {
                    let show = |sorts: &[SemanticSortRef]| {
                        sorts
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" or ")
                    };
                    return Err(self.invalid_pattern_or(
                        key,
                        format!(
                            "`{name}` has sort {} in one alternative and sort {} in another; every alternative must bind it at one sort",
                            show(&here),
                            show(&there)
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    /// Lowers `A | B | ..` at the least common sort of its alternatives.
    fn lower_pattern_or(
        &mut self,
        key: &ProvenanceKey,
        alternatives: &krs_ir::AtLeastTwo<DescriptorTerm>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if !subject {
            return Err(self.invalid_pattern_or(key, PATTERN_OR_OUTSIDE_LHS.to_owned()));
        }
        let lowered = alternatives
            .try_map_ref(|alternative| self.lower(alternative, expected_sort, subject))?;
        let sorts = lowered
            .iter()
            .map(|alternative| semantic_sort_closure(alternative.sort(), self.sort_parents))
            .collect::<Vec<_>>();
        let mut common = sorts[0].clone();
        for closure in &sorts[1..] {
            common.retain(|candidate| closure.contains(candidate));
        }
        let least = common
            .iter()
            .filter(|candidate| {
                !common.iter().any(|other| {
                    other != *candidate && semantic_is_subsort(other, candidate, self.sort_parents)
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        let [sort] = least.as_slice() else {
            return Err(self.invalid_pattern_or(
                key,
                format!(
                    "the alternatives (of sorts {}) have no single least common sort",
                    lowered
                        .iter()
                        .map(|alternative| alternative.sort().to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            ));
        };
        Ok(SemanticTerm::pattern_or(
            semantic_origin(self.descriptor, key.clone(), "term-pattern-or")?,
            sort.clone(),
            lowered,
        ))
    }

    /// The result sort of a declared constructor at the root of an aliased
    /// pattern, which bounds the alias's sort.
    fn pattern_head_sort(&self, pattern: &DescriptorTerm) -> Option<SemanticSortRef> {
        match pattern {
            DescriptorTerm::Application {
                reference:
                    DescriptorApplicationReference {
                        application: DescriptorApplicationRef::Declared(id),
                        ..
                    },
                ..
            } => self
                .catalog
                .get(id)
                .map(|signature| signature.result_sort.clone()),
            // A group pattern matches the whole nested cell (KF-016).
            DescriptorTerm::Cell { declaration, .. } => {
                Some(SemanticSortRef::Cell(declaration.clone()))
            }
            DescriptorTerm::As { pattern, .. } => self.pattern_head_sort(pattern),
            _ => None,
        }
    }

    fn invalid_pattern_or(&self, key: &ProvenanceKey, reason: String) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidPatternOr {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    fn invalid_pattern_as(&self, key: &ProvenanceKey, reason: String) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidPatternAs {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One dispatch over every application head kind."
    )]
    pub(super) fn infer_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        partial: Partial<'_>,
    ) -> Result<(), DescriptorLoweringError> {
        let subject = partial.subject;
        self.reject_misplaced_turbofish(reference, instance)?;
        if let DescriptorApplicationRef::Declared(id) = &reference.application
            && let Some(signature) = self.catalog.get(id)
            && !signature.parameters.is_empty()
        {
            let signature = signature.clone();
            return self.infer_parametric(
                reference,
                &signature,
                arguments,
                instance,
                expected_sort,
                partial,
            );
        }
        let signature = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id} has no grammar production"
                    ))
                })?
            }
            DescriptorApplicationRef::Builtin(operation) if operation.is_sort_generic() => {
                return self.infer_generic_builtin(*operation, arguments, expected_sort, subject);
            }
            DescriptorApplicationRef::Builtin(operation) => {
                builtin_production_signature(*operation)
                    .ok_or_else(|| self.sort_generic_builtin(*operation))?
            }
            DescriptorApplicationRef::Map(operation) => {
                self.infer_collection_operation(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                return Ok(());
            }
            DescriptorApplicationRef::List(operation) => {
                self.infer_collection_operation(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                return Ok(());
            }
            DescriptorApplicationRef::Set(operation) => {
                self.infer_collection_operation(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                return Ok(());
            }
            DescriptorApplicationRef::Ml(connective) => {
                return Err(self.ml_in_object_term(&reference.key, *connective));
            }
            DescriptorApplicationRef::Operator(operator) => {
                return self.infer_operator(
                    reference,
                    *operator,
                    arguments,
                    expected_sort,
                    subject,
                );
            }
            DescriptorApplicationRef::ListNotation(ListNotation::Cons | ListNotation::Snoc) => {
                return self.infer_list_spine(reference, arguments, expected_sort, subject);
            }
            DescriptorApplicationRef::ListNotation(notation) => {
                let reference = self.list_constructor(reference, *notation, expected_sort)?;
                return self.infer_application(
                    &reference,
                    arguments,
                    instance,
                    expected_sort,
                    partial,
                );
            }
        };
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&signature.result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "application result sort {} is not admissible at sort {expected}",
                signature.result_sort
            )));
        }
        let ordered = partial
            .ordered(arguments, &signature.fields)
            .map_err(|detail| self.invalid_term(detail))?;
        for (argument, (_, sort)) in ordered.into_iter().zip(&signature.fields) {
            if let Some(argument) = argument {
                self.infer(argument, Some(sort), subject)?;
            }
        }
        Ok(())
    }

    /// The sort each argument of a sort-generic builtin is inferred and lowered
    /// at: its builtin sort, nothing for `K`, and for `Parameter` the sort
    /// expected of a `Parameter` result, an upper bound of the instance.
    fn generic_argument_sorts(
        &self,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<Vec<Option<SemanticSortRef>>, DescriptorLoweringError> {
        let spec = operation.spec();
        if arguments.len() != spec.argument_sorts.len() || arguments.is_named() {
            return Err(self.invalid_term(format!(
                "the {operation} operation expects {} positional arguments",
                spec.argument_sorts.len()
            )));
        }
        let parameter_bound = match spec.result_sort {
            OperationSort::Parameter => expected_sort.cloned(),
            OperationSort::Builtin(_) | OperationSort::K => None,
        };
        Ok(spec
            .argument_sorts
            .iter()
            .map(|sort| match sort {
                OperationSort::Builtin(sort) => Some(SemanticSortRef::Builtin(*sort)),
                OperationSort::K => None,
                OperationSort::Parameter => parameter_bound.clone(),
            })
            .collect())
    }

    fn infer_generic_builtin(
        &mut self,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if let OperationSort::Builtin(result) = operation.result_sort()
            && let Some(expected) = expected_sort
            && !semantic_is_subsort(
                &SemanticSortRef::Builtin(result),
                expected,
                self.sort_parents,
            )
        {
            return Err(self.invalid_term(format!(
                "application result sort {} is not admissible at sort {expected}",
                SemanticSortRef::Builtin(result)
            )));
        }
        let sorts = self.generic_argument_sorts(operation, arguments, expected_sort)?;
        for (argument, sort) in arguments.iter().zip(&sorts) {
            if let krs_ir::TermArgumentRef::Positional { value } = argument {
                self.infer(value, sort.as_ref(), subject)?;
            }
        }
        Ok(())
    }

    fn lower_generic_builtin(
        &mut self,
        reference: &DescriptorApplicationReference,
        operation: BuiltinOperation,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let sorts = self.generic_argument_sorts(operation, arguments, expected_sort)?;
        let mut lowered = Vec::with_capacity(sorts.len());
        for (argument, sort) in arguments.iter().zip(&sorts) {
            if let krs_ir::TermArgumentRef::Positional { value } = argument {
                lowered.push(self.lower(value, sort.as_ref(), subject)?);
            }
        }
        let result_sort = match operation.result_sort() {
            OperationSort::Builtin(sort) => SemanticSortRef::Builtin(sort),
            OperationSort::Parameter => {
                let branches = lowered
                    .iter()
                    .zip(operation.argument_sorts())
                    .filter(|(_, sort)| **sort == OperationSort::Parameter)
                    .map(|(argument, _)| argument.sort().clone())
                    .collect::<Vec<_>>();
                least_instance(&branches, expected_sort, self.sort_parents)
                    .map_err(|error| self.invalid_term(error.message(operation, &branches)))?
            }
            // K's `K` sort: the computation the operation evaluates to (`.K`).
            OperationSort::K => SemanticSortRef::Builtin(BuiltinSort::KSequence),
        };
        Ok(SemanticTerm::application(
            semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
            result_sort,
            ApplicationRef::Builtin(operation),
            lowered,
        ))
    }

    fn infer_collection_operation<O: CollectionApplication>(
        &mut self,
        key: &ProvenanceKey,
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(key, operation, expected_sort)?;
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "{} operation result sort {result_sort} is not admissible at sort {expected}",
                O::SORT.k_name()
            )));
        }
        // A read of a typed collection at a position whose sort its
        // elements never have can never succeed.
        if let (Some(expected), Some(site)) =
            (expected_sort, self.collections.typing.projection(key))
            && !share_a_sort(&site.sort, expected, self.sort_parents)
        {
            let marker = operation.facade_marker();
            return Err(super::collection_types::disjoint_read(
                self.descriptor,
                site,
                &format!("`{}::{}(..)`", marker.module, marker.name),
                expected,
                key,
            ));
        }
        for (operand, sort) in operands.into_iter().zip(operation.spec().operand_sorts) {
            let expected = self.collection_operand_expected(operand, *sort)?;
            self.infer(operand, expected.as_ref(), subject)?;
        }
        Ok(())
    }

    /// The sort an element of a typed collection is lowered at, if `term`
    /// is one.
    pub(super) fn collection_element_sort(&self, term: &DescriptorTerm) -> Option<SemanticSortRef> {
        self.collections
            .typing
            .element(term)
            .map(|site| site.sort.clone())
    }

    /// The sort an operand is inferred at: its row's builtin sort, or for an
    /// element of a typed collection its element sort. A probe into a typed
    /// collection must share a sort with its elements.
    pub(super) fn collection_operand_expected(
        &mut self,
        operand: &DescriptorTerm,
        sort: CollectionOperandSort,
    ) -> Result<Option<SemanticSortRef>, DescriptorLoweringError> {
        if let Some(sort) = collection_operand_sort(sort) {
            return Ok(Some(sort));
        }
        let typing = self.collections.typing;
        if let Some(read) = typing.read(operand) {
            match operand {
                DescriptorTerm::Variable { name, key, .. } if !self.is_let_local_name(name) => {
                    self.collections.reads.push((name.clone(), key.clone()));
                }
                _ => {
                    if let Some(stated) = self.stated_sort(operand)
                        && !share_a_sort(&stated, &read.sort, self.sort_parents)
                    {
                        return Err(super::collection_types::disjoint_read(
                            self.descriptor,
                            read,
                            &format!(
                                "`{}` of sort {}",
                                super::collection_types::spelling(operand),
                                super::overload::sort_name(&stated)
                            ),
                            &stated,
                            Self::term_key(operand),
                        ));
                    }
                }
            }
            return Ok(None);
        }
        Ok(typing.element(operand).map(|site| site.sort.clone()))
    }

    /// Lowers a collection application's operands, in wire order, with its result sort.
    fn lower_collection_operands<O: CollectionApplication>(
        &mut self,
        key: &ProvenanceKey,
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(SemanticSortRef, Vec<SemanticTerm>), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(key, operation, expected_sort)?;
        let typing = self.collections.typing;
        let lowered = operands
            .into_iter()
            .zip(operation.spec().operand_sorts)
            .map(|(operand, sort)| {
                let expected = collection_operand_sort(*sort).or_else(|| {
                    typing
                        .read(operand)
                        .is_none()
                        .then(|| typing.element(operand).map(|site| site.sort.clone()))
                        .flatten()
                });
                self.lower(operand, expected.as_ref(), subject)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok((result_sort, lowered))
    }

    /// The result sort of a collection application: its row's, or for a
    /// projecting read the sort its position expects, and with no position
    /// the element sort of the typed collection it reads.
    fn collection_result_sort<O: CollectionApplication>(
        &self,
        key: &ProvenanceKey,
        operation: O,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        match operation.spec().result_sort {
            CollectionResultSort::Builtin(sort) => Ok(SemanticSortRef::Builtin(sort)),
            CollectionResultSort::Projected => expected_sort
                .cloned()
                .or_else(|| {
                    self.collections
                        .typing
                        .projection(key)
                        .map(|site| site.sort.clone())
                })
                .ok_or_else(|| {
                    let marker = operation.facade_marker();
                    self.invalid_term(format!(
                        "{}::{} requires an expected result sort",
                        marker.module, marker.name
                    ))
                }),
        }
    }

    /// Infers the replacement of a `for Sort` table's `where update cell =
    /// map::update(cell, k, v)`: the update operation of the cell's
    /// collection sort applied to the matched cell, inferred as any term
    /// written into the cell, its key and value at the cell's element sorts.
    pub(super) fn infer_collection_update(
        &mut self,
        update: &DescriptorTerm,
        base_binding: &str,
        cell_sort: &SemanticSortRef,
    ) -> Result<(), DescriptorLoweringError> {
        let DescriptorTerm::Application {
            head_class,
            reference,
            arguments,
            ..
        } = update
        else {
            return Err(self.invalid_term("updated-cell replacement is not an application"));
        };
        if *head_class != krs_ir::DescriptorApplicationHeadClass::Applied {
            return Err(self.invalid_term("updated-cell replacement head is not applied"));
        }
        let ordered = match (&reference.application, cell_sort) {
            (
                DescriptorApplicationRef::Map(krs_ir::TermMapOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::Map),
            ) => UpdateArguments::new(krs_ir::TermMapOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            (
                DescriptorApplicationRef::List(ListOperation::Update),
                SemanticSortRef::Builtin(BuiltinSort::List),
            ) => UpdateArguments::new(ListOperation::Update, arguments)
                .map_err(|detail| self.invalid_term(detail))?,
            _ => {
                return Err(self.invalid_term(
                    "updated-cell replacement does not resolve to the registered update operation for its collection sort",
                ));
            }
        };
        let DescriptorTerm::Variable { name, .. } = ordered.base else {
            return Err(
                self.invalid_term("updated-cell base is not the matched whole-collection binding")
            );
        };
        if name != base_binding {
            return Err(self.invalid_term(format!(
                "updated-cell base {name:?} does not match {base_binding:?}"
            )));
        }
        self.infer(update, Some(cell_sort), false)
    }

    pub(super) fn resolve_binding_sorts(&mut self) -> Result<(), DescriptorLoweringError> {
        for name in self.binding_names {
            if self.binding_sorts.contains_key(name) {
                continue;
            }
            let constraints = self.binding_constraints.get(name).ok_or_else(|| {
                self.invalid_term(format!("variable {name:?} has no expected sort"))
            })?;
            let candidates = most_specific_common_descendants(constraints, self.sort_parents);
            let occurrence_sorts = constraints
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            let inferred = match candidates.as_slice() {
                [sort] => sort.clone(),
                // A hidden binder is a template's value: its subject
                // occurrence is the template, and its other occurrences,
                // the guard and the fields, are `Int` arguments.
                [] if krs_syntax::is_hidden_binder(name) => {
                    let int = SemanticSortRef::Builtin(BuiltinSort::Int);
                    let position = constraints
                        .iter()
                        .filter(|sort| **sort != int)
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(DescriptorLoweringError::BitTemplateSort {
                        item: Box::new(self.descriptor.id().clone()),
                        reason: format!(
                            "a `k::bits!` template matches an `Int`, but it stands where a term of sort {position} is expected, and no `Int` is one; a template belongs in an argument of sort `Int` or of a sort above it"
                        ),
                        range: self
                            .subject_keys
                            .get(name)
                            .and_then(|key| self.authored_range(key)),
                    });
                }
                [] => {
                    // A binder stored in a typed collection names the
                    // element position among its occurrences.
                    if let Some((key, site)) = self
                        .collections
                        .typing
                        .element_sites_of(name)
                        .into_iter()
                        .find(|(_, site)| constraints.contains(&site.sort))
                    {
                        let others = constraints
                            .iter()
                            .filter(|sort| **sort != site.sort)
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        let others =
                            match most_specific_common_descendants(&others, self.sort_parents)
                                .as_slice()
                            {
                                [sort] if !others.is_empty() => Some(sort.clone()),
                                _ => None,
                            };
                        return Err(super::collection_types::binder_conflict(
                            self.descriptor,
                            name,
                            key,
                            site,
                            others.as_ref(),
                            &occurrence_sorts,
                        ));
                    }
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has no declared common descendant for occurrence sorts [{occurrence_sorts}]"
                    )));
                }
                _ => {
                    return Err(self.invalid_term(format!(
                        "variable {name:?} has ambiguous most-specific common descendants [{}] for occurrence sorts [{occurrence_sorts}]",
                        candidates.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")
                    )));
                }
            };
            self.binding_sorts.insert(name.clone(), inferred);
        }
        self.check_collection_reads()
    }

    /// Checks each binder read as a key or element of a typed collection
    /// against the collection's elements, now that its sort is resolved.
    fn check_collection_reads(&mut self) -> Result<(), DescriptorLoweringError> {
        for (name, key) in std::mem::take(&mut self.collections.reads) {
            let Some(sort) = self.binding_sorts.get(&name) else {
                continue;
            };
            let Some(site) = self.collections.typing.reads_at(&key) else {
                continue;
            };
            if !share_a_sort(sort, &site.sort, self.sort_parents) {
                return Err(super::collection_types::disjoint_read(
                    self.descriptor,
                    site,
                    &format!("`{name}` of sort {}", super::overload::sort_name(sort)),
                    sort,
                    &key,
                ));
            }
        }
        Ok(())
    }

    /// Lowers `term` at `expected_sort` ([`Self::lower_term`]), locating an
    /// invalid-term error at the innermost term with an authored range.
    pub(super) fn lower(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        self.lower_term(term, expected_sort, subject)
            .map_err(|error| self.locate(error, term))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive lowering over the closed descriptor term sum."
    )]
    fn lower_term(
        &mut self,
        term: &DescriptorTerm,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        // Only the root of a sentence's subject is its head (KF-027).
        if !matches!(term, DescriptorTerm::Application { .. }) {
            self.head_pending = false;
        }
        match term {
            DescriptorTerm::Variable { key, name, .. }
                if self
                    .locals
                    .scope
                    .as_ref()
                    .is_some_and(|scope| scope.contains_key(name)) =>
            {
                let (id, sort) = self.locals.scope.as_ref().expect("checked above")[name].clone();
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-local-binder")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::Variable { key, name, .. } if self.let_local(name).is_some() => {
                let (id, sort) = self.let_local(name).expect("checked above");
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_let(
                        key,
                        format!(
                            "`{name}` is bound by a `let` or `ml::exists` at sort `{}`, which is not admissible at sort `{}`",
                            super::overload::sort_name(&sort),
                            super::overload::sort_name(expected)
                        ),
                    ));
                }
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-local-binder")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::Variable { key, name, .. } => {
                if !self.binding_names.contains(name) {
                    return Err(self.invalid_term(format!("unbound variable {name:?}")));
                }
                // A whole use of an alias over a group record is the group
                // rebuilt from its children's binders (N7).
                if self.record_updates.updates.reconstructed(name).is_some() {
                    return self.rebuild_group(name, key, expected_sort);
                }
                let sort = self.binding_sorts.get(name).cloned().ok_or_else(|| {
                    self.invalid_term(format!("variable {name:?} has no inferred sort"))
                })?;
                debug_assert!(expected_sort.is_none_or(|expected| semantic_is_subsort(
                    &sort,
                    expected,
                    self.sort_parents
                )));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-variable")?,
                    sort,
                    SemanticId::new(name.clone())?,
                ))
            }
            DescriptorTerm::Wildcard { key } => {
                if !subject && !self.result_wildcards {
                    return Err(self.invalid_term("wildcard occurs outside the rule subject"));
                }
                let sort = expected_sort.cloned().ok_or_else(|| {
                    self.invalid_term("wildcard has no expected production-field sort")
                })?;
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::wildcard(ordinal);
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "term-wildcard")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::Literal { key, literal } => {
                let (sort, value) = match literal {
                    krs_ir::DescriptorLiteral::Int(value) => {
                        (SemanticSortRef::Builtin(BuiltinSort::Int), value.clone())
                    }
                    krs_ir::DescriptorLiteral::Bool(value) => (
                        SemanticSortRef::Builtin(BuiltinSort::Bool),
                        value.to_string(),
                    ),
                    krs_ir::DescriptorLiteral::String(value) => (
                        SemanticSortRef::Builtin(BuiltinSort::String),
                        krs_ir::string_token::encode(value).map_err(|error| {
                            self.invalid_term(format!("string literal: {error}"))
                        })?,
                    ),
                    krs_ir::DescriptorLiteral::Float(token) => {
                        krs_ir::float_token::validate(token).map_err(|error| {
                            self.invalid_term(format!("float literal `{token}`: {error}"))
                        })?;
                        (SemanticSortRef::Builtin(BuiltinSort::Float), token.clone())
                    }
                };
                Ok(SemanticTerm::token(
                    semantic_origin(self.descriptor, key.clone(), "term-literal")?,
                    sort,
                    value,
                )?)
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                instance,
                update,
                open,
                ..
            } => {
                let head = std::mem::take(&mut self.head_pending);
                let record = RecordContext {
                    alias: self.record_updates.alias.take(),
                    update: update.as_deref(),
                    subject,
                    open: *open,
                };
                self.lower_application(reference, arguments, instance, expected_sort, &record, head)
            }
            DescriptorTerm::BuiltinToken { key, sort, value } => SemanticTerm::token(
                semantic_origin(self.descriptor, key.clone(), "claim-builtin-token")?,
                SemanticSortRef::Builtin(*sort),
                value.clone(),
            )
            .map_err(Into::into),
            DescriptorTerm::Lexeme { key, sort, text } => {
                let sort = self.lexeme_sort(key, sort, text)?;
                SemanticTerm::token(
                    semantic_origin(self.descriptor, key.clone(), "term-lexeme")?,
                    sort,
                    text.clone(),
                )
                .map_err(Into::into)
            }
            DescriptorTerm::Anonymous {
                key,
                sort,
                spelling,
            } => {
                if !subject {
                    return Err(self.invalid_term("anonymous occurrence outside claim subject"));
                }
                let sort = semantic_sort_ref(&sort.sort);
                let ordinal = self.wildcard_offset + self.wildcards.len();
                let id = SemanticId::anonymous(spelling, ordinal)?;
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), sort.clone()));
                Ok(SemanticTerm::variable(
                    semantic_origin(self.descriptor, key.clone(), "claim-anonymous")?,
                    sort,
                    id,
                ))
            }
            DescriptorTerm::OrBool { key, arguments } => {
                self.lower_or_bool(key, arguments, subject)
            }
            DescriptorTerm::Cell {
                key,
                declaration,
                fields,
                open,
                update,
            } => {
                let record = RecordContext {
                    alias: self.record_updates.alias.take(),
                    update: update.as_deref(),
                    subject,
                    open: *open,
                };
                self.lower_cell_term(key, declaration, fields, *open, expected_sort, &record)
            }
            DescriptorTerm::SortTest {
                key,
                kind,
                sort,
                operand,
            } => {
                let result = self.sort_test_result(key, *kind, sort, subject)?;
                let target = semantic_sort_ref(&sort.sort);
                let operand_sort = self.sort_test_operand_sort(operand);
                let operand = self.lower(operand, operand_sort.as_ref(), subject)?;
                let operation = match kind {
                    SortTestKind::Predicate => GeneratedOperation::SortPredicate(target),
                    SortTestKind::Projection => GeneratedOperation::SortProjection(target),
                };
                Ok(SemanticTerm::application(
                    semantic_origin(self.descriptor, key.clone(), "term-sort-test")?,
                    result,
                    ApplicationRef::Generated(operation),
                    vec![operand],
                ))
            }
            DescriptorTerm::As {
                key, name, pattern, ..
            } => {
                if !subject {
                    return Err(self.invalid_pattern_as(
                        key,
                        format!(
                            "`{name} @ ..` binds only on a left-hand side (K's #as is LHS-only)"
                        ),
                    ));
                }
                let local = self
                    .locals
                    .scope
                    .as_ref()
                    .and_then(|scope| scope.get(name))
                    .cloned();
                let (id, sort) = match local {
                    Some(local) => local,
                    None => (
                        SemanticId::new(name.clone())?,
                        self.binding_sorts.get(name).cloned().ok_or_else(|| {
                            self.invalid_term(format!("variable {name:?} has no inferred sort"))
                        })?,
                    ),
                };
                // The alias of a record update's base binds the fields its
                // updates leave out (F5); one used only as a base is no
                // `#as`.
                if self.record_updates.updates.is_base(name) {
                    self.record_updates.alias = Some(name.clone());
                }
                let pattern = self.lower(pattern, Some(&sort), subject)?;
                if self.record_updates.updates.is_dropped(name) {
                    return Ok(pattern);
                }
                if !semantic_is_subsort(pattern.sort(), &sort, self.sort_parents) {
                    return Err(self.invalid_pattern_as(
                        key,
                        format!(
                            "alias `{name}` has sort {sort}, but its pattern has sort {}; an alias must name a term of its own sort",
                            pattern.sort()
                        ),
                    ));
                }
                Ok(SemanticTerm::pattern_as(
                    semantic_origin(self.descriptor, key.clone(), "term-pattern-as")?,
                    sort,
                    id,
                    pattern,
                ))
            }
            DescriptorTerm::Or { key, alternatives } => {
                self.lower_pattern_or(key, alternatives, expected_sort, subject)
            }
            DescriptorTerm::Matches {
                key,
                subject: tested,
                pattern,
            } => self.lower_matches(key, tested, pattern),
            DescriptorTerm::Let {
                key,
                pattern,
                sort,
                value,
                body,
            } => self.lower_let(key, pattern, sort.as_ref(), value, body, expected_sort),
            DescriptorTerm::Closure { key, .. } => Err(self.invalid_ml(
                key,
                "closures introduce quantified binders only inside ml::exists".to_owned(),
            )),
            DescriptorTerm::Rewrite {
                key,
                to_key,
                from,
                to,
                ..
            } => self.lower_rewrite(key, to_key, from, to.as_deref(), expected_sort),
        }
    }

    /// The result sort of `k::is!` (Bool) or `k::project!` (its target).
    /// Either is a function call, so it cannot be matched, and K has no
    /// projection into `K`.
    fn sort_test_result(
        &self,
        key: &ProvenanceKey,
        kind: SortTestKind,
        sort: &krs_ir::DescriptorSortReference,
        subject: bool,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        let target = semantic_sort_ref(&sort.sort);
        let name = super::overload::sort_name(&target);
        let reason = if subject {
            Some(match kind {
                SortTestKind::Projection => format!(
                    "`k::project!({name}, ..)` is a projection, which is a function call and cannot be matched; restrict the binder with a typed parameter or `where x: {name}`"
                ),
                SortTestKind::Predicate => format!(
                    "`k::is!({name}, ..)` is a sort predicate, which is a function call and cannot be matched; restrict the binder with a typed parameter or `where x: {name}`"
                ),
            })
        } else if kind == SortTestKind::Projection
            && target == SemanticSortRef::Builtin(BuiltinSort::KSequence)
        {
            Some(
                "`k::project!(K, ..)` projects into `K`, for which K generates no projection; every term already has sort `K`"
                    .to_owned(),
            )
        } else {
            None
        };
        if let Some(reason) = reason {
            return Err(DescriptorLoweringError::InvalidSortTest {
                item: Box::new(self.descriptor.id().clone()),
                reason,
                range: self
                    .descriptor
                    .provenance()
                    .origin_for(key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            });
        }
        Ok(match kind {
            SortTestKind::Predicate => SemanticSortRef::Builtin(BuiltinSort::Bool),
            SortTestKind::Projection => target,
        })
    }

    /// The sort at which the operand of `k::is!` or `k::project!` is
    /// inferred. Both take an argument of sort `K`, so the operand is
    /// unconstrained, except that a projected collection lookup (`map::get`,
    /// `list::get`) keeps its declared result sort `KItem`: the sort test then
    /// supplies the term's one cast.
    fn sort_test_operand_sort(&self, operand: &DescriptorTerm) -> Option<SemanticSortRef> {
        let DescriptorTerm::Application { reference, .. } = operand else {
            return None;
        };
        let projected = match &reference.application {
            DescriptorApplicationRef::Map(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::List(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::Set(operation) => operation.spec().is_projected(),
            DescriptorApplicationRef::Declared(_)
            | DescriptorApplicationRef::Builtin(_)
            | DescriptorApplicationRef::Ml(_)
            | DescriptorApplicationRef::Operator(_)
            | DescriptorApplicationRef::ListNotation(_) => false,
        };
        projected.then(|| {
            self.k_item_sort
                .clone()
                .unwrap_or(SemanticSortRef::Builtin(BuiltinSort::KSequence))
        })
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One arm per kind of the closed application reference sum."
    )]
    pub(super) fn lower_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        record: &RecordContext<'_>,
        head: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let subject = record.subject;
        if let DescriptorApplicationRef::Declared(id) = &reference.application
            && let Some(signature) = self.catalog.get(id)
            && !signature.parameters.is_empty()
        {
            let signature = signature.clone();
            return self.lower_parametric(
                reference,
                id,
                &signature,
                arguments,
                instance,
                expected_sort,
                record,
                head,
            );
        }
        let (application, signature) = match &reference.application {
            DescriptorApplicationRef::Declared(id) => {
                let signature = self.catalog.get(id).cloned().ok_or_else(|| {
                    self.invalid_term(format!(
                        "declared application {id} has no grammar production"
                    ))
                })?;
                (ApplicationRef::Declared(id.clone()), signature)
            }
            DescriptorApplicationRef::Builtin(operation) if operation.is_sort_generic() => {
                return self.lower_generic_builtin(
                    reference,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                );
            }
            DescriptorApplicationRef::Builtin(operation) => (
                ApplicationRef::Builtin(*operation),
                builtin_production_signature(*operation)
                    .ok_or_else(|| self.sort_generic_builtin(*operation))?,
            ),
            DescriptorApplicationRef::Map(operation) => {
                let (result_sort, operands) = self.lower_collection_operands(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                let operands = MapOperands::from_operands((*operation).into(), operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::typed_map(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-map-operation")?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::List(operation) => {
                let (result_sort, operands) = self.lower_collection_operands(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                let operands = ListOperands::from_operands(*operation, operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::list(
                    semantic_origin(
                        self.descriptor,
                        reference.key.clone(),
                        "term-list-operation",
                    )?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::Set(operation) => {
                let (result_sort, operands) = self.lower_collection_operands(
                    &reference.key,
                    *operation,
                    arguments,
                    expected_sort,
                    subject,
                )?;
                let operands = SetOperands::from_operands(*operation, operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::set(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-set-operation")?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::Ml(connective) => {
                return Err(self.ml_in_object_term(&reference.key, *connective));
            }
            DescriptorApplicationRef::Operator(operator) => {
                return self.lower_operator(
                    reference,
                    *operator,
                    arguments,
                    expected_sort,
                    subject,
                    head,
                );
            }
            DescriptorApplicationRef::ListNotation(ListNotation::Cons | ListNotation::Snoc)
                if !head || super::cons_lists::is_builtin_list(expected_sort) =>
            {
                return self.lower_list_spine(reference, arguments, expected_sort, subject);
            }
            DescriptorApplicationRef::ListNotation(notation) => {
                let reference = self.list_constructor(reference, *notation, expected_sort)?;
                return self.lower_application(
                    &reference,
                    arguments,
                    instance,
                    expected_sort,
                    record,
                    head,
                );
            }
        };
        let lowered = record
            .ordered(arguments, &signature.fields)
            .map_err(|detail| self.invalid_term(detail))?
            .into_iter()
            .zip(&signature.fields)
            .map(|(argument, (field, sort))| {
                self.lower_record_field(argument, field, Some(sort), record)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SemanticTerm::application(
            semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
            signature.result_sort,
            application,
            lowered,
        ))
    }

    fn lower_or_bool(
        &mut self,
        key: &ProvenanceKey,
        arguments: &krs_ir::AtLeastTwo<DescriptorTerm>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let lowered =
            arguments.try_map_ref(|argument| self.lower(argument, Some(&bool_sort), subject))?;
        let (mut value, tail) = lowered.into_head_tail();
        for right in tail {
            value = SemanticTerm::application(
                semantic_origin(self.descriptor, key.clone(), "claim-or-bool")?,
                bool_sort.clone(),
                ApplicationRef::Builtin(BuiltinOperation::BoolOr),
                vec![value, right],
            );
        }
        Ok(value)
    }

    fn cell_k_item_sort(&self) -> Result<SemanticSortRef, DescriptorLoweringError> {
        self.k_item_sort.clone().ok_or_else(|| {
            self.invalid_term("fragment! requires one selected framework KItem sort")
        })
    }

    fn cell_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellDeclaration, DescriptorLoweringError> {
        let declarations = self.declarations.ok_or_else(|| {
            self.invalid_term("fragment! is supported only where cell declarations are available")
        })?;
        let declaration = declarations.cell(owner)?;
        Ok(declaration)
    }

    fn infer_cell_fields(
        &mut self,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        subject: bool,
        partial: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        if supplied.len() != fields.len()
            || (!partial && supplied.len() != declaration.fields.len())
        {
            return Err(self.invalid_term(format!(
                "the cell term for {:?} (a `k::fragment!` or a group record) must name every child field exactly once; a pattern ends in `..` to leave the others unconstrained, and a result takes them from a matched group with `..base`",
                owner.item_name()
            )));
        }
        for field in supplied.keys() {
            if !declaration
                .fields
                .iter()
                .any(|declared| declared.rust_field == field.as_str())
            {
                return Err(self.invalid_term(format!(
                    "fragment! for {:?} has no child field {:?}",
                    owner.item_name(),
                    field.as_str()
                )));
            }
        }
        for declared in &declaration.fields {
            let Some(field) = supplied.get(&ProductionFieldId::new(&declared.rust_field)?) else {
                if partial {
                    continue;
                }
                return Err(self.invalid_term(format!(
                    "fragment! for {:?} is missing child field {:?}",
                    owner.item_name(),
                    declared.rust_field
                )));
            };
            match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    self.infer(&field.value, Some(&semantic_sort_ref(&sort.sort)), subject)?;
                }
                // A group child is a value of its cell sort: a group record
                // or fragment, a binder, `_`, or an alias over a group record,
                // which the record updates rebuild where it is used (N7).
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => {
                    let record = match field.value.as_ref() {
                        DescriptorTerm::Cell { declaration, .. } => Some(declaration),
                        DescriptorTerm::As { name, pattern, .. } => {
                            let DescriptorTerm::Cell { declaration, .. } = pattern.as_ref() else {
                                return Err(self.invalid_term(format!(
                                    "the alias `{name}` over the group child {:?} must alias a group record",
                                    declared.rust_field
                                )));
                            };
                            if !self.record_updates.updates.is_dropped(name) {
                                return Err(self.invalid_term(format!(
                                    "the alias `{name}` over the group child {:?} names one matched cell, so it must be bound once and outside `|`",
                                    declared.rust_field
                                )));
                            }
                            Some(declaration)
                        }
                        DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. } => None,
                        _ => {
                            return Err(self.invalid_term(format!(
                                "the group child {:?} is a group record, `k::fragment!`, a binder, or `_`",
                                declared.rust_field
                            )));
                        }
                    };
                    if let Some(declaration) = record {
                        if declaration != &nested.declaration {
                            return Err(self.invalid_term(format!(
                                "nested child {:?} uses the wrong cell declaration",
                                declared.rust_field
                            )));
                        }
                        self.infer(&field.value, Some(&self.cell_k_item_sort()?), subject)?;
                    } else {
                        self.infer(
                            &field.value,
                            Some(&SemanticSortRef::Cell(nested.declaration.clone())),
                            subject,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn lower_cell_term(
        &mut self,
        key: &ProvenanceKey,
        owner: &StableItemId,
        fields: &[krs_ir::DescriptorCellTermField],
        open: bool,
        expected_sort: Option<&SemanticSortRef>,
        record: &RecordContext<'_>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        // A fragment that is a whole group-cell clause has the group's
        // generated cell sort (KF-016); elsewhere it keeps the KItem sort it
        // always had, so existing emitted and native terms are unchanged.
        let whole = SemanticSortRef::Cell(owner.clone());
        let sort = if expected_sort == Some(&whole) {
            whole
        } else {
            self.cell_k_item_sort()?
        };
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        let mut children = Vec::with_capacity(declaration.fields.len());
        for declared in &declaration.fields {
            let field_id = ProductionFieldId::new(&declared.rust_field)?;
            let field = supplied.get(&field_id);
            // A child the term leaves out is unconstrained in a `..` pattern
            // and its base's in an update (F5); a complete term names it.
            if field.is_none() && !open && record.update.is_none() && record.alias.is_none() {
                return Err(self.invalid_term(format!(
                    "fragment! is missing child field {:?}",
                    declared.rust_field
                )));
            }
            let value = field.map(|field| field.value.as_ref());
            let child = match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    let content_sort = semantic_sort_ref(&sort.sort);
                    let content =
                        self.lower_record_field(value, &field_id, Some(&content_sort), record)?;
                    let origin = match field {
                        Some(field) => {
                            semantic_origin(self.descriptor, field.key.clone(), "cell-term-child")?
                        }
                        None => self.generated_record_origin(key, "cell-term-child")?,
                    };
                    SemanticTerm::cell(
                        origin,
                        self.cell_k_item_sort()?,
                        semantic_cell_id(&declared.reference.cell)?,
                        vec![content],
                    )
                }
                // A nested group child left out is matched or written whole,
                // by a variable of its generated cell sort.
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => match value {
                    Some(value @ (DescriptorTerm::Cell { .. } | DescriptorTerm::As { .. })) => {
                        // A group child a base's fills rebuild binds its own
                        // children (N7).
                        if let Some(alias) = &record.alias
                            && let Some(Fill::Group(child)) =
                                self.record_updates.updates.fill(alias, &field_id)
                            && matches!(value, DescriptorTerm::Cell { .. })
                        {
                            self.record_updates.alias = Some(child.clone());
                        }
                        self.lower(value, Some(&self.cell_k_item_sort()?), record.subject)?
                    }
                    // A binder or `_` is matched or written at the child's
                    // cell sort, as a child the term leaves out is.
                    Some(value) => self.lower_record_field(
                        Some(value),
                        &field_id,
                        Some(&SemanticSortRef::Cell(nested.declaration.clone())),
                        record,
                    )?,
                    None => self.lower_record_field(
                        None,
                        &field_id,
                        Some(&SemanticSortRef::Cell(nested.declaration.clone())),
                        record,
                    )?,
                },
            };
            children.push(child);
        }
        let identity = self.cell_identity_for_declaration(owner)?;
        Ok(SemanticTerm::cell(
            semantic_origin(self.descriptor, key.clone(), "cell-term")?,
            sort,
            semantic_cell_id(identity)?,
            children,
        ))
    }

    /// Lowers one field of a record: its authored term, or, for a field the
    /// record leaves out, the binder that fills it (F5) or, in a pattern, a
    /// wildcard. In the record pattern of a base alias, a field an update
    /// takes is matched by its hidden binder, as `( p #as Hidden )` when the
    /// pattern constrains it.
    fn lower_record_field(
        &mut self,
        argument: Option<&DescriptorTerm>,
        field: &ProductionFieldId,
        sort: Option<&SemanticSortRef>,
        record: &RecordContext<'_>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let fill = |updates: &super::record_updates::RecordUpdates, base: &str| {
            updates.fill(base, field).cloned()
        };
        if let Some(alias) = &record.alias
            && let Some(Fill::Hidden(id)) = fill(&self.record_updates.updates, alias)
        {
            let sort = self.record_field_sort(sort, field)?;
            let key = self
                .record_updates
                .updates
                .alias_key(alias)
                .cloned()
                .expect("a base alias has a key");
            let hidden = self.hidden_record_binder(&id, &sort, &key)?;
            return match argument {
                None | Some(DescriptorTerm::Wildcard { .. }) => Ok(hidden),
                Some(pattern) => {
                    let pattern = self.lower(pattern, Some(&sort), record.subject)?;
                    Ok(SemanticTerm::pattern_as(
                        self.generated_record_origin(&key, "record-update-as")?,
                        sort,
                        id,
                        pattern,
                    ))
                }
            };
        }
        if let Some(argument) = argument {
            return self.lower(argument, sort, record.subject);
        }
        if let Some(DescriptorTerm::Variable { key, name, .. }) = record.update {
            return match fill(&self.record_updates.updates, name) {
                Some(fill) => self.lower_fill(fill, sort, field, key),
                None => Err(self.invalid_record_update(
                    key,
                    format!(
                        "`..{name}` cannot supply the field `{}` here; a record update is notation of readable rules, equations, and claims",
                        field.as_str()
                    ),
                )),
            };
        }
        let sort = sort.cloned().ok_or_else(|| {
            self.invalid_term("a record rest at a parameter position needs a turbofish")
        })?;
        self.lower_record_rest_wildcard(&sort)
    }

    /// The term that fills `field`, which an update leaves out, from its
    /// base's fill.
    fn lower_fill(
        &mut self,
        fill: Fill,
        sort: Option<&SemanticSortRef>,
        field: &ProductionFieldId,
        key: &ProvenanceKey,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        match fill {
            Fill::Binder(binder) => {
                let binder_sort = self.binding_sorts.get(&binder).cloned().ok_or_else(|| {
                    self.invalid_term(format!("variable {binder:?} has no inferred sort"))
                })?;
                Ok(SemanticTerm::variable(
                    self.generated_record_origin(key, "record-update-field")?,
                    binder_sort,
                    SemanticId::new(binder)?,
                ))
            }
            Fill::Hidden(id) => {
                let sort = self.record_field_sort(sort, field)?;
                self.hidden_record_binder(&id, &sort, key)
            }
            // A group child is written as an authored child is, at the
            // KItem sort.
            Fill::Group(child) => {
                let k_item = self.cell_k_item_sort()?;
                self.rebuild_group(&child, key, Some(&k_item))
            }
        }
    }

    /// The cell of the group record `name` (an alias over a group record, or
    /// a group child below a base) rebuilt from its children: each child is
    /// the binder the record's pattern gives it, a hidden binder, or a group
    /// child rebuilt in turn (N7). The rebuilt term matches exactly the cells
    /// the record's pattern matches, so it denotes the matched cell without
    /// a conjunction among a cell's children.
    fn rebuild_group(
        &mut self,
        name: &str,
        key: &ProvenanceKey,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let owner = self
            .record_updates
            .updates
            .group(name)
            .cloned()
            .expect("a rebuilt record is a group record");
        let whole = SemanticSortRef::Cell(owner.clone());
        let sort = if expected_sort == Some(&whole) {
            whole
        } else {
            self.cell_k_item_sort()?
        };
        let declaration = self.cell_declaration(&owner)?.clone();
        let mut children = Vec::with_capacity(declaration.fields.len());
        for declared in &declaration.fields {
            let field = ProductionFieldId::new(&declared.rust_field)?;
            let fill = self
                .record_updates
                .updates
                .fill(name, &field)
                .cloned()
                .expect("a rebuilt record fills every child");
            let child = match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    let content =
                        self.lower_fill(fill, Some(&semantic_sort_ref(&sort.sort)), &field, key)?;
                    SemanticTerm::cell(
                        self.generated_record_origin(key, "cell-term-child")?,
                        self.cell_k_item_sort()?,
                        semantic_cell_id(&declared.reference.cell)?,
                        vec![content],
                    )
                }
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => self.lower_fill(
                    fill,
                    Some(&SemanticSortRef::Cell(nested.declaration.clone())),
                    &field,
                    key,
                )?,
            };
            children.push(child);
        }
        let identity = self.cell_identity_for_declaration(&owner)?;
        let identity = semantic_cell_id(identity)?;
        Ok(SemanticTerm::cell(
            self.generated_record_origin(key, "record-rebuild")?,
            sort,
            identity,
            children,
        ))
    }

    /// The sort a field left out of a record is filled at: the field's
    /// declared sort, known unless it is a sort parameter no turbofish fixes.
    fn record_field_sort(
        &self,
        sort: Option<&SemanticSortRef>,
        field: &ProductionFieldId,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        sort.cloned().ok_or_else(|| {
            self.invalid_term(format!(
                "the field `{}` of a parametric record takes the sort of its instance; write the field, or fix the instance with a turbofish",
                field.as_str()
            ))
        })
    }

    /// A hidden binder of a record update, declared as a sentence variable at
    /// its first occurrence.
    fn hidden_record_binder(
        &mut self,
        id: &SemanticId,
        sort: &SemanticSortRef,
        key: &ProvenanceKey,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if self.record_updates.declared.insert(id.clone()) {
            self.wildcards
                .push(SemanticVariable::new(id.clone(), sort.clone()));
        }
        Ok(SemanticTerm::variable(
            self.generated_record_origin(key, "record-update-binder")?,
            sort.clone(),
            id.clone(),
        ))
    }

    /// The origin of one term a record rest or update generates: each has a
    /// role of its own, since several share the authored key.
    fn generated_record_origin(
        &mut self,
        key: &ProvenanceKey,
        role: &str,
    ) -> Result<krs_ir::NodeOrigin, DescriptorLoweringError> {
        let ordinal = self.record_updates.ordinal;
        self.record_updates.ordinal += 1;
        semantic_origin(self.descriptor, key.clone(), &format!("{role}-{ordinal}"))
    }

    pub(super) fn invalid_record_update(
        &self,
        key: &ProvenanceKey,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidRecordUpdate {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        }
    }

    fn cell_identity_for_declaration(
        &self,
        owner: &StableItemId,
    ) -> Result<&krs_ir::DescriptorCellIdentity, DescriptorLoweringError> {
        let declarations = self
            .declarations
            .ok_or_else(|| self.invalid_term("fragment! has no cell-declaration catalog"))?;
        let mut matches = declarations
            .values()
            .flat_map(|descriptor| {
                let declaration = match descriptor.payload() {
                    DescriptorPayload::Cell(value) => Some(value.as_ref()),
                    DescriptorPayload::FixedConfiguration(value) => Some(&value.declaration),
                    _ => None,
                };
                declaration
                    .into_iter()
                    .flat_map(|declaration| declaration.fields.iter())
            })
            .filter(|field| {
                matches!(
                    &field.content,
                    ProtocolCellContent::Nested { declaration } if &declaration.declaration == owner
                )
            });
        let first = matches.next().ok_or_else(|| {
            self.invalid_term(format!(
                "cell declaration {:?} is not attached to the fixed configuration",
                owner.item_name()
            ))
        })?;
        if matches.next().is_some() {
            return Err(self.invalid_term(format!(
                "cell declaration {:?} is attached more than once",
                owner.item_name()
            )));
        }
        Ok(&first.reference.cell)
    }

    fn lower_record_rest_wildcard(
        &mut self,
        sort: &SemanticSortRef,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let pattern_key = self.pattern_key.ok_or_else(|| {
            self.invalid_term("partial named patterns are valid only in structured rule subjects")
        })?;
        let ordinal = self.wildcard_offset + self.wildcards.len();
        let id = SemanticId::wildcard(ordinal);
        let role = format!("record-rest-{ordinal}");
        self.wildcards
            .push(SemanticVariable::new(id.clone(), sort.clone()));
        Ok(SemanticTerm::variable(
            semantic_origin(self.descriptor, pattern_key.clone(), &role)?,
            sort.clone(),
            id,
        ))
    }

    fn sort_generic_builtin(&self, operation: BuiltinOperation) -> DescriptorLoweringError {
        self.invalid_term(format!(
            "builtin operation {operation} has a sort-generic signature"
        ))
    }

    /// The sort of a `k::lexeme!` term, which must be a user sort with token
    /// productions; builtin tokens are written as literals or with their own
    /// islands.
    fn lexeme_sort(
        &self,
        key: &ProvenanceKey,
        sort: &krs_ir::DescriptorSortReference,
        text: &str,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        let semantic = semantic_sort_ref(&sort.sort);
        let reason = match &semantic {
            SemanticSortRef::Builtin(builtin) => Some(format!(
                "`k::lexeme!` names the builtin sort `{}`; write a builtin token as a literal, `k::id!(\"$name\")`, or `k::bytes!(b\"..\")`",
                builtin.k_name()
            )),
            SemanticSortRef::Parameter(_) => {
                Some("`k::lexeme!` names a sort parameter, which is not a token sort".to_owned())
            }
            SemanticSortRef::Declared(_)
                if !self
                    .catalog
                    .values()
                    .any(|signature| signature.token && signature.result_sort == semantic) =>
            {
                Some(format!(
                    "`k::lexeme!({}, {text:?})` names `{}`, which is not a token sort; declare its tokens with `#[k::token(..)]` on a `struct {}(String);`",
                    super::overload::sort_name(&semantic),
                    super::overload::sort_name(&semantic),
                    super::overload::sort_name(&semantic),
                ))
            }
            SemanticSortRef::Cell(_) => Some(format!(
                "`k::lexeme!({}, {text:?})` names a generated cell sort, which is not a token sort",
                super::overload::sort_name(&semantic),
            )),
            SemanticSortRef::Declared(_) => None,
        };
        match reason {
            Some(reason) => Err(DescriptorLoweringError::InvalidTokenSort {
                item: Box::new(self.descriptor.id().clone()),
                reason,
                range: self
                    .descriptor
                    .provenance()
                    .origin_for(key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            }),
            None => Ok(semantic),
        }
    }

    /// Rejects an occurrence of a typed binder whose position needs a sort
    /// the declared sort is not below (KF-009). A narrower declared sort is
    /// kept, as K keeps `X:S`.
    fn check_declared_binder(
        &self,
        name: &str,
        expected: &SemanticSortRef,
    ) -> Result<(), DescriptorLoweringError> {
        let Some((declared, key)) = self.declared_binders.get(name) else {
            return Ok(());
        };
        if semantic_is_subsort(declared, expected, self.sort_parents) {
            return Ok(());
        }
        Err(DescriptorLoweringError::IncompatibleBinder {
            item: Box::new(self.descriptor.id().clone()),
            reason: format!(
                "binder `{name}` is declared `{}` but this occurrence needs `{}`",
                super::overload::sort_name(declared),
                super::overload::sort_name(expected),
            ),
            range: self
                .descriptor
                .provenance()
                .origin_for(key)
                .and_then(krs_ir::OriginStack::exact_authored_range)
                .map(Box::new),
        })
    }

    /// A turbofish names an instance only on a parametric production
    /// (KF-027); one on a builtin operation or a fixed production is an error.
    fn reject_misplaced_turbofish(
        &self,
        reference: &DescriptorApplicationReference,
        instance: &[krs_ir::DescriptorSortReference],
    ) -> Result<(), DescriptorLoweringError> {
        let Some(first) = instance.first() else {
            return Ok(());
        };
        let parametric = match &reference.application {
            DescriptorApplicationRef::Declared(id) => self
                .catalog
                .get(id)
                .is_some_and(|signature| !signature.parameters.is_empty()),
            _ => false,
        };
        if parametric {
            return Ok(());
        }
        Err(self.parametric_instance_error(
            &first.key,
            "this application is not a parametric production, so it takes no turbofish; remove it"
                .to_owned(),
        ))
    }

    /// The turbofish of a parametric application as semantic sorts, checked
    /// against the production's parameter count.
    fn turbofish(
        &self,
        reference: &DescriptorApplicationReference,
        signature: &ProductionSignature,
        instance: &[krs_ir::DescriptorSortReference],
    ) -> Result<Option<Vec<SemanticSortRef>>, DescriptorLoweringError> {
        if instance.is_empty() {
            return Ok(None);
        }
        if instance.len() != signature.parameters.len() {
            return Err(self.parametric_instance_error(
                &reference.key,
                format!(
                    "this production has {} sort parameter{} but its turbofish names {} sort{}",
                    signature.parameters.len(),
                    if signature.parameters.len() == 1 {
                        ""
                    } else {
                        "s"
                    },
                    instance.len(),
                    if instance.len() == 1 { "" } else { "s" },
                ),
            ));
        }
        Ok(Some(
            instance
                .iter()
                .map(|sort| semantic_sort_ref(&sort.sort))
                .collect(),
        ))
    }

    /// The sort each field of a parametric application is inferred and
    /// lowered at: its declared sort at the turbofish instance or, without
    /// one, a parameter position bounded by the position's sort when the
    /// result is that parameter (an upper bound of the instance).
    fn parametric_field_sorts(
        signature: &ProductionSignature,
        turbofish: Option<&[SemanticSortRef]>,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Vec<Option<SemanticSortRef>> {
        signature
            .fields
            .iter()
            .map(|(_, sort)| match sort {
                SemanticSortRef::Parameter(name) => {
                    let index = signature
                        .parameters
                        .iter()
                        .position(|parameter| parameter == name);
                    match (index, turbofish) {
                        (Some(index), Some(turbofish)) => turbofish.get(index).cloned(),
                        _ if signature.result_sort == *sort => expected_sort.cloned(),
                        _ => None,
                    }
                }
                sort => Some(sort.clone()),
            })
            .collect()
    }

    fn instantiate(
        signature: &ProductionSignature,
        sort: &SemanticSortRef,
        instance: &[SemanticSortRef],
    ) -> SemanticSortRef {
        match sort {
            SemanticSortRef::Parameter(name) => signature
                .parameters
                .iter()
                .position(|parameter| parameter == name)
                .and_then(|index| instance.get(index))
                .cloned()
                .unwrap_or_else(|| sort.clone()),
            sort => sort.clone(),
        }
    }

    fn infer_parametric(
        &mut self,
        reference: &DescriptorApplicationReference,
        signature: &ProductionSignature,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        partial: Partial<'_>,
    ) -> Result<(), DescriptorLoweringError> {
        let subject = partial.subject;
        let turbofish = self.turbofish(reference, signature, instance)?;
        if let Some(expected) = expected_sort {
            let result = match &turbofish {
                Some(turbofish) => Some(Self::instantiate(
                    signature,
                    &signature.result_sort,
                    turbofish,
                )),
                None if matches!(signature.result_sort, SemanticSortRef::Parameter(_)) => None,
                None => Some(signature.result_sort.clone()),
            };
            if let Some(result) = result
                && !semantic_is_subsort(&result, expected, self.sort_parents)
            {
                return Err(match &turbofish {
                    Some(turbofish) => self.parametric_instance_error(
                        &reference.key,
                        format!(
                            "the turbofish `::<{}>` gives this application the sort {}, which is not admissible where the sort {} is declared or expected",
                            turbofish.iter().map(marker_spelling).collect::<Vec<_>>().join(", "),
                            super::overload::sort_name(&result),
                            super::overload::sort_name(expected),
                        ),
                    ),
                    None => self.invalid_term(format!(
                        "application result sort {result} is not admissible at sort {expected}"
                    )),
                });
            }
        }
        let sorts = Self::parametric_field_sorts(signature, turbofish.as_deref(), expected_sort);
        let ordered = partial
            .ordered(arguments, &signature.fields)
            .map_err(|detail| self.invalid_term(detail))?;
        for (argument, sort) in ordered.into_iter().zip(&sorts) {
            if let Some(argument) = argument {
                self.infer(argument, sort.as_ref(), subject)?;
            }
        }
        Ok(())
    }

    /// Lowers an application of a parametric production (KF-027) and solves
    /// its instance by k-rust's rule (X9.1): per parameter, the least sort
    /// above the sorts of its argument positions, bounded by the position
    /// when the result is that parameter. A head's turbofish fixes the
    /// instance; elsewhere a turbofish must agree with the solved instance,
    /// because emitted K and k-rust cannot write it.
    #[expect(
        clippy::too_many_arguments,
        clippy::too_many_lines,
        reason = "One pass lowers, solves, and checks a parametric application."
    )]
    fn lower_parametric(
        &mut self,
        reference: &DescriptorApplicationReference,
        id: &StableItemId,
        signature: &ProductionSignature,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        record: &RecordContext<'_>,
        head: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let turbofish = self.turbofish(reference, signature, instance)?;
        let name = crate::partition::production_display_name(id);
        if head && turbofish.is_none() {
            let example = format!(
                "{name}::<{}>",
                expected_sort.map_or_else(|| "k::builtin::Int".to_owned(), marker_spelling)
            );
            return Err(self.parametric_instance_error(
                &reference.key,
                format!(
                    "an equation or rule head of the parametric production `{name}` needs a turbofish: without one K would instantiate its sort parameter at K and this sentence would never apply; write `{example}`"
                ),
            ));
        }
        let sorts = Self::parametric_field_sorts(signature, turbofish.as_deref(), expected_sort);
        let ordered = record
            .ordered(arguments, &signature.fields)
            .map_err(|detail| self.invalid_term(detail))?;
        let mut lowered = Vec::with_capacity(sorts.len());
        let mut variables = Vec::with_capacity(sorts.len());
        for ((argument, sort), (field, _)) in ordered.into_iter().zip(&sorts).zip(&signature.fields)
        {
            // A record rest (`..`) is a wildcard, so it counts as a variable.
            variables.push(argument.is_none_or(|argument| {
                matches!(
                    argument,
                    DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. }
                )
            }));
            lowered.push(self.lower_record_field(argument, field, sort.as_ref(), record)?);
        }
        let mut solved_instance = Vec::with_capacity(signature.parameters.len());
        for (index, parameter) in signature.parameters.iter().enumerate() {
            let parameter_sort = SemanticSortRef::Parameter(parameter.clone());
            let positions = signature
                .fields
                .iter()
                .zip(&lowered)
                .zip(&variables)
                .filter(|(((_, sort), _), _)| *sort == parameter_sort)
                .map(|((_, argument), variable)| (argument.sort().clone(), *variable))
                .collect::<Vec<_>>();
            let argument_sorts = positions
                .iter()
                .map(|(sort, _)| sort.clone())
                .collect::<Vec<_>>();
            let bound = if signature.result_sort == parameter_sort {
                expected_sort
            } else {
                None
            };
            let solved = least_instance(&argument_sorts, bound, self.sort_parents);
            let Some(turbofish) = &turbofish else {
                let instance = solved.map_err(|error| {
                    self.parametric_instance_error(
                        &reference.key,
                        format!(
                            "K cannot determine the sort parameter `{parameter}` of `{name}` from its arguments ({}) and position: {}; give an argument a narrower sort with a typed binder or `where`",
                            argument_sorts.iter().map(super::overload::sort_name).collect::<Vec<_>>().join(", "),
                            match error {
                                InstanceError::NoCommonSort { .. } => "they have no common sort".to_owned(),
                                InstanceError::Ambiguous(candidates) => format!(
                                    "they have no least common sort (candidates {})",
                                    candidates.iter().map(super::overload::sort_name).collect::<Vec<_>>().join(", ")
                                ),
                            }
                        ),
                    )
                })?;
                solved_instance.push(instance);
                continue;
            };
            let fixed = turbofish[index].clone();
            if head {
                if bound.is_some_and(|bound| *bound != fixed) {
                    return Err(self.parametric_instance_error(
                        &reference.key,
                        format!(
                            "the turbofish `{name}::<{}>` disagrees with the head's declared `k::Term<{}>`; the result of `{name}` is its sort parameter `{parameter}`, so both name the same sort",
                            marker_spelling(&fixed),
                            expected_sort.map_or_else(String::new, marker_spelling),
                        ),
                    ));
                }
                for (sort, variable) in &positions {
                    if !*variable && *sort != fixed {
                        return Err(self.parametric_instance_error(
                            &reference.key,
                            format!(
                                "an argument of sort {} at a position of the sort parameter `{parameter}` of this head is not a variable, so K's strict cast cannot fix its instance `{}`; match it with a variable of sort {} and test it in `requires`",
                                super::overload::sort_name(sort),
                                super::overload::sort_name(&fixed),
                                super::overload::sort_name(&fixed),
                            ),
                        ));
                    }
                }
                if solved.as_ref().ok() != Some(&fixed) {
                    let solved_text = solved.as_ref().map_or_else(
                        |_| "no unique instance".to_owned(),
                        |sort| format!("{parameter} = {}", super::overload::sort_name(sort)),
                    );
                    return Err(DescriptorLoweringError::NativeInstance {
                        item: Box::new(self.descriptor.id().clone()),
                        reason: format!(
                            "label sort parameters cannot be written natively, so k-rust fixes this head's instance from its argument sorts: it would solve {solved_text}, not the turbofish's {parameter} = {}. Give at least one parametric argument a variable of sort {}.",
                            super::overload::sort_name(&fixed),
                            super::overload::sort_name(&fixed),
                        ),
                        range: self.authored_range(&reference.key),
                    });
                }
            } else if solved.as_ref().ok() != Some(&fixed) {
                return Err(self.parametric_instance_error(
                    &reference.key,
                    format!(
                        "K and k-rust solve the sort parameter `{parameter}` of this `{name}` from its arguments and position as {}, not the turbofish's {}; the turbofish of a term that is not an equation or rule head must name the instance K solves",
                        solved.as_ref().map_or_else(
                            |_| "no unique sort".to_owned(),
                            super::overload::sort_name,
                        ),
                        super::overload::sort_name(&fixed),
                    ),
                ));
            }
            solved_instance.push(fixed);
        }
        let result_sort = Self::instantiate(signature, &signature.result_sort, &solved_instance);
        if !signature.function
            && matches!(signature.result_sort, SemanticSortRef::Parameter(_))
            && self.has_domain_values(&result_sort)
        {
            return Err(DescriptorLoweringError::InvalidParametricProduction {
                item: Box::new(self.descriptor.id().clone()),
                reason: format!(
                    "the parametric constructor `{name}` builds a value of its sort parameter, so it cannot be instantiated at {}, whose values its domain or hook fixes",
                    super::overload::sort_name(&result_sort)
                ),
                range: self.authored_range(&reference.key),
            });
        }
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "application result sort {result_sort} is not admissible at sort {expected}"
            )));
        }
        Ok(SemanticTerm::parametric_application(
            semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
            result_sort,
            ApplicationRef::Declared(id.clone()),
            lowered,
            solved_instance,
            head,
        ))
    }

    /// Whether `sort` has domain values or a hook: a builtin sort other than
    /// `K` and `KItem`, or a token sort.
    fn has_domain_values(&self, sort: &SemanticSortRef) -> bool {
        match sort {
            SemanticSortRef::Builtin(builtin) => *builtin != BuiltinSort::KSequence,
            SemanticSortRef::Declared(_) => self
                .catalog
                .values()
                .any(|signature| signature.token && signature.result_sort == *sort),
            SemanticSortRef::Cell(_) | SemanticSortRef::Parameter(_) => false,
        }
    }

    pub(super) fn authored_range(&self, key: &ProvenanceKey) -> Option<Box<krs_ir::SourceRange>> {
        self.descriptor
            .provenance()
            .origin_for(key)
            .and_then(krs_ir::OriginStack::exact_authored_range)
            .map(Box::new)
    }

    fn parametric_instance_error(
        &self,
        key: &ProvenanceKey,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::ParametricInstance {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self.authored_range(key),
        }
    }

    /// An invalid-term error, which [`Self::infer`] and [`Self::lower`]
    /// locate at the term they were given.
    pub(super) fn invalid_term(&self, detail: impl Into<String>) -> DescriptorLoweringError {
        DescriptorLoweringError::invalid_term(self.descriptor.id(), detail)
    }

    /// `error`, an invalid-term error not yet located, located at `term`.
    fn locate(
        &self,
        mut error: DescriptorLoweringError,
        term: &DescriptorTerm,
    ) -> DescriptorLoweringError {
        if let DescriptorLoweringError::InvalidTerm {
            range: range @ None,
            ..
        } = &mut error
        {
            *range = self.authored_range(Self::term_key(term));
        }
        error
    }
}

/// Whether a `let` pattern is one name or `_` (`let x = v`, `let _ = v`),
/// whose sort is the ascription or the value's (KF-032).
const fn is_bare_let_pattern(pattern: &DescriptorTerm) -> bool {
    matches!(
        pattern,
        DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. }
    )
}

/// The authored macro of a sort test, for messages.
/// Every name a `k::matches!` pattern binds, with the provenance key of each
/// occurrence, in preorder: variables and `name @ ..` aliases.
fn pattern_names(term: &DescriptorTerm, output: &mut Vec<(String, ProvenanceKey)>) {
    match term {
        DescriptorTerm::Variable { key, name, .. } => output.push((name.clone(), key.clone())),
        DescriptorTerm::As {
            binding_key,
            name,
            pattern,
            ..
        } => {
            output.push((name.clone(), binding_key.clone()));
            pattern_names(pattern, output);
        }
        DescriptorTerm::Or { alternatives, .. } => {
            for alternative in alternatives {
                pattern_names(alternative, output);
            }
        }
        DescriptorTerm::OrBool { arguments, .. } => {
            for argument in arguments {
                pattern_names(argument, output);
            }
        }
        DescriptorTerm::Application { arguments, .. } => {
            for argument in arguments {
                let (krs_ir::TermArgumentRef::Positional { value }
                | krs_ir::TermArgumentRef::Named { value, .. }) = argument;
                pattern_names(value, output);
            }
        }
        DescriptorTerm::Cell { fields, .. } => {
            for field in fields {
                pattern_names(&field.value, output);
            }
        }
        DescriptorTerm::SortTest { operand, .. } => pattern_names(operand, output),
        DescriptorTerm::Matches { subject, .. } => pattern_names(subject, output),
        DescriptorTerm::Rewrite { from, .. } => pattern_names(from, output),
        DescriptorTerm::Let { .. }
        | DescriptorTerm::Closure { .. }
        | DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => {}
    }
}

const fn sort_test_macro(kind: SortTestKind) -> &'static str {
    match kind {
        SortTestKind::Predicate => "`k::is!`",
        SortTestKind::Projection => "`k::project!`",
    }
}

/// Why a sort-parametric application has no instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum InstanceError {
    /// The argument sorts have no common supersort within the bound.
    NoCommonSort { bound: Option<Box<SemanticSortRef>> },
    /// Several common supersorts are minimal, so none is least.
    Ambiguous(Vec<SemanticSortRef>),
}

impl InstanceError {
    fn message(&self, operation: BuiltinOperation, arguments: &[SemanticSortRef]) -> String {
        let spec = operation.spec();
        let sorts = arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" and ");
        let name = format!("{}::{}", spec.rust_module, spec.rust_name);
        match self {
            Self::NoCommonSort { bound: None } => format!(
                "branches of {name} have sorts {sorts} with no common sort; narrow one with a typed binder or `where`"
            ),
            Self::NoCommonSort { bound: Some(bound) } => format!(
                "branches of {name} have sorts {sorts} with no common sort admissible at sort {bound}; narrow one with a typed binder or `where`"
            ),
            Self::Ambiguous(candidates) => format!(
                "branches of {name} have sorts {sorts} with no least common sort (candidates {}); narrow one with a typed binder or `where`",
                candidates
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

/// The instance of a sort-parametric application, by k-rust's rule (X9.1):
/// the least sort that every argument sort is a subsort of, with the sort
/// expected at the position, when there is one, as an upper bound. A result
/// that is not unique is an error rather than a guess.
pub(super) fn least_instance(
    arguments: &[SemanticSortRef],
    bound: Option<&SemanticSortRef>,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<SemanticSortRef, InstanceError> {
    let mut common: Option<BTreeSet<SemanticSortRef>> = None;
    for sort in arguments {
        let closure = semantic_sort_closure(sort, parents);
        common = Some(match common {
            None => closure,
            Some(common) => common.intersection(&closure).cloned().collect(),
        });
    }
    let mut common = common.unwrap_or_default();
    if let Some(bound) = bound {
        common.retain(|candidate| semantic_is_subsort(candidate, bound, parents));
    }
    let least = common
        .iter()
        .filter(|candidate| {
            !common
                .iter()
                .any(|other| other != *candidate && semantic_is_subsort(other, candidate, parents))
        })
        .cloned()
        .collect::<Vec<_>>();
    match least.as_slice() {
        [instance] => Ok(instance.clone()),
        [] => Err(InstanceError::NoCommonSort {
            bound: bound.cloned().map(Box::new),
        }),
        _ => Err(InstanceError::Ambiguous(least)),
    }
}

pub(super) fn initial_binding_constraints(
    binding_sorts: &BTreeMap<String, SemanticSortRef>,
) -> BTreeMap<String, BTreeSet<SemanticSortRef>> {
    binding_sorts
        .iter()
        .map(|(name, sort)| (name.clone(), BTreeSet::from([sort.clone()])))
        .collect()
}

/// Returns the nearest declared sorts below every occurrence constraint.
///
/// Descendants strictly below another common descendant are redundant: the
/// higher candidate is the greatest lower bound that preserves every value
/// admitted by the occurrence constraints. The stable sort ordering makes an
/// ambiguous result deterministic for diagnostics.
pub(super) fn most_specific_common_descendants(
    constraints: &BTreeSet<SemanticSortRef>,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Vec<SemanticSortRef> {
    let universe = parents
        .keys()
        .chain(parents.values().flatten())
        .chain(constraints)
        .cloned()
        .collect::<BTreeSet<_>>();
    let closures = universe
        .into_iter()
        .map(|candidate| {
            let closure = semantic_sort_closure(&candidate, parents);
            (candidate, closure)
        })
        .collect::<BTreeMap<_, _>>();
    let common = closures
        .iter()
        .filter(|(_, closure)| constraints.is_subset(closure))
        .map(|(candidate, _)| candidate.clone())
        .collect::<BTreeSet<_>>();
    common
        .iter()
        .filter(|candidate| {
            !closures[*candidate]
                .iter()
                .any(|ancestor| ancestor != *candidate && common.contains(ancestor))
        })
        .cloned()
        .collect()
}

/// The fixed signature of a builtin operation whose catalog sorts are all builtin sorts.
fn builtin_production_signature(operation: BuiltinOperation) -> Option<ProductionSignature> {
    Some(ProductionSignature {
        result_sort: SemanticSortRef::Builtin(operation.result_sort().builtin()?),
        fields: operation
            .argument_sorts()
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                Some((
                    ProductionFieldId::new(format!("argument_{index}"))
                        .expect("builtin field identity is valid"),
                    SemanticSortRef::Builtin(sort.builtin()?),
                ))
            })
            .collect::<Option<_>>()?,
        token: false,
        parameters: Vec::new(),
        cons_list_empty: None,
        function: true,
    })
}

struct UpdateArguments<'a> {
    base: &'a DescriptorTerm,
}

impl<'a> UpdateArguments<'a> {
    fn new(
        operation: impl CollectionApplication,
        arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Self, String> {
        let operands = collection_positional_operands(operation, arguments)?;
        let [base, _, _] = <[&DescriptorTerm; 3]>::try_from(operands).map_err(|operands| {
            format!(
                "the {operation} operation expects 3 positional arguments but received {}",
                operands.len()
            )
        })?;
        Ok(Self { base })
    }
}

/// Checks a collection application's arity against its catalog row and returns
/// its operands in wire order.
fn collection_positional_operands<O: CollectionApplication>(
    operation: O,
    arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
) -> Result<Vec<&DescriptorTerm>, String> {
    let expected = operation.spec().arity();
    if arguments.len() != expected {
        return Err(format!(
            "the {operation} operation expects {expected} positional arguments but received {}",
            arguments.len()
        ));
    }
    arguments
        .iter()
        .map(|argument| match argument {
            krs_ir::TermArgumentRef::Positional { value } => Ok(value),
            krs_ir::TermArgumentRef::Named { .. } => {
                Err("builtin collection operations accept positional arguments only".to_owned())
            }
        })
        .collect()
}

/// The sort an operand is inferred and lowered at, if its row fixes one.
fn collection_operand_sort(sort: CollectionOperandSort) -> Option<SemanticSortRef> {
    match sort {
        CollectionOperandSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
        CollectionOperandSort::Element => None,
    }
}

/// [`order_structured_arguments`] for a record that may name no field: an
/// update that lists none, `Ctor { ..t }`, takes every field from its base
/// (F5), and a pattern `Ctor { .. }` leaves every field unconstrained, as
/// in Rust. `Ctor()` and `Ctor {}` still name all of them.
fn order_record_arguments<'a>(
    arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    fields: &[(ProductionFieldId, SemanticSortRef)],
    allow_missing_named: bool,
    fieldless: bool,
) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
    if fieldless && arguments.is_empty() {
        return Ok(vec![None; fields.len()]);
    }
    order_structured_arguments(arguments, fields, allow_missing_named)
}

fn order_structured_arguments<'a>(
    arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    fields: &[(ProductionFieldId, SemanticSortRef)],
    allow_missing_named: bool,
) -> Result<Vec<Option<&'a DescriptorTerm>>, String> {
    if arguments.len() != fields.len() && (!allow_missing_named || !arguments.is_named()) {
        return Err(format!(
            "application expects {} arguments but received {}",
            fields.len(),
            arguments.len()
        ));
    }
    let arguments = match arguments {
        krs_ir::Arguments::Positional(arguments) => {
            return Ok(arguments.iter().map(|value| Some(value.as_ref())).collect());
        }
        krs_ir::Arguments::Named(arguments) => arguments,
    };
    let mut by_name = arguments
        .iter()
        .map(|argument| (argument.field.clone(), argument.value.as_ref()))
        .collect::<BTreeMap<_, _>>();
    let ordered = fields
        .iter()
        .map(|(field, _)| {
            let value = by_name.remove(field);
            if value.is_none() && !allow_missing_named {
                return Err(format!(
                    "named application lacks field {:?}",
                    field.as_str()
                ));
            }
            Ok(value)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some((field, _)) = by_name.into_iter().next() {
        return Err(format!(
            "named application has unknown field {:?}",
            field.as_str()
        ));
    }
    Ok(ordered)
}

/// The sort marker a turbofish names for `sort`: `k::builtin::Int`, or a user
/// sort's `dyn ExpSort` (KF-027).
fn marker_spelling(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Builtin(builtin) => format!("k::builtin::{}", builtin.marker_name()),
        SemanticSortRef::Declared(id) => format!("dyn {}Sort", id.item_name()),
        SemanticSortRef::Cell(_) | SemanticSortRef::Parameter(_) => {
            super::overload::sort_name(sort)
        }
    }
}

#[cfg(test)]
mod instance_tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{BuiltinSort, ItemKind};
    use krs_ir_levels::SemanticSortRef;

    use super::{InstanceError, least_instance};

    fn declared(name: &str) -> SemanticSortRef {
        SemanticSortRef::Declared(krs_ir::testing::item("sorts", name, ItemKind::Sort))
    }

    /// `Int, Bool < Value < Exp < KItem`, and `Left, Right < Both1, Both2`.
    fn graph() -> BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>> {
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let boolean = SemanticSortRef::Builtin(BuiltinSort::Bool);
        BTreeMap::from([
            (int, BTreeSet::from([declared("Value")])),
            (boolean, BTreeSet::from([declared("Value")])),
            (declared("Value"), BTreeSet::from([declared("Exp")])),
            (declared("Exp"), BTreeSet::from([declared("KItem")])),
            (
                declared("Left"),
                BTreeSet::from([declared("Both1"), declared("Both2")]),
            ),
            (
                declared("Right"),
                BTreeSet::from([declared("Both1"), declared("Both2")]),
            ),
        ])
    }

    #[test]
    fn the_instance_is_the_least_sort_of_the_branches_below_the_position() {
        let parents = graph();
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let boolean = SemanticSortRef::Builtin(BuiltinSort::Bool);
        // Two Int branches at an Exp position: the instance is Int, then injected.
        assert_eq!(
            least_instance(
                &[int.clone(), int.clone()],
                Some(&declared("Exp")),
                &parents
            ),
            Ok(int.clone())
        );
        assert_eq!(
            least_instance(
                &[declared("Exp"), declared("Exp")],
                Some(&declared("Exp")),
                &parents
            ),
            Ok(declared("Exp"))
        );
        assert_eq!(
            least_instance(&[int.clone(), boolean.clone()], None, &parents),
            Ok(declared("Value"))
        );
        assert_eq!(
            least_instance(
                &[int.clone(), declared("Exp")],
                Some(&declared("KItem")),
                &parents
            ),
            Ok(declared("Exp"))
        );
    }

    #[test]
    fn branches_without_a_unique_least_sort_are_rejected() {
        let parents = graph();
        let int = SemanticSortRef::Builtin(BuiltinSort::Int);
        let map = SemanticSortRef::Builtin(BuiltinSort::Map);
        assert_eq!(
            least_instance(&[int.clone(), map], None, &parents),
            Err(InstanceError::NoCommonSort { bound: None })
        );
        // The least common sort Value is above the Int position.
        assert_eq!(
            least_instance(
                &[int.clone(), SemanticSortRef::Builtin(BuiltinSort::Bool)],
                Some(&int),
                &parents
            ),
            Err(InstanceError::NoCommonSort {
                bound: Some(Box::new(int.clone()))
            })
        );
        assert_eq!(
            least_instance(&[declared("Left"), declared("Right")], None, &parents),
            Err(InstanceError::Ambiguous(vec![
                declared("Both1"),
                declared("Both2")
            ]))
        );
    }
}
