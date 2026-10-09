use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CollectionApplication, CollectionOperandSort,
    CollectionResultSort, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorIndex, DescriptorPayload, DescriptorTerm, GeneratedOperation, ListOperation,
    OperationSort, ProductionFieldId, ProtocolCellContent, ProvenanceKey, SemanticId, SortTestKind,
    StableItemId,
};
use krs_ir_levels::{
    ListOperands, MapOperands, SemanticSortRef, SemanticTerm, SemanticVariable, SetOperands,
};

use super::catalog::{
    ProductionSignature, semantic_is_subsort, semantic_sort_closure, semantic_sort_ref,
};
use super::error::DescriptorLoweringError;
use super::origin::{semantic_cell_id, semantic_origin};

/// The reason given for `A | B` outside a left-hand side (KF-030).
const PATTERN_OR_OUTSIDE_LHS: &str = "`|` is a pattern alternative (K's #Or) and occurs only on a left-hand side; for Bool disjunction use bool::or or k::or_bool!";

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

/// The reason given for a `let` block in a pattern (KF-032).
const LET_IN_PATTERN: &str =
    "a `let` block (K's #let) is a term; it cannot appear on a left-hand side or inside a pattern";

impl StructuredTermBuilder<'_> {
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive inference over the closed descriptor term sum."
    )]
    pub(super) fn infer(
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
            DescriptorTerm::Variable { name, .. } => {
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
                let sort = match literal {
                    krs_ir::DescriptorLiteral::Int(_) => SemanticSortRef::Builtin(BuiltinSort::Int),
                    krs_ir::DescriptorLiteral::Bool(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::Bool)
                    }
                    krs_ir::DescriptorLiteral::String(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::String)
                    }
                    krs_ir::DescriptorLiteral::Float(_) => {
                        SemanticSortRef::Builtin(BuiltinSort::Float)
                    }
                };
                if let Some(expected) = expected_sort
                    && !semantic_is_subsort(&sort, expected, self.sort_parents)
                {
                    return Err(self.invalid_term(format!(
                        "literal of sort {sort} is not admissible at sort {expected}"
                    )));
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                instance,
                ..
            } => self.infer_application(reference, arguments, instance, expected_sort, subject)?,
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
                self.infer_cell_fields(declaration, fields, subject)?;
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
        }
        Ok(())
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

    fn is_inferring_local(&self, name: &str) -> bool {
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

    fn infer_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
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
                subject,
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
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::List(operation) => {
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
            }
            DescriptorApplicationRef::Set(operation) => {
                self.infer_collection_operation(*operation, arguments, expected_sort, subject)?;
                return Ok(());
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
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
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
            OperationSort::K => {
                return Err(
                    self.invalid_term(format!("builtin operation {operation} has no result sort"))
                );
            }
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
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(operation, expected_sort)?;
        if let Some(expected) = expected_sort
            && !semantic_is_subsort(&result_sort, expected, self.sort_parents)
        {
            return Err(self.invalid_term(format!(
                "{} operation result sort {result_sort} is not admissible at sort {expected}",
                O::SORT.k_name()
            )));
        }
        for (operand, sort) in operands.into_iter().zip(operation.spec().operand_sorts) {
            self.infer(operand, collection_operand_sort(*sort).as_ref(), subject)?;
        }
        Ok(())
    }

    /// Lowers a collection application's operands, in wire order, with its result sort.
    fn lower_collection_operands<O: CollectionApplication>(
        &mut self,
        operation: O,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(SemanticSortRef, Vec<SemanticTerm>), DescriptorLoweringError> {
        let operands = collection_positional_operands(operation, arguments)
            .map_err(|detail| self.invalid_term(detail))?;
        let result_sort = self.collection_result_sort(operation, expected_sort)?;
        let lowered = operands
            .into_iter()
            .zip(operation.spec().operand_sorts)
            .map(|(operand, sort)| {
                self.lower(operand, collection_operand_sort(*sort).as_ref(), subject)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok((result_sort, lowered))
    }

    fn collection_result_sort<O: CollectionApplication>(
        &self,
        operation: O,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<SemanticSortRef, DescriptorLoweringError> {
        match operation.spec().result_sort {
            CollectionResultSort::Builtin(sort) => Ok(SemanticSortRef::Builtin(sort)),
            CollectionResultSort::Projected => expected_sort.cloned().ok_or_else(|| {
                let marker = operation.facade_marker();
                self.invalid_term(format!(
                    "{}::{} requires an expected result sort",
                    marker.module, marker.name
                ))
            }),
        }
    }

    pub(super) fn infer_collection_update(
        &mut self,
        update: &DescriptorTerm,
        base_binding: &str,
        cell_sort: &SemanticSortRef,
        map_sorts: Option<&(SemanticSortRef, SemanticSortRef)>,
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
        let UpdateArguments { base, key, value } = ordered;
        let DescriptorTerm::Variable { name, .. } = base else {
            return Err(
                self.invalid_term("updated-cell base is not the matched whole-collection binding")
            );
        };
        if name != base_binding {
            return Err(self.invalid_term(format!(
                "updated-cell base {name:?} does not match {base_binding:?}"
            )));
        }
        self.infer(base, Some(cell_sort), false)?;
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        match cell_sort {
            SemanticSortRef::Builtin(BuiltinSort::Map) => {
                self.infer(key, map_sorts.map(|(key_sort, _)| key_sort), false)?;
                self.infer(value, map_sorts.map(|(_, value_sort)| value_sort), false)
            }
            SemanticSortRef::Builtin(BuiltinSort::List) => {
                self.infer(key, Some(&int_sort), false)?;
                self.infer(value, None, false)
            }
            _ => Err(self.invalid_term("only Map and List cells support readable updates")),
        }
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
                [] => {
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
        Ok(())
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive lowering over the closed descriptor term sum."
    )]
    pub(super) fn lower(
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
                            "`{name}` is bound by a `let` at sort `{}`, which is not admissible at sort `{}`",
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
                ..
            } => {
                let head = std::mem::take(&mut self.head_pending);
                self.lower_application(reference, arguments, instance, expected_sort, subject, head)
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
            } => self.lower_cell_term(key, declaration, fields, expected_sort, subject),
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
                let pattern = self.lower(pattern, Some(&sort), subject)?;
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
            DescriptorApplicationRef::Declared(_) | DescriptorApplicationRef::Builtin(_) => false,
        };
        projected.then(|| {
            self.k_item_sort
                .clone()
                .unwrap_or(SemanticSortRef::Builtin(BuiltinSort::KSequence))
        })
    }

    fn lower_application(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        instance: &[krs_ir::DescriptorSortReference],
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
        head: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
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
                subject,
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
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
                let operands = MapOperands::from_operands((*operation).into(), operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::typed_map(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-map-operation")?,
                    result_sort,
                    operands,
                ));
            }
            DescriptorApplicationRef::List(operation) => {
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
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
                let (result_sort, operands) =
                    self.lower_collection_operands(*operation, arguments, expected_sort, subject)?;
                let operands = SetOperands::from_operands(*operation, operands)
                    .map_err(|error| self.invalid_term(error.to_string()))?;
                return Ok(SemanticTerm::set(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-set-operation")?,
                    result_sort,
                    operands,
                ));
            }
        };
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
            .map_err(|detail| self.invalid_term(detail))?;
        let lowered = ordered
            .into_iter()
            .zip(&signature.fields)
            .map(|(argument, (_, sort))| match argument {
                Some(argument) => self.lower(argument, Some(sort), subject),
                None => self.lower_record_rest_wildcard(sort),
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
    ) -> Result<(), DescriptorLoweringError> {
        let declaration = self.cell_declaration(owner)?.clone();
        let supplied = fields
            .iter()
            .map(|field| (field.field.clone(), field))
            .collect::<BTreeMap<_, _>>();
        if supplied.len() != fields.len() || supplied.len() != declaration.fields.len() {
            return Err(self.invalid_term(format!(
                "fragment! for {:?} must provide every child field exactly once",
                owner.item_name()
            )));
        }
        for declared in &declaration.fields {
            let field = supplied
                .get(&ProductionFieldId::new(&declared.rust_field)?)
                .ok_or_else(|| {
                    self.invalid_term(format!(
                        "fragment! for {:?} is missing child field {:?}",
                        owner.item_name(),
                        declared.rust_field
                    ))
                })?;
            match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    self.infer(&field.value, Some(&semantic_sort_ref(&sort.sort)), subject)?;
                }
                ProtocolCellContent::Nested {
                    declaration: nested,
                } => {
                    let DescriptorTerm::Cell { declaration, .. } = field.value.as_ref() else {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} must be authored with fragment!",
                            declared.rust_field
                        )));
                    };
                    if declaration != &nested.declaration {
                        return Err(self.invalid_term(format!(
                            "nested child {:?} uses the wrong cell declaration",
                            declared.rust_field
                        )));
                    }
                    self.infer(&field.value, Some(&self.cell_k_item_sort()?), subject)?;
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
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
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
            let field = supplied.get(&field_id).ok_or_else(|| {
                self.invalid_term(format!(
                    "fragment! is missing child field {:?}",
                    declared.rust_field
                ))
            })?;
            let child = match &declared.content {
                ProtocolCellContent::Leaf { sort, .. } => {
                    let content_sort = semantic_sort_ref(&sort.sort);
                    let content = self.lower(&field.value, Some(&content_sort), subject)?;
                    SemanticTerm::cell(
                        semantic_origin(self.descriptor, field.key.clone(), "cell-term-child")?,
                        self.cell_k_item_sort()?,
                        semantic_cell_id(&declared.reference.cell)?,
                        vec![content],
                    )
                }
                ProtocolCellContent::Nested { .. } => {
                    self.lower(&field.value, Some(&self.cell_k_item_sort()?), subject)?
                }
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
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
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
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
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
        subject: bool,
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
        let ordered = order_structured_arguments(arguments, &signature.fields, subject)
            .map_err(|detail| self.invalid_term(detail))?;
        let mut lowered = Vec::with_capacity(sorts.len());
        let mut variables = Vec::with_capacity(sorts.len());
        for (argument, sort) in ordered.into_iter().zip(&sorts) {
            // A record rest (`..`) is a wildcard, so it counts as a variable.
            variables.push(argument.is_none_or(|argument| {
                matches!(
                    argument,
                    DescriptorTerm::Variable { .. } | DescriptorTerm::Wildcard { .. }
                )
            }));
            let term = if let Some(argument) = argument {
                self.lower(argument, sort.as_ref(), subject)?
            } else {
                let sort = sort.clone().ok_or_else(|| {
                    self.invalid_term("a record rest at a parameter position needs a turbofish")
                })?;
                self.lower_record_rest_wildcard(&sort)?
            };
            lowered.push(term);
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

    fn authored_range(&self, key: &ProvenanceKey) -> Option<Box<krs_ir::SourceRange>> {
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

    fn invalid_term(&self, detail: impl Into<String>) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidTerm {
            id: Box::new(self.descriptor.id().clone()),
            detail: detail.into(),
        }
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
        DescriptorTerm::Let { .. }
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
fn most_specific_common_descendants(
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
        function: true,
    })
}

struct UpdateArguments<'a> {
    base: &'a DescriptorTerm,
    key: &'a DescriptorTerm,
    value: &'a DescriptorTerm,
}

impl<'a> UpdateArguments<'a> {
    fn new(
        operation: impl CollectionApplication,
        arguments: &'a krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Self, String> {
        let operands = collection_positional_operands(operation, arguments)?;
        let [base, key, value] =
            <[&DescriptorTerm; 3]>::try_from(operands).map_err(|operands| {
                format!(
                    "the {operation} operation expects 3 positional arguments but received {}",
                    operands.len()
                )
            })?;
        Ok(Self { base, key, value })
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
