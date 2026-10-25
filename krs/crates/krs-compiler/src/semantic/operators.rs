//! Operators (`a + b`, `a == b`, `!a`): the builtin domain each one reads in,
//! chosen from its operands' inferred sorts.
//!
//! An operator names an operation but not its domain. Each builtin domain
//! defines its operations on that domain only, so an operand whose sort is a
//! domain, or a subsort of one, pins the operator to that domain: no other
//! reading is well sorted. An operator whose operands pin one domain denotes
//! that domain's operation, and from then on it is inferred, checked, and
//! lowered exactly as the call it denotes; every later phase sees an ordinary
//! builtin application. Operands that pin no domain, or two, are an error that
//! names the explicit forms, and nothing is guessed.
//!
//! An operand's sort may only be known after other parts of the sentence are
//! inferred, as when `x + y` precedes the pattern that binds `y` to an `Int`.
//! [`StructuredTermBuilder::infer_sentence`] therefore repeats inference until
//! no further operator is decided. Binder constraints only grow from one pass
//! to the next, and a binder's final sort lies below every constraint, so a
//! domain pinned by the constraints known so far is the domain its final sort
//! pins.

use std::collections::BTreeMap;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinOperator, BuiltinSort, CollectionResultSort,
    DescriptorApplicationRef, DescriptorApplicationReference, DescriptorPayload, DescriptorTerm,
    OperationSort, OperatorDomain, OperatorReading, ProvenanceKey, SortTestKind,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::catalog::{semantic_is_subsort, semantic_sort_ref};
use super::error::{DescriptorLoweringError, OperatorProblem};
use super::infer::{StructuredTermBuilder, most_specific_common_descendants};
use super::origin::semantic_origin;

/// The operator domains of one sentence, decided across inference passes.
#[derive(Default)]
pub(super) struct OperatorInference {
    /// The domain chosen for each operator, by its head's provenance key.
    domains: BTreeMap<ProvenanceKey, OperatorDomain>,
    /// The error for the first operator of the current pass whose operands
    /// chose no domain, reported if a further pass decides nothing more.
    pending: Option<DescriptorLoweringError>,
}

/// What the operands of one operator choose.
enum DomainChoice {
    /// One domain.
    Chosen(OperatorDomain),
    /// None yet: no operand's sort is known to lie in a domain.
    Unknown(Vec<Option<SemanticSortRef>>),
    /// Two domains.
    Conflict(Vec<Option<SemanticSortRef>>, Vec<OperatorDomain>),
    /// None ever: an operand has a builtin sort that has no operators.
    Foreign(Vec<Option<SemanticSortRef>>, BuiltinSort),
}

impl StructuredTermBuilder<'_> {
    /// Runs `pass`, which infers every term of one sentence, until no further
    /// operator's domain is decided; an operator still undecided then is an
    /// error. A sentence without an undecided operator takes one pass.
    ///
    /// # Errors
    ///
    /// Returns the first error of a pass, or
    /// [`DescriptorLoweringError::InvalidOperator`] for an operator whose
    /// operands never choose a domain.
    pub(super) fn infer_sentence(
        &mut self,
        mut pass: impl FnMut(&mut Self) -> Result<(), DescriptorLoweringError>,
    ) -> Result<(), DescriptorLoweringError> {
        let mut first = true;
        loop {
            let decided = self.operators.domains.len();
            self.operators.pending = None;
            pass(self)?;
            let Some(pending) = self.operators.pending.take() else {
                return Ok(());
            };
            // A pass that decides nothing adds no constraint the next pass
            // would not repeat, except that the first pass also collects the
            // constraints of everything after an undecided operator.
            if !first && self.operators.domains.len() == decided {
                return Err(pending);
            }
            first = false;
        }
    }

    /// Infers an operator application: as the call of its domain's operation
    /// once its operands choose the domain, and otherwise its operands alone,
    /// leaving the operator for a later pass.
    pub(super) fn infer_operator(
        &mut self,
        reference: &DescriptorApplicationReference,
        operator: BuiltinOperator,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let operands = self.operator_operands(operator, arguments)?;
        let domain = if let Some(domain) = self.operators.domains.get(&reference.key) {
            *domain
        } else {
            match self.operator_domain(&operands) {
                DomainChoice::Chosen(domain) => {
                    self.operators.domains.insert(reference.key.clone(), domain);
                    domain
                }
                DomainChoice::Unknown(sorts) => {
                    if self.operators.pending.is_none() {
                        self.operators.pending = Some(self.ambiguous_operator(
                            &reference.key,
                            operator,
                            &operands,
                            &sorts,
                            &[],
                        ));
                    }
                    if let Some(result) = operator.uniform_result() {
                        self.check_operator_result(
                            &reference.key,
                            operator,
                            result,
                            expected_sort,
                        )?;
                    }
                    for operand in operands {
                        self.infer(operand, None, subject)?;
                    }
                    return Ok(());
                }
                DomainChoice::Conflict(sorts, domains) => {
                    return Err(self.ambiguous_operator(
                        &reference.key,
                        operator,
                        &operands,
                        &sorts,
                        &domains,
                    ));
                }
                DomainChoice::Foreign(sorts, sort) => {
                    return Err(self.foreign_operator(&reference.key, operator, &sorts, sort));
                }
            }
        };
        let reading = self.operator_reading(&reference.key, operator, domain)?;
        if let Some(result) = reading.operation().result_sort().builtin() {
            self.check_operator_result(&reference.key, operator, result, expected_sort)?;
        }
        match reading {
            OperatorReading::Operation(operation) => self.infer_application(
                &builtin_reference(reference, operation),
                arguments,
                &[],
                expected_sort,
                super::infer::Partial::new(subject, None, false),
            ),
            OperatorReading::IntNegation => self.infer(
                operands[0],
                Some(&SemanticSortRef::Builtin(BuiltinSort::Int)),
                subject,
            ),
        }
    }

    /// Lowers an operator application as the call of the operation of the
    /// domain inference chose for it; `-x` on `Int` is `int::sub(0, x)`.
    pub(super) fn lower_operator(
        &mut self,
        reference: &DescriptorApplicationReference,
        operator: BuiltinOperator,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
        head: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let domain = *self.operators.domains.get(&reference.key).ok_or_else(|| {
            self.invalid_term(format!(
                "operator `{}` was lowered before inference chose its domain",
                operator.symbol()
            ))
        })?;
        match self.operator_reading(&reference.key, operator, domain)? {
            OperatorReading::Operation(operation) => self.lower_application(
                &builtin_reference(reference, operation),
                arguments,
                &[],
                expected_sort,
                &super::infer::RecordContext {
                    alias: None,
                    update: None,
                    subject,
                    open: false,
                },
                head,
            ),
            OperatorReading::IntNegation => {
                let operands = self.operator_operands(operator, arguments)?;
                let int = SemanticSortRef::Builtin(BuiltinSort::Int);
                let operand = self.lower(operands[0], Some(&int), subject)?;
                let zero = SemanticTerm::token(
                    semantic_origin(
                        self.descriptor,
                        reference.key.clone(),
                        "operator-negation-zero",
                    )?,
                    int.clone(),
                    "0".to_owned(),
                )?;
                Ok(SemanticTerm::application(
                    semantic_origin(self.descriptor, reference.key.clone(), "term-application")?,
                    int,
                    ApplicationRef::Builtin(BuiltinOperation::IntSub),
                    vec![zero, operand],
                ))
            }
        }
    }

    /// The operands of an operator application, which has exactly the
    /// operator's arity of positional arguments.
    fn operator_operands<'t>(
        &self,
        operator: BuiltinOperator,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Vec<&'t DescriptorTerm>, DescriptorLoweringError> {
        let operands = arguments
            .iter()
            .filter_map(|argument| match argument {
                krs_ir::TermArgumentRef::Positional { value } => Some(value),
                krs_ir::TermArgumentRef::Named { .. } => None,
            })
            .collect::<Vec<_>>();
        if arguments.is_named() || operands.len() != operator.arity() {
            return Err(self.invalid_term(format!(
                "operator `{}` takes {} positional operands",
                operator.symbol(),
                operator.arity()
            )));
        }
        Ok(operands)
    }

    /// The reading of `operator` in `domain`, or the error naming what to
    /// write instead.
    fn operator_reading(
        &self,
        key: &ProvenanceKey,
        operator: BuiltinOperator,
        domain: OperatorDomain,
    ) -> Result<OperatorReading, DescriptorLoweringError> {
        operator
            .reading(domain)
            .ok_or_else(|| self.undefined_operator(key, operator, domain))
    }

    /// Checks the operator's result sort at its position, naming the
    /// operator as written.
    fn check_operator_result(
        &self,
        key: &ProvenanceKey,
        operator: BuiltinOperator,
        result: BuiltinSort,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<(), DescriptorLoweringError> {
        let result = SemanticSortRef::Builtin(result);
        self.admit(
            key,
            || super::collection_types::operator_spelling(operator),
            &result,
            expected_sort,
            |expected| {
                format!("application result sort {result} is not admissible at sort {expected}")
            },
        )
    }

    /// The domain an operator's operands choose from the sorts known so far.
    fn operator_domain(&self, operands: &[&DescriptorTerm]) -> DomainChoice {
        let sorts = operands
            .iter()
            .map(|operand| self.operand_sort(operand))
            .collect::<Vec<_>>();
        let mut domains = Vec::new();
        let mut foreign = None;
        for sort in sorts.iter().flatten() {
            let pinned = OperatorDomain::ALL.into_iter().filter(|domain| {
                semantic_is_subsort(
                    sort,
                    &SemanticSortRef::Builtin(domain.sort()),
                    self.sort_parents,
                )
            });
            let before = domains.len();
            for domain in pinned {
                if !domains.contains(&domain) {
                    domains.push(domain);
                }
            }
            if domains.len() == before
                && let SemanticSortRef::Builtin(builtin) = sort
                && *builtin != BuiltinSort::KSequence
                && OperatorDomain::of_sort(*builtin).is_none()
            {
                foreign.get_or_insert(*builtin);
            }
        }
        domains.sort();
        match (domains.as_slice(), foreign) {
            ([domain], _) => DomainChoice::Chosen(*domain),
            ([], Some(sort)) => DomainChoice::Foreign(sorts, sort),
            ([], None) => DomainChoice::Unknown(sorts),
            _ => DomainChoice::Conflict(sorts, domains),
        }
    }

    /// The sort a term is known to have before it is inferred at a position:
    /// a literal's, a binder's from its constraints so far, an application's
    /// result, or a comparison's `Bool`. `None` when it is not yet known.
    fn operand_sort(&self, term: &DescriptorTerm) -> Option<SemanticSortRef> {
        match term {
            DescriptorTerm::Variable { name, .. } => self.binder_sort(name),
            DescriptorTerm::Literal { literal, .. } => {
                Some(SemanticSortRef::Builtin(match literal {
                    krs_ir::DescriptorLiteral::Int(_) => BuiltinSort::Int,
                    krs_ir::DescriptorLiteral::Bool(_) => BuiltinSort::Bool,
                    krs_ir::DescriptorLiteral::String(_) => BuiltinSort::String,
                    krs_ir::DescriptorLiteral::Float(_) => BuiltinSort::Float,
                }))
            }
            DescriptorTerm::BuiltinToken { sort, .. } => Some(SemanticSortRef::Builtin(*sort)),
            DescriptorTerm::Anonymous { sort, .. } => Some(semantic_sort_ref(&sort.sort)),
            DescriptorTerm::OrBool { .. } | DescriptorTerm::Matches { .. } => {
                Some(SemanticSortRef::Builtin(BuiltinSort::Bool))
            }
            DescriptorTerm::SortTest { kind, sort, .. } => Some(match kind {
                SortTestKind::Predicate => SemanticSortRef::Builtin(BuiltinSort::Bool),
                SortTestKind::Projection => semantic_sort_ref(&sort.sort),
            }),
            DescriptorTerm::Let { body, .. } => self.operand_sort(body),
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => self.application_sort(reference, arguments),
            DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::Cell { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::As { .. }
            | DescriptorTerm::Or { .. }
            | DescriptorTerm::Closure { .. }
            | DescriptorTerm::Rewrite { .. } => None,
        }
    }

    /// The sort a binder is known to have: its declared or resolved sort, or
    /// the one greatest sort below every constraint collected so far. A local
    /// binder's sort is not known before its scope is lowered.
    fn binder_sort(&self, name: &str) -> Option<SemanticSortRef> {
        if self.is_let_local_name(name) || self.is_inferring_local(name) {
            return None;
        }
        if let Some(sort) = self.binding_sorts.get(name) {
            return Some(sort.clone());
        }
        let constraints = self.binding_constraints.get(name)?;
        match most_specific_common_descendants(constraints, self.sort_parents).as_slice() {
            [sort] => Some(sort.clone()),
            _ => None,
        }
    }

    fn application_sort(
        &self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Option<SemanticSortRef> {
        match &reference.application {
            DescriptorApplicationRef::Declared(id) => self
                .catalog
                .get(id)
                .filter(|signature| signature.parameters.is_empty())
                .map(|signature| signature.result_sort.clone()),
            DescriptorApplicationRef::Builtin(operation) => match operation.result_sort() {
                OperationSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
                OperationSort::K | OperationSort::Parameter => None,
            },
            DescriptorApplicationRef::Map(operation) => {
                collection_result(operation.spec().result_sort).or_else(|| {
                    self.collections
                        .projection(&reference.key)
                        .map(|site| site.sort.clone())
                        .or_else(|| self.collections.untyped_element().cloned())
                })
            }
            DescriptorApplicationRef::List(operation) => {
                collection_result(operation.spec().result_sort).or_else(|| {
                    self.collections
                        .projection(&reference.key)
                        .map(|site| site.sort.clone())
                        .or_else(|| self.collections.untyped_element().cloned())
                })
            }
            DescriptorApplicationRef::Set(operation) => {
                collection_result(operation.spec().result_sort).or_else(|| {
                    self.collections
                        .projection(&reference.key)
                        .map(|site| site.sort.clone())
                        .or_else(|| self.collections.untyped_element().cloned())
                })
            }
            // A list's sort is the position's, which an operand does not have.
            DescriptorApplicationRef::Ml(_) | DescriptorApplicationRef::ListNotation(_) => None,
            DescriptorApplicationRef::Operator(operator) => {
                if let Some(result) = operator.uniform_result() {
                    return Some(SemanticSortRef::Builtin(result));
                }
                let domain = if let Some(domain) = self.operators.domains.get(&reference.key) {
                    *domain
                } else {
                    let operands = self.operator_operands(*operator, arguments).ok()?;
                    let DomainChoice::Chosen(domain) = self.operator_domain(&operands) else {
                        return None;
                    };
                    domain
                };
                let reading = operator.reading(domain)?;
                reading
                    .operation()
                    .result_sort()
                    .builtin()
                    .map(SemanticSortRef::Builtin)
            }
        }
    }

    /// The error for operands that choose no domain or two. A binder that no
    /// occurrence sorts, or sorts no more precisely than `KItem` (an element
    /// of a bare collection), is named, with the narrowing that says which
    /// domain is meant.
    fn ambiguous_operator(
        &self,
        key: &ProvenanceKey,
        operator: BuiltinOperator,
        operands: &[&DescriptorTerm],
        sorts: &[Option<SemanticSortRef>],
        domains: &[OperatorDomain],
    ) -> DescriptorLoweringError {
        let alternative = if operator == BuiltinOperator::BitOr && domains.is_empty() {
            "; `|` joins pattern alternatives only on a left-hand side"
        } else {
            ""
        };
        let forms = explicit_forms(operator);
        let unsorted = operands
            .iter()
            .zip(sorts)
            .map(|(operand, sort)| match operand {
                DescriptorTerm::Variable { name, .. }
                    if !self.is_let_local_name(name)
                        && !self.is_inferring_local(name)
                        && sort.as_ref().is_none_or(is_k_item) =>
                {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let names = unsorted.iter().flatten().copied().collect::<Vec<_>>();
        let reason = if domains.is_empty() && !names.is_empty() {
            self.unsorted_operands(operator, &unsorted, sorts, &forms, alternative)
        } else {
            let choice = if domains.is_empty() {
                "which choose no builtin domain".to_owned()
            } else {
                format!(
                    "which choose the domains {}",
                    prose_list(
                        &domains
                            .iter()
                            .map(|domain| format!("`{}`", domain.name()))
                            .collect::<Vec<_>>(),
                        "and"
                    )
                )
            };
            format!(
                "`{}` has {}, {choice}; write the operation you mean: {forms}{alternative}",
                operator.symbol(),
                describe_sorts(sorts),
            )
        };
        self.operator_error(key, OperatorProblem::Ambiguous, reason)
    }

    /// The reason of an ambiguous operator some of whose operands are
    /// binders `unsorted` names, which no occurrence sorts more precisely
    /// than `KItem`: the binders and the narrowing that picks a domain.
    fn unsorted_operands(
        &self,
        operator: BuiltinOperator,
        unsorted: &[Option<&str>],
        sorts: &[Option<SemanticSortRef>],
        forms: &str,
        alternative: &str,
    ) -> String {
        let names = unsorted.iter().flatten().copied().collect::<Vec<_>>();
        let operands = if names.len() == unsorted.len() {
            let sorted = if sorts.iter().all(Option::is_none) {
                String::new()
            } else {
                " more precisely than `KItem`".to_owned()
            };
            let (noun, verb) = if names.len() == 1 {
                ("the operand", "it chooses")
            } else {
                ("operands", "they choose")
            };
            format!(
                "{noun} {}, which no occurrence sorts{sorted}, so {verb} no builtin domain",
                prose_list(
                    &names
                        .iter()
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>(),
                    "and"
                )
            )
        } else {
            let described = unsorted
                .iter()
                .zip(sorts)
                .map(|(name, sort)| match (name, sort) {
                    (Some(name), Some(_)) => {
                        format!("`{name}`, which no occurrence sorts more precisely than `KItem`,")
                    }
                    (Some(name), None) => format!("`{name}`, which no occurrence sorts,"),
                    (None, Some(sort)) => {
                        format!("an operand of sort `{}`", super::overload::sort_name(sort))
                    }
                    (None, None) => "an operand of an unknown sort".to_owned(),
                })
                .collect::<Vec<_>>();
            format!(
                "operands {}, which choose no builtin domain",
                prose_list(&described, "and")
            )
        };
        let domain = operator
            .domains()
            .first()
            .map_or("Int", |domain| domain.name());
        let narrowing = if matches!(self.descriptor.payload(), DescriptorPayload::HeadRule(_)) {
            format!(
                "`where {}`",
                names
                    .iter()
                    .map(|name| format!("{name}: {domain}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            format!(
                "the typed binders `{}`",
                names
                    .iter()
                    .map(|name| format!("{name}: Term<{domain}>"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let them = if names.len() == 1 { "it" } else { "them" };
        format!(
            "`{}` has {operands}; narrow {them} ({narrowing}) or write the operation you mean: {forms}{alternative}",
            operator.symbol(),
        )
    }

    /// The error for an operand of a builtin sort that has no operators.
    fn foreign_operator(
        &self,
        key: &ProvenanceKey,
        operator: BuiltinOperator,
        sorts: &[Option<SemanticSortRef>],
        sort: BuiltinSort,
    ) -> DescriptorLoweringError {
        let instead = if matches!(operator, BuiltinOperator::Eq | BuiltinOperator::Ne) {
            format!(
                "compare the terms with `a.{}::<K>(b)`",
                if operator == BuiltinOperator::Eq {
                    "eq"
                } else {
                    "ne"
                }
            )
        } else {
            "write the operation as a call".to_owned()
        };
        self.operator_error(
            key,
            OperatorProblem::Ambiguous,
            format!(
                "`{}` has {}, and `{}` has no operators, which read only in `Int`, `Bool`, `String`, and `Float`; {instead}",
                operator.symbol(),
                describe_sorts(sorts),
                SemanticSortRef::Builtin(sort)
            ),
        )
    }

    /// The error for an operator its operands' domain does not define.
    fn undefined_operator(
        &self,
        key: &ProvenanceKey,
        operator: BuiltinOperator,
        domain: OperatorDomain,
    ) -> DescriptorLoweringError {
        let symbol = operator.symbol();
        let reason = match (operator, domain) {
            (BuiltinOperator::BitAnd, OperatorDomain::Bool) => {
                "`&` is not a `Bool` connective: Rust's precedence would make `a == b & c == d` a parse error; write `a && b`, or `bool::and(a, b)` to evaluate both operands".to_owned()
            }
            (BuiltinOperator::BitOr, OperatorDomain::Bool) => {
                "`|` is not a `Bool` connective: Rust's precedence would make `a == b | c == d` a parse error; write `a || b`, or `bool::or(a, b)` to evaluate both operands".to_owned()
            }
            (BuiltinOperator::BitXor, OperatorDomain::Bool) => {
                "`^` is not a `Bool` operation; write `bool::xor(a, b)` or `a != b`".to_owned()
            }
            _ => {
                let defined = BuiltinOperator::ALL
                    .into_iter()
                    .filter(|candidate| candidate.reading(domain).is_some())
                    .map(|candidate| match candidate {
                        BuiltinOperator::Neg => "unary `-`".to_owned(),
                        _ => format!("`{}`", candidate.symbol()),
                    })
                    .collect::<Vec<_>>();
                let unary = if operator.arity() == 1 { "unary " } else { "" };
                format!(
                    "{unary}`{symbol}` is not an operation of `{}`, whose operators are {}; write the operation you mean as a call",
                    domain.name(),
                    prose_list(&defined, "and")
                )
            }
        };
        self.operator_error(key, OperatorProblem::Undefined, reason)
    }

    fn operator_error(
        &self,
        key: &ProvenanceKey,
        problem: OperatorProblem,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidOperator {
            item: Box::new(self.descriptor.id().clone()),
            problem,
            reason,
            range: self.authored_range(key),
        }
    }
}

/// The reference of the call an operator denotes: the operation, at the
/// operator's own key.
fn builtin_reference(
    reference: &DescriptorApplicationReference,
    operation: BuiltinOperation,
) -> DescriptorApplicationReference {
    DescriptorApplicationReference {
        key: reference.key.clone(),
        application: DescriptorApplicationRef::Builtin(operation),
    }
}

fn collection_result(result: CollectionResultSort) -> Option<SemanticSortRef> {
    match result {
        CollectionResultSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
        CollectionResultSort::Projected => None,
    }
}

/// Whether `sort` is the framework's `KItem`, the sort of every element of a
/// bare collection, which pins no operator domain.
fn is_k_item(sort: &SemanticSortRef) -> bool {
    matches!(sort, SemanticSortRef::Declared(id)
        if id.item_name() == "KItem" && id.package().k_namespace() == "KRS-FRAMEWORK")
}

/// `` operands of sorts `Exp` and `Int` `` or `` an operand of an unknown sort ``.
fn describe_sorts(sorts: &[Option<SemanticSortRef>]) -> String {
    let described = sorts
        .iter()
        .map(|sort| match sort {
            Some(sort) => format!("`{}`", super::overload::sort_name(sort)),
            None => "an unknown sort".to_owned(),
        })
        .collect::<Vec<_>>();
    match described.as_slice() {
        [only] if only.starts_with('`') => format!("an operand of sort {only}"),
        [only] => format!("an operand of {only}"),
        _ => format!("operands of sorts {}", prose_list(&described, "and")),
    }
}

/// The method or call forms that name each domain of `operator` explicitly.
fn explicit_forms(operator: BuiltinOperator) -> String {
    let mut forms = operator
        .domains()
        .into_iter()
        .filter_map(|domain| Some((domain, operator.reading(domain)?)))
        .map(|(domain, reading)| {
            let spec = reading.operation().spec();
            match (reading, operator.arity()) {
                (OperatorReading::IntNegation, _) => "`int::sub(0, a)`".to_owned(),
                (_, 1) => format!("`a.{}::<{}>()`", spec.rust_name, domain.name()),
                _ => format!("`a.{}::<{}>(b)`", spec.rust_name, domain.name()),
            }
        })
        .collect::<Vec<_>>();
    match operator {
        BuiltinOperator::Eq => forms.push("`a.eq::<K>(b)` to compare terms".to_owned()),
        BuiltinOperator::Ne => forms.push("`a.ne::<K>(b)` to compare terms".to_owned()),
        _ => {}
    }
    prose_list(&forms, "or")
}

fn prose_list(items: &[String], conjunction: &str) -> String {
    match items {
        [] => String::new(),
        [only] => only.clone(),
        [first, second] => format!("{first} {conjunction} {second}"),
        [rest @ .., last] => format!("{}, {conjunction} {last}", rest.join(", ")),
    }
}
