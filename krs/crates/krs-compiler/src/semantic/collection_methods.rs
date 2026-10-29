//! Index reads and collection methods (`m[k]`, `s.contains(x)`): the
//! collection domain each one reads in, chosen from its receiver's inferred
//! sort.
//!
//! An index or a collection method names an operation but not its
//! collection: `m[k]` is `map::get(m, k)` on a `Map` and `list::get(m, k)` on
//! a `List`. Each collection operation reads a receiver of its own sort only,
//! so a receiver whose sort is `Map`, `List` or `Set`, or a subsort of one,
//! pins the method to that domain: no other reading is well sorted. A method
//! whose receiver pins a domain denotes that domain's operation, applied to
//! the arguments the parser already wrote in the operation's order, and from
//! then on it is inferred, checked, and lowered exactly as that call; every
//! later phase sees an ordinary collection application. A receiver that pins
//! no domain is an error that names the narrowing and the calls, and nothing
//! is guessed. The domain is decided in the passes that decide operators
//! ([`StructuredTermBuilder::infer_sentence`]), for the same reason: a
//! receiver's sort may only be known once a later part of the sentence is
//! inferred.

use krs_ir::{
    BuiltinSort, CollectionDomain, CollectionMethod, CollectionReading, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorPayload, DescriptorTerm, ProvenanceKey,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm};

use super::catalog::semantic_is_subsort;
use super::error::{DescriptorLoweringError, OperatorProblem};
use super::infer::StructuredTermBuilder;

/// What a method's receiver chooses.
enum DomainChoice {
    /// One domain.
    Chosen(CollectionDomain),
    /// None yet: the receiver's sort is not known, or is `KItem` or `K`,
    /// which every collection lies below.
    Unknown(Option<SemanticSortRef>),
    /// None ever: the receiver has a sort no collection lies below.
    Foreign(SemanticSortRef),
}

impl StructuredTermBuilder<'_> {
    /// Infers an index or a collection method: as the call of its domain's
    /// operation once its receiver chooses the domain, and otherwise its
    /// arguments alone, leaving the method for a later pass.
    pub(super) fn infer_collection_method(
        &mut self,
        reference: &DescriptorApplicationReference,
        method: CollectionMethod,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let operands = self.method_operands(method, arguments)?;
        let domain = if let Some(domain) = self.operators.methods.get(&reference.key) {
            *domain
        } else {
            let receiver = operands[method.receiver()];
            match self.method_domain(receiver) {
                DomainChoice::Chosen(domain) => {
                    self.operators.methods.insert(reference.key.clone(), domain);
                    domain
                }
                DomainChoice::Unknown(sort) => {
                    if self.operators.pending.is_none() {
                        self.operators.pending = Some(self.unknown_receiver(
                            &reference.key,
                            method,
                            receiver,
                            sort.as_ref(),
                        ));
                    }
                    for operand in operands {
                        self.infer(operand, None, subject)?;
                    }
                    return Ok(());
                }
                DomainChoice::Foreign(sort) => {
                    return Err(self.foreign_receiver(&reference.key, method, &sort));
                }
            }
        };
        let reading = self.method_reading(&reference.key, method, domain)?;
        self.infer_application(
            &reading_reference(reference, reading),
            arguments,
            &[],
            expected_sort,
            super::infer::Partial::new(subject, None, false),
        )
    }

    /// Lowers an index or a collection method as the call of the operation
    /// of the domain inference chose for it.
    pub(super) fn lower_collection_method(
        &mut self,
        reference: &DescriptorApplicationReference,
        method: CollectionMethod,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
        head: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let domain = *self.operators.methods.get(&reference.key).ok_or_else(|| {
            self.invalid_term(format!(
                "`{}` was lowered before inference chose its collection",
                method.written()
            ))
        })?;
        let reading = self.method_reading(&reference.key, method, domain)?;
        self.lower_application(
            &reading_reference(reference, reading),
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
        )
    }

    /// The sort of the result of a method whose domain is decided, when its
    /// operation's result is a builtin sort.
    pub(super) fn method_result_sort(
        &self,
        reference: &DescriptorApplicationReference,
        method: CollectionMethod,
    ) -> Option<SemanticSortRef> {
        let domain = self.operators.methods.get(&reference.key)?;
        match method.reading(*domain)?.spec().result_sort {
            krs_ir::CollectionResultSort::Builtin(sort) => Some(SemanticSortRef::Builtin(sort)),
            krs_ir::CollectionResultSort::Projected => self
                .collections
                .projection(&reference.key)
                .map(|site| site.sort.clone())
                .or_else(|| self.collections.untyped_element().cloned()),
        }
    }

    /// The arguments of a method's application, which has exactly the
    /// arity of the call it denotes, positionally.
    fn method_operands<'t>(
        &self,
        method: CollectionMethod,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Vec<&'t DescriptorTerm>, DescriptorLoweringError> {
        let operands = arguments
            .iter()
            .filter_map(|argument| match argument {
                krs_ir::TermArgumentRef::Positional { value } => Some(value),
                krs_ir::TermArgumentRef::Named { .. } => None,
            })
            .collect::<Vec<_>>();
        if arguments.is_named() || operands.len() != method.arity() {
            return Err(self.invalid_term(format!(
                "`{}` takes {} positional arguments, its receiver included",
                method.written(),
                method.arity()
            )));
        }
        Ok(operands)
    }

    /// The domain a receiver chooses from the sorts known so far.
    fn method_domain(&self, receiver: &DescriptorTerm) -> DomainChoice {
        let Some(sort) = self.operand_sort(receiver) else {
            return DomainChoice::Unknown(None);
        };
        let pinned = CollectionDomain::ALL
            .into_iter()
            .filter(|domain| {
                semantic_is_subsort(
                    &sort,
                    &SemanticSortRef::Builtin(domain.sort()),
                    self.sort_parents,
                )
            })
            .collect::<Vec<_>>();
        match pinned.as_slice() {
            [domain] => DomainChoice::Chosen(*domain),
            _ if is_unsorted(&sort) => DomainChoice::Unknown(Some(sort)),
            _ => DomainChoice::Foreign(sort),
        }
    }

    /// The reading of `method` in `domain`, or the error naming the
    /// collections that have it.
    fn method_reading(
        &self,
        key: &ProvenanceKey,
        method: CollectionMethod,
        domain: CollectionDomain,
    ) -> Result<CollectionReading, DescriptorLoweringError> {
        method.reading(domain).ok_or_else(|| {
            let readers = method
                .domains()
                .into_iter()
                .map(|domain| format!("a `{}`", domain.name()))
                .collect::<Vec<_>>();
            let what = match method.spelling() {
                krs_ir::CollectionMethodSpelling::Index => "an index".to_owned(),
                krs_ir::CollectionMethodSpelling::Method => {
                    format!("the method `{}`", method.written())
                }
            };
            self.method_error(
                key,
                OperatorProblem::Undefined,
                format!(
                    "{what} reads {}, and the receiver is a `{}`, whose methods are {}",
                    prose_list(&readers, "or"),
                    domain.name(),
                    method_names(domain),
                ),
            )
        })
    }

    /// The error for a receiver whose sort chooses no collection yet: a
    /// binder that no occurrence sorts, or sorts no more precisely than
    /// `KItem`, is named with the narrowing that says which collection is
    /// meant.
    fn unknown_receiver(
        &self,
        key: &ProvenanceKey,
        method: CollectionMethod,
        receiver: &DescriptorTerm,
        sort: Option<&SemanticSortRef>,
    ) -> DescriptorLoweringError {
        let calls = method_calls(method);
        let reason = match receiver {
            DescriptorTerm::Variable { name, .. }
                if !self.is_let_local_name(name) && !self.is_inferring_local(name) =>
            {
                let sorted = if sort.is_some() {
                    " more precisely than `KItem`"
                } else {
                    ""
                };
                let collection = method
                    .domains()
                    .first()
                    .map_or("Map", |domain| domain.name());
                let narrowing =
                    if matches!(self.descriptor.payload(), DescriptorPayload::HeadRule(_)) {
                        format!("`where {name}: {collection}`")
                    } else {
                        format!("the typed binder `{name}: Term<{collection}>`")
                    };
                format!(
                    "`{}` has the receiver `{name}`, which no occurrence sorts{sorted}, so it chooses no collection; narrow it ({narrowing}) or write the call you mean: {calls}",
                    method.written()
                )
            }
            _ => format!(
                "`{}` has a receiver of {}, which chooses no collection; write the call you mean: {calls}",
                method.written(),
                sort.map_or_else(
                    || "an unknown sort".to_owned(),
                    |sort| format!("sort `{}`", super::overload::sort_name(sort))
                ),
            ),
        };
        self.method_error(key, OperatorProblem::Ambiguous, reason)
    }

    /// The error for a receiver of a sort no collection lies below: the
    /// notation does not apply to it, which is no ambiguity.
    fn foreign_receiver(
        &self,
        key: &ProvenanceKey,
        method: CollectionMethod,
        sort: &SemanticSortRef,
    ) -> DescriptorLoweringError {
        let scalar = scalar_forms(method, |domain| {
            semantic_is_subsort(sort, &SemanticSortRef::Builtin(domain), self.sort_parents)
        });
        // Nothing is ambiguous: the notation reads no receiver of this sort.
        self.method_error(
            key,
            OperatorProblem::Undefined,
            format!(
                "`{}` has a receiver of sort `{}`, which is no collection: an index and the collection methods read a `Map`, a `List` or a `Set`{scalar}",
                method.written(),
                super::overload::sort_name(sort),
            ),
        )
    }

    fn method_error(
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

/// The reference of the call a method denotes: the operation, at the
/// method's own key.
fn reading_reference(
    reference: &DescriptorApplicationReference,
    reading: CollectionReading,
) -> DescriptorApplicationReference {
    DescriptorApplicationReference {
        key: reference.key.clone(),
        application: match reading {
            CollectionReading::Map(operation) => DescriptorApplicationRef::Map(operation),
            CollectionReading::List(operation) => DescriptorApplicationRef::List(operation),
            CollectionReading::Set(operation) => DescriptorApplicationRef::Set(operation),
        },
    }
}

/// Whether `sort` lies above every collection, so that it pins none: the
/// framework's `KItem`, the sort of an element of a bare collection, and
/// `K`.
fn is_unsorted(sort: &SemanticSortRef) -> bool {
    match sort {
        SemanticSortRef::Builtin(sort) => *sort == BuiltinSort::KSequence,
        SemanticSortRef::Declared(id) => {
            id.item_name() == "KItem" && id.package().k_namespace() == "KRS-FRAMEWORK"
        }
        _ => false,
    }
}

/// The calls a method denotes, one per domain: `` `map::size(..)`,
/// `list::size(..)`, or `set::size(..)` ``.
fn method_calls(method: CollectionMethod) -> String {
    let calls = method
        .domains()
        .into_iter()
        .filter_map(|domain| method.reading(domain))
        .map(|reading| {
            let marker = reading.facade_marker();
            format!("`{}::{}(..)`", marker.module, marker.name)
        })
        .collect::<Vec<_>>();
    prose_list(&calls, "or")
}

/// The index and the methods a collection of `domain` has.
fn method_names(domain: CollectionDomain) -> String {
    let names = CollectionMethod::ALL
        .into_iter()
        .filter(|method| method.reading(domain).is_some())
        .map(|method| format!("`{}`", method.written()))
        .collect::<Vec<_>>();
    prose_list(&names, "and")
}

/// For a method whose name the module of a scalar domain the receiver's sort
/// lies in also defines (`b.update(i, v)` on `Bytes`), the turbofish form
/// that names that operation instead.
fn scalar_forms(method: CollectionMethod, receiver_in: impl Fn(BuiltinSort) -> bool) -> String {
    let name = method.rust_name();
    let forms = [
        ("Int", "int", BuiltinSort::Int),
        ("Bool", "bool", BuiltinSort::Bool),
        ("String", "string", BuiltinSort::String),
        ("Float", "float", BuiltinSort::Float),
        ("Bytes", "bytes", BuiltinSort::Bytes),
    ]
    .into_iter()
    .filter(|(_, _, sort)| receiver_in(*sort))
    .filter(|(_, module, _)| {
        krs_ir::BuiltinOperation::ALL.iter().any(|operation| {
            operation.spec().rust_module == *module && operation.spec().rust_name == name
        })
    })
    .map(|(domain, _, _)| format!("`{name}::<{domain}>`"))
    .collect::<Vec<_>>();
    if forms.is_empty() {
        String::new()
    } else {
        format!(
            "; a builtin operation of a scalar domain names its domain: {}",
            prose_list(&forms, "or")
        )
    }
}

fn prose_list(items: &[String], conjunction: &str) -> String {
    match items {
        [] => String::new(),
        [only] => only.clone(),
        [first, second] => format!("{first} {conjunction} {second}"),
        [rest @ .., last] => format!("{}, {conjunction} {last}", rest.join(", ")),
    }
}
