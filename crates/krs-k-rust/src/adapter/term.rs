use k_rust::kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm};
use krs_ir::{
    ApplicationRef, CollectionOperationSpec, GeneratedOperation, MapOperation, NodeOrigin,
    NonEmpty, SemanticId,
};
use krs_ir_levels::{DefinitionSortRef, DefinitionTerm, DefinitionTermKind, MapEntry, MapOperands};

use super::{Adapter, AdapterError, SentenceNodeRole};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum TermContext {
    Normal,
    ConfigurationInitializer,
    ContextAlias,
}

impl Adapter<'_> {
    #[expect(
        clippy::too_many_lines,
        reason = "Keeps exhaustive term adaptation in one match."
    )]
    pub(super) fn term(
        &mut self,
        term: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            term.origin(),
            module,
            sentence_index,
            SentenceNodeRole::Term(path.clone()),
        );
        match term.kind() {
            DefinitionTermKind::Variable { variable } => {
                if context == TermContext::ContextAlias
                    && self.context_here.as_ref() == Some(variable)
                {
                    return Ok(NativeTerm::variable("HERE"));
                }
                if context == TermContext::ConfigurationInitializer
                    && let Some(name) = self.initializer_variables.get(variable).cloned()
                {
                    let sort = self.sort(term.sort(), term.origin())?;
                    return Ok(NativeTerm::apply(
                        format!("#SemanticCastTo{}", sort.name),
                        vec![NativeTerm::Token {
                            token: format!("${name}"),
                            sort: NativeSort::new("KConfigVar"),
                        }],
                    ));
                }
                let sort = self.sort(term.sort(), term.origin())?;
                self.native_variable(variable, sort, term.origin())
            }
            DefinitionTermKind::Application {
                application: ApplicationRef::Generated(operation),
                arguments,
            } => self.generated_application(
                operation,
                arguments,
                term.origin(),
                module,
                sentence_index,
                &path,
                context,
            ),
            DefinitionTermKind::Application {
                application,
                arguments,
            } => Ok(NativeTerm::Apply {
                label: NativeLabel::new(match application {
                    ApplicationRef::Declared(symbol) => {
                        self.symbol_name(symbol, term.origin())?.to_owned()
                    }
                    ApplicationRef::Builtin(operation) => operation.spec().k_label.to_owned(),
                    ApplicationRef::Generated(_) => {
                        unreachable!("generated applications are adapted above")
                    }
                }),
                arguments: arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            DefinitionTermKind::Token { value } => Ok(NativeTerm::Token {
                token: value.clone(),
                sort: self.sort(term.sort(), term.origin())?,
            }),
            DefinitionTermKind::KSequence { item_sort, items } => {
                self.sort(item_sort, term.origin())?;
                Ok(NativeTerm::sequence(
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, item)| {
                            let mut child_path = path.clone();
                            child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                            self.term(item, module, sentence_index, child_path, context)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            DefinitionTermKind::Map(operands) => {
                let mut next_index = 0_usize;
                let native = operands.try_map_ref(|operand| {
                    let mut child_path = path.clone();
                    child_path.push(u32::try_from(next_index).unwrap_or(u32::MAX));
                    next_index += 1;
                    self.term(operand, module, sentence_index, child_path, context)
                })?;
                let native = match native {
                    MapOperands::Items(entries) => native_map_items(entries),
                    native => {
                        NativeTerm::apply(native.operation().spec().k_label, native.into_operands())
                    }
                };
                self.project_collection(native, operands.operation().spec(), term)
            }
            DefinitionTermKind::List(operands) => {
                let arguments = operands
                    .operands()
                    .enumerate()
                    .map(|(index, operand)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(operand, module, sentence_index, child_path, context)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let spec = operands.operation().spec();
                self.project_collection(NativeTerm::apply(spec.k_label, arguments), spec, term)
            }
            DefinitionTermKind::Set(operands) => {
                let arguments = operands
                    .operands()
                    .enumerate()
                    .map(|(index, operand)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(operand, module, sentence_index, child_path, context)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let spec = operands.operation().spec();
                self.project_collection(NativeTerm::apply(spec.k_label, arguments), spec, term)
            }
            DefinitionTermKind::Cell { cell, children } => {
                let name = self.cell_name(cell, term.origin())?.to_owned();
                let arguments = children
                    .iter()
                    .enumerate()
                    .map(|(index, child)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(child, module, sentence_index, child_path, context)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(NativeTerm::apply(format!("<{name}>"), arguments))
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.rewrite(from, to, module, sentence_index, path, context)
            }
            // `alias @ pattern` is the AST k-rust's parser produces for
            // `PATTERN #as Alias:Sort` (KF-029).
            DefinitionTermKind::As { alias, pattern } => {
                let mut child_path = path;
                child_path.push(0);
                let pattern = self.term(pattern, module, sentence_index, child_path, context)?;
                let sort = self.sort(term.sort(), term.origin())?;
                Ok(NativeTerm::As {
                    pattern: Box::new(pattern),
                    alias: Box::new(self.native_variable(alias, sort, term.origin())?),
                })
            }
            // `A | B | C` is the AST k-rust's parser produces for
            // `A #Or B #Or C`: binary `#Or` nested to the left, with no label
            // sort parameter (X9.1). k-rust's `guard_or_patterns` pass then
            // aliases each disjunction, as Java K does (KF-030).
            DefinitionTermKind::Or { alternatives } => {
                let mut native = alternatives.iter().enumerate().map(|(index, alternative)| {
                    let mut child_path = path.clone();
                    child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                    self.term(alternative, module, sentence_index, child_path, context)
                });
                let first = native
                    .next()
                    .expect("an or-pattern has at least two alternatives")?;
                native.try_fold(first, |left, right| {
                    Ok(NativeTerm::apply("#Or", vec![left, right?]))
                })
            }
            // K's `( PATTERN :=K SUBJECT )`, with no label sort parameter;
            // k-rust's `resolve_fun` generates its lambda (KF-031).
            DefinitionTermKind::Matches {
                subject, pattern, ..
            } => {
                let mut pattern_path = path.clone();
                pattern_path.push(0);
                let mut subject_path = path;
                subject_path.push(1);
                let pattern = self.term(pattern, module, sentence_index, pattern_path, context)?;
                let subject = self.term(subject, module, sentence_index, subject_path, context)?;
                Ok(NativeTerm::apply("_:=K_", vec![pattern, subject]))
            }
            // K's `( #let PATTERN = VALUE #in BODY )` is `#let(PATTERN,
            // VALUE, BODY)` with no label sort parameter; k-rust's
            // `resolve_fun` lowers it to `#fun(PATTERN => BODY)(VALUE)`
            // (KF-032).
            DefinitionTermKind::Let {
                pattern,
                value,
                body,
                ..
            } => {
                let mut pattern_path = path.clone();
                pattern_path.push(0);
                let mut value_path = path.clone();
                value_path.push(1);
                let mut body_path = path;
                body_path.push(2);
                let pattern = self.term(pattern, module, sentence_index, pattern_path, context)?;
                let value = self.term(value, module, sentence_index, value_path, context)?;
                let body = self.term(body, module, sentence_index, body_path, context)?;
                Ok(NativeTerm::apply("#let", vec![pattern, value, body]))
            }
        }
    }

    pub(super) fn rewrite(
        &mut self,
        from: &DefinitionTerm,
        to: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        let mut left_path = path.clone();
        left_path.push(0);
        let mut right_path = path;
        right_path.push(1);
        Ok(NativeTerm::Rewrite {
            left: Box::new(self.term(from, module, sentence_index, left_path, context)?),
            right: Box::new(self.term(to, module, sentence_index, right_path, context)?),
        })
    }

    /// Spells a variable with the name the shared naming function gave it in this sentence.
    pub(super) fn native_variable(
        &self,
        variable: &SemanticId,
        sort: NativeSort,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let name =
            self.variable_names
                .name(variable)
                .ok_or_else(|| AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "sentence variable",
                    target: variable.as_str().to_owned(),
                })?;
        Ok(NativeTerm::Variable {
            name: name.to_owned(),
            sort: Some(sort),
        })
    }

    /// Adapts K's generated sort predicate or projection with k-rust's labels
    /// `is<Sort>` and `project:<Sort>`. Both take an argument of sort `K`, so a
    /// projected collection lookup keeps its `KItem` result and the term has
    /// exactly one projection.
    #[expect(
        clippy::too_many_arguments,
        reason = "Mirrors the term adapter's positional context."
    )]
    fn generated_application(
        &mut self,
        operation: &GeneratedOperation<DefinitionSortRef>,
        arguments: &[DefinitionTerm],
        origin: &NodeOrigin,
        module: &str,
        sentence_index: usize,
        path: &[u32],
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        let [argument] = arguments else {
            return Err(AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "generated sort operation argument",
                target: format!("{} arguments", arguments.len()),
            });
        };
        let mut child_path = path.to_vec();
        child_path.push(0);
        let operand = self.term(argument, module, sentence_index, child_path, context)?;
        let operand = match (argument.kind(), operand) {
            (
                DefinitionTermKind::Map(_)
                | DefinitionTermKind::List(_)
                | DefinitionTermKind::Set(_),
                NativeTerm::Apply {
                    label,
                    mut arguments,
                },
            ) if label.name.starts_with("project:") && arguments.len() == 1 => arguments.remove(0),
            (_, operand) => operand,
        };
        let sort = self.sort(operation.sort(), origin)?.name;
        let label = match operation {
            GeneratedOperation::SortPredicate(_) => format!("is{sort}"),
            GeneratedOperation::SortProjection(_) => format!("project:{sort}"),
        };
        Ok(NativeTerm::apply(label, vec![operand]))
    }

    /// Projects a `KItem` collection result to the Definition IR result sort when
    /// the operation's catalog row says both backends do.
    fn project_collection(
        &self,
        native: NativeTerm,
        spec: &CollectionOperationSpec,
        term: &DefinitionTerm,
    ) -> Result<NativeTerm, AdapterError> {
        if !spec.is_projected() {
            return Ok(native);
        }
        // semantic-cast-projection-widening: represent a typed
        // heterogeneous lookup with the project:<Sort> term used
        // by k-rust's semantic downcast. Keep the Definition IR
        // result sort explicit.
        Ok(NativeTerm::apply(
            format!("project:{}", self.sort(term.sort(), term.origin())?.name),
            vec![native],
        ))
    }
}

/// Applies the Map item label to each entry and joins the items with Map concatenation.
fn native_map_items(entries: NonEmpty<MapEntry<NativeTerm>>) -> NativeTerm {
    let item = |entry: MapEntry<NativeTerm>| {
        NativeTerm::apply(
            MapOperation::Item.spec().k_label,
            vec![entry.key, entry.value],
        )
    };
    let (first, rest) = entries.into_head_tail();
    rest.fold(item(first), |left, right| {
        NativeTerm::apply(MapOperation::CONCATENATION.k_label, vec![left, item(right)])
    })
}
