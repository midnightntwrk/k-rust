use k_rust::kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm};
use krs_ir::{
    ApplicationRef, CollectionOperationSpec, MapOperation, NonEmpty, SemanticId, SemanticIdKind,
};
use krs_ir_levels::{
    DefinitionTerm, DefinitionTermKind, MapEntry, MapOperands, RuleSentence,
    k_surface::variable_name,
};

use super::{Adapter, AdapterError, SentenceNodeRole};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum TermContext {
    Normal,
    ConfigurationInitializer,
    ContextAlias,
}

impl Adapter<'_> {
    #[allow(clippy::too_many_lines)]
    pub(super) fn term(
        &mut self,
        term: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
        rule: Option<&RuleSentence>,
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
                let existential = rule.and_then(RuleSentence::claim).is_some_and(|claim| {
                    claim
                        .existentials()
                        .iter()
                        .any(|binder| binder.id() == variable)
                });
                Ok(native_variable(
                    variable,
                    Some(self.sort(term.sort(), term.origin())?),
                    existential,
                ))
            }
            DefinitionTermKind::Application {
                application,
                arguments,
            } => Ok(NativeTerm::Apply {
                label: NativeLabel::new(match application {
                    ApplicationRef::Declared(symbol) => {
                        self.symbol_name(symbol, term.origin())?.to_owned()
                    }
                    ApplicationRef::Builtin(operation) => operation.spec().k_label.to_owned(),
                }),
                arguments: arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
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
                            self.term(item, module, sentence_index, child_path, context, rule)
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
                    self.term(operand, module, sentence_index, child_path, context, rule)
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
                        self.term(operand, module, sentence_index, child_path, context, rule)
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
                        self.term(operand, module, sentence_index, child_path, context, rule)
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
                        self.term(child, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(NativeTerm::apply(format!("<{name}>"), arguments))
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.rewrite(from, to, module, sentence_index, path, context, rule)
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "A rewrite carries both sides plus the traversal state that `term` threads through."
    )]
    pub(super) fn rewrite(
        &mut self,
        from: &DefinitionTerm,
        to: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
        rule: Option<&RuleSentence>,
    ) -> Result<NativeTerm, AdapterError> {
        let mut left_path = path.clone();
        left_path.push(0);
        let mut right_path = path;
        right_path.push(1);
        Ok(NativeTerm::Rewrite {
            left: Box::new(self.term(from, module, sentence_index, left_path, context, rule)?),
            right: Box::new(self.term(to, module, sentence_index, right_path, context, rule)?),
        })
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

pub(super) fn native_variable(
    variable: &SemanticId,
    sort: Option<NativeSort>,
    existential: bool,
) -> NativeTerm {
    let name = if existential {
        format!("?{}", variable_name(variable))
    } else if let SemanticIdKind::Anonymous { name } = variable.kind() {
        name.to_owned()
    } else {
        variable_name(variable)
    };
    NativeTerm::Variable { name, sort }
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
