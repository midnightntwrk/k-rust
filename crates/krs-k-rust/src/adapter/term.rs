use k_rust::kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm};
use krs_ir::{
    ApplicationRef, ListOperation, MapOperation, NodeOrigin, SemanticId, SemanticIdKind,
    SetOperation,
};
use krs_ir_levels::{DefinitionTerm, DefinitionTermKind, RuleSentence, k_surface::variable_name};

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
            DefinitionTermKind::Map {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let native = Self::map_term(*operation, arguments, term.origin())?;
                if *operation == MapOperation::Get {
                    // semantic-cast-projection-widening: represent a typed
                    // heterogeneous lookup with the project:<Sort> term used
                    // by k-rust's semantic downcast. Keep the Definition IR
                    // result sort explicit.
                    Ok(NativeTerm::apply(
                        format!("project:{}", self.sort(term.sort(), term.origin())?.name),
                        vec![native],
                    ))
                } else {
                    Ok(native)
                }
            }
            DefinitionTermKind::List {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let native = Self::list_term(*operation, arguments, term.origin())?;
                if *operation == ListOperation::Get {
                    Ok(NativeTerm::apply(
                        format!("project:{}", self.sort(term.sort(), term.origin())?.name),
                        vec![native],
                    ))
                } else {
                    Ok(native)
                }
            }
            DefinitionTermKind::Set {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Self::set_term(*operation, arguments, term.origin())
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

    fn map_term(
        operation: MapOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        match operation {
            MapOperation::Empty if arguments.is_empty() => Ok(NativeTerm::apply(".Map", vec![])),
            MapOperation::Item if !arguments.is_empty() && arguments.len().is_multiple_of(2) => {
                let mut arguments = arguments.into_iter();
                let mut items = std::iter::from_fn(|| {
                    let key = arguments.next()?;
                    let value = arguments.next().expect("validated even map item arity");
                    Some(NativeTerm::apply("_|->_", vec![key, value]))
                });
                let first = items.next().expect("nonempty even argument list");
                Ok(items.fold(first, |left, right| {
                    NativeTerm::apply("_Map_", vec![left, right])
                }))
            }
            MapOperation::Update if arguments.len() == 3 => {
                Ok(NativeTerm::apply("Map:update", arguments))
            }
            MapOperation::Get if arguments.len() == 2 => {
                Ok(NativeTerm::apply("Map:lookup", arguments))
            }
            MapOperation::InKeys if arguments.len() == 2 => Ok(NativeTerm::apply(
                "_in_keys(_)_MAP_Bool_KItem_Map",
                arguments,
            )),
            _ => Err(AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "Map operation arity",
                target: format!("{operation}/{}", arguments.len()),
            }),
        }
    }

    fn list_term(
        operation: ListOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let label = match (operation, arguments.len()) {
            (ListOperation::Empty, 0) => ".List",
            (ListOperation::Item, 1) => "ListItem",
            (ListOperation::Concat, 2) => "_List_",
            (ListOperation::Get, 2) => "List:get",
            (ListOperation::Update, 3) => "List:set",
            (ListOperation::Size, 1) => "sizeList",
            (ListOperation::Make, 2) => "makeList(_,_)_LIST_List_Int_KItem",
            (ListOperation::Range, 3) => "List:range",
            (ListOperation::UpdateAll, 3) => "updateList(_,_,_)_LIST_List_List_Int_List",
            _ => {
                return Err(AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "List operation arity",
                    target: format!("{operation}/{}", arguments.len()),
                });
            }
        };
        Ok(NativeTerm::apply(label, arguments))
    }

    fn set_term(
        operation: SetOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let label = match (operation, arguments.len()) {
            (SetOperation::Empty, 0) => ".Set",
            (SetOperation::Item, 1) => "SetItem",
            (SetOperation::Concat, 2) => "_Set_",
            (SetOperation::Union, 2) => "_|Set__SET_Set_Set_Set",
            (SetOperation::Contains, 2) => "Set:in",
            _ => {
                return Err(AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "Set operation arity",
                    target: format!("{operation}/{}", arguments.len()),
                });
            }
        };
        Ok(NativeTerm::apply(label, arguments))
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
