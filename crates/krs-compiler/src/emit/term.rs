use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinOperationNotation, CollectionNotation,
    CollectionOperationSpec, GrammarProductionItemKind, MapOperation, ProductionAttribute,
    ProductionGroupId, SemanticId, SemanticIdKind, SourceMapKey,
};
use krs_ir_levels::{
    DefinitionClaimBinder, DefinitionSortRef, DefinitionTerm, DefinitionTermKind, MapOperands,
    ProductionSentence, RuleSentence, k_surface::variable_name,
};

use super::{EmitContext, EmitError, quoted};

pub(super) fn render_context_term(
    term: &DefinitionTerm,
    here: &SemanticId,
    here_origin: &krs_ir::NodeOrigin,
    context: &EmitContext<'_>,
) -> Result<Rendered, EmitError> {
    if matches!(term.kind(), DefinitionTermKind::Variable { variable } if variable == here) {
        let mut output = Rendered::default();
        output.push("HERE");
        output.ranges.push((term.origin().key().clone(), 0, 4));
        output.ranges.push((here_origin.key().clone(), 0, 4));
        return Ok(output);
    }
    if let DefinitionTermKind::KSequence { items, .. } = term.kind() {
        let mut output = Rendered::default();
        for (index, item) in items.iter().enumerate() {
            if index != 0 {
                output.push(" ~> ");
            }
            output.append(render_context_term(item, here, here_origin, context)?);
        }
        if items.is_empty() {
            output.push(".K");
        }
        return Ok(output.finish(term.origin().key(), 0));
    }
    render_term(term, context, false)
}

#[derive(Default)]
pub(super) struct Rendered {
    pub(super) text: String,
    pub(super) ranges: Vec<(SourceMapKey, usize, usize)>,
}

impl Rendered {
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
    }

    fn append(&mut self, child: Self) {
        let base = self.text.len();
        self.text.push_str(&child.text);
        self.ranges.extend(
            child
                .ranges
                .into_iter()
                .map(|(key, start, end)| (key, base + start, base + end)),
        );
    }

    pub(super) fn finish(mut self, key: &SourceMapKey, start: usize) -> Self {
        self.ranges.push((key.clone(), start, self.text.len()));
        self
    }
}

pub(super) fn render_term(
    term: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
) -> Result<Rendered, EmitError> {
    render_term_with_binders(term, context, root_rewrite, &[])
}

pub(super) fn render_rule_term(
    term: &DefinitionTerm,
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    root_rewrite: bool,
) -> Result<Rendered, EmitError> {
    let existentials = sentence
        .claim()
        .map_or(&[][..], |claim| claim.existentials());
    render_term_with_binders(term, context, root_rewrite, existentials)
}

pub(super) fn render_rewrite(
    from: &DefinitionTerm,
    to: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    existentials: &[DefinitionClaimBinder],
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    if !root_rewrite {
        output.push("(");
    }
    output.append(render_term_with_binders(
        from,
        context,
        false,
        existentials,
    )?);
    output.push(" => ");
    output.append(render_term_with_binders(to, context, false, existentials)?);
    if !root_rewrite {
        output.push(")");
    }
    Ok(output)
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps exhaustive term rendering and binder handling together."
)]
fn render_term_with_binders(
    term: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    existentials: &[DefinitionClaimBinder],
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let start = 0;
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            if variable.kind() == SemanticIdKind::Wildcard {
                output.push("_");
            } else if let SemanticIdKind::Anonymous { name } = variable.kind() {
                output.push(name);
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            } else if existentials.iter().any(|binder| binder.id() == variable) {
                output.push("?");
                output.push(&variable.as_str().to_ascii_uppercase());
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            } else {
                output.push(&variable_name(variable));
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            }
        }
        DefinitionTermKind::Application {
            application,
            arguments,
        } => match application {
            ApplicationRef::Builtin(operation) => {
                render_builtin_application(
                    *operation,
                    arguments,
                    context,
                    existentials,
                    &mut output,
                )?;
            }
            ApplicationRef::Declared(symbol) => {
                let production = context.production(symbol)?;
                let mut arguments = arguments.iter();
                for (index, item) in production.items().iter().enumerate() {
                    if index != 0 {
                        output.push(" ");
                    }
                    match item.kind() {
                        GrammarProductionItemKind::Terminal { text } => output.push(text),
                        GrammarProductionItemKind::NonTerminal { .. } => {
                            let Some(argument) = arguments.next() else {
                                return Err(EmitError::InvalidReference(format!(
                                    "production {:?} has fewer application arguments than nonterminals",
                                    symbol.as_str()
                                )));
                            };
                            let parenthesize =
                                parenthesize_declared_child(production, argument, context)?;
                            if parenthesize {
                                output.push("(");
                            }
                            output.append(render_term_with_binders(
                                argument,
                                context,
                                false,
                                existentials,
                            )?);
                            if parenthesize {
                                output.push(")");
                            }
                        }
                        GrammarProductionItemKind::RegexTerminal { .. } => {
                            return Err(EmitError::UnsupportedShape {
                                node: "regex application",
                                detail: "regex productions are not term constructors".to_owned(),
                            });
                        }
                    }
                }
                if arguments.next().is_some() {
                    return Err(EmitError::InvalidReference(format!(
                        "production {:?} has more application arguments than nonterminals",
                        symbol.as_str()
                    )));
                }
            }
        },
        DefinitionTermKind::Token { value } => {
            if matches!(term.sort(), DefinitionSortRef::Builtin(_)) {
                output.push(value);
            } else {
                output.push("#token(");
                output.push(&quoted(value));
                output.push(",");
                output.push(&quoted(context.sort_name_ref(term.sort())?));
                output.push(")");
            }
        }
        DefinitionTermKind::KSequence { items, .. } => {
            if items.is_empty() {
                output.push(".K");
            } else {
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        output.push(" ~> ");
                    }
                    output.append(render_term_with_binders(
                        item,
                        context,
                        false,
                        existentials,
                    )?);
                }
            }
        }
        DefinitionTermKind::Map(operands) => {
            render_map(term.sort(), operands, context, existentials, &mut output)?;
        }
        DefinitionTermKind::List(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            existentials,
            &mut output,
        )?,
        DefinitionTermKind::Set(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            existentials,
            &mut output,
        )?,
        DefinitionTermKind::Cell { cell, children } => {
            let name = context.cell_name(cell)?;
            output.push("<");
            output.push(name);
            output.push(">");
            if !children.is_empty() {
                output.push(" ");
            }
            for (index, child) in children.iter().enumerate() {
                if index != 0 {
                    output.push(" ");
                }
                output.append(render_term_with_binders(
                    child,
                    context,
                    false,
                    existentials,
                )?);
            }
            if !children.is_empty() {
                output.push(" ");
            }
            output.push("</");
            output.push(name);
            output.push(">");
        }
        DefinitionTermKind::Rewrite { from, to } => {
            output.append(render_rewrite(
                from,
                to,
                context,
                root_rewrite,
                existentials,
            )?);
        }
    }
    Ok(output.finish(term.origin().key(), start))
}

fn parenthesize_declared_child(
    parent: &ProductionSentence,
    child: &DefinitionTerm,
    context: &EmitContext<'_>,
) -> Result<bool, EmitError> {
    let Some(parent_group) = production_group(parent) else {
        return Ok(false);
    };
    let prefix_unary = matches!(
        parent.items(),
        [terminal, nonterminal]
            if matches!(terminal.kind(), GrammarProductionItemKind::Terminal { .. })
                && matches!(
                    nonterminal.kind(),
                    GrammarProductionItemKind::NonTerminal { .. }
                )
    );
    if !context.is_non_associative(parent_group) && !prefix_unary {
        return Ok(false);
    }
    let DefinitionTermKind::Application {
        application: ApplicationRef::Declared(child_symbol),
        ..
    } = child.kind()
    else {
        return Ok(false);
    };
    Ok(production_group(context.production(child_symbol)?).is_some())
}

fn production_group(production: &ProductionSentence) -> Option<&ProductionGroupId> {
    production
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::Group { group, .. } => Some(group),
            _ => None,
        })
}

fn render_builtin_application(
    operation: BuiltinOperation,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let spec = operation.spec();
    if arguments.len() != spec.argument_sorts.len() {
        return Err(EmitError::InvalidReference(format!(
            "builtin operation {operation} has invalid arity {}",
            arguments.len()
        )));
    }
    match spec.k_notation {
        BuiltinOperationNotation::Mixfix { pieces } => {
            output.push(pieces[0]);
            for (argument, piece) in arguments.iter().zip(&pieces[1..]) {
                output.append(render_builtin_argument(argument, context, existentials)?);
                output.push(piece);
            }
        }
        BuiltinOperationNotation::Call { name } => {
            output.push(name);
            output.push("(");
            for (index, argument) in arguments.iter().enumerate() {
                if index > 0 {
                    output.push(", ");
                }
                output.append(render_term_with_binders(
                    argument,
                    context,
                    false,
                    existentials,
                )?);
            }
            output.push(")");
        }
    }
    Ok(())
}

fn render_builtin_argument(
    argument: &DefinitionTerm,
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
) -> Result<Rendered, EmitError> {
    let parenthesize = matches!(
        argument.kind(),
        DefinitionTermKind::Application {
            application: ApplicationRef::Builtin(_),
            ..
        }
    );
    let mut output = Rendered::default();
    if parenthesize {
        output.push("(");
    }
    output.append(render_term_with_binders(
        argument,
        context,
        false,
        existentials,
    )?);
    if parenthesize {
        output.push(")");
    }
    Ok(output)
}

fn render_map(
    result_sort: &DefinitionSortRef,
    operands: &MapOperands<DefinitionTerm>,
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let MapOperands::Items(entries) = operands else {
        return render_collection(
            result_sort,
            operands.operation().spec(),
            operands.operands(),
            context,
            existentials,
            output,
        );
    };
    for (index, entry) in entries.iter().enumerate() {
        if index != 0 {
            output.push(MapOperation::CONCATENATION.separator);
        }
        render_collection(
            result_sort,
            MapOperation::Item.spec(),
            [&entry.key, &entry.value].into_iter(),
            context,
            existentials,
            output,
        )?;
    }
    Ok(())
}

fn render_collection<'a>(
    result_sort: &DefinitionSortRef,
    spec: &CollectionOperationSpec,
    operands: impl Iterator<Item = &'a DefinitionTerm>,
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    if spec.is_projected() {
        output.push("{");
    }
    match spec.k_notation {
        CollectionNotation::Mixfix { pieces } => {
            output.push(pieces[0]);
            for (operand, piece) in operands.zip(&pieces[1..]) {
                output.append(render_term_with_binders(
                    operand,
                    context,
                    false,
                    existentials,
                )?);
                output.push(piece);
            }
        }
        CollectionNotation::Call { name } => {
            output.push(name);
            output.push("(");
            for (index, operand) in operands.enumerate() {
                if index > 0 {
                    output.push(", ");
                }
                output.append(render_term_with_binders(
                    operand,
                    context,
                    false,
                    existentials,
                )?);
            }
            output.push(")");
        }
    }
    if spec.is_projected() {
        output.push("}:>");
        output.push(context.sort_name_ref(result_sort)?);
    }
    Ok(())
}
