use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinOperationNotation, CollectionNotation,
    CollectionOperationSpec, GeneratedOperation, GrammarProductionItemKind, MapOperation,
    ProductionAttribute, ProductionGroupId, SemanticId, SemanticIdKind, SetOperation, SourceMapKey,
};
use krs_ir_levels::{
    DefinitionSortRef, DefinitionTerm, DefinitionTermKind, MapOperands, ProductionSentence,
    k_surface::SentenceVariables,
};

use super::{EmitContext, EmitError};

pub(super) fn render_context_term(
    term: &DefinitionTerm,
    here: &SemanticId,
    here_origin: &krs_ir::NodeOrigin,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
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
            output.append(render_context_term(
                item,
                here,
                here_origin,
                context,
                names,
            )?);
        }
        if items.is_empty() {
            output.push(".K");
        }
        return Ok(output.finish(term.origin().key(), 0));
    }
    render_term(term, context, names, false)
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
    names: &SentenceVariables,
    root_rewrite: bool,
) -> Result<Rendered, EmitError> {
    render_term_with_binders(term, context, root_rewrite, names)
}

pub(super) fn render_rewrite(
    from: &DefinitionTerm,
    to: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    names: &SentenceVariables,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    if !root_rewrite {
        output.push("(");
    }
    output.append(render_term_with_binders(from, context, false, names)?);
    output.push(" => ");
    output.append(render_term_with_binders(to, context, false, names)?);
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
    names: &SentenceVariables,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let start = 0;
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            if variable.kind() == SemanticIdKind::Wildcard {
                output.push("_");
            } else {
                output.push(names.name(variable).ok_or_else(|| {
                    EmitError::InvalidReference(format!(
                        "variable {:?} is not named in its sentence",
                        variable.as_str()
                    ))
                })?);
                output.push(":");
                output.push(&context.sort_name_ref(term.sort())?);
            }
        }
        DefinitionTermKind::Application {
            application,
            arguments,
            head_instance_fixed,
            ..
        } => match application {
            ApplicationRef::Builtin(operation) => {
                render_builtin_application(*operation, arguments, context, names, &mut output)?;
            }
            ApplicationRef::Generated(operation) => {
                render_generated_application(operation, arguments, context, names, &mut output)?;
            }
            ApplicationRef::Declared(symbol) => {
                let production = context.production(symbol)?;
                // K parses an untyped `_` at an argument of an overloaded
                // production as the most general family member, so a
                // wildcard there names its sort and K selects the member
                // the structured term denotes.
                let overloaded = production
                    .attributes()
                    .iter()
                    .any(|attribute| matches!(attribute, ProductionAttribute::Overload { .. }));
                let mut arguments = arguments.iter();
                for (index, item) in production.items().iter().enumerate() {
                    if index != 0 {
                        output.push(" ");
                    }
                    match item.kind() {
                        GrammarProductionItemKind::Terminal { text } => output.push(text),
                        GrammarProductionItemKind::NonTerminal { sort, .. } => {
                            let Some(argument) = arguments.next() else {
                                return Err(EmitError::InvalidReference(format!(
                                    "production {:?} has fewer application arguments than nonterminals",
                                    symbol.as_str()
                                )));
                            };
                            // At a parametric position of an equation or rule
                            // head, a variable prints K's strict cast to its
                            // own sort and a wildcard to the instance (X13,
                            // KF-027): a semantic cast there would let K
                            // instantiate the parameter at `K`, so the
                            // sentence would never apply.
                            if *head_instance_fixed
                                && matches!(sort, DefinitionSortRef::Parameter(_))
                                && let DefinitionTermKind::Variable { variable } = argument.kind()
                            {
                                let mut cast = Rendered::default();
                                if variable.kind() == SemanticIdKind::Wildcard {
                                    cast.push("_");
                                } else {
                                    cast.push(names.name(variable).ok_or_else(|| {
                                        EmitError::InvalidReference(format!(
                                            "variable {:?} is not named in its sentence",
                                            variable.as_str()
                                        ))
                                    })?);
                                }
                                cast.push("::");
                                cast.push(&context.sort_name_ref(argument.sort())?);
                                output.append(cast.finish(argument.origin().key(), 0));
                                continue;
                            }
                            let parenthesize =
                                parenthesize_declared_child(production, argument, context)?;
                            if parenthesize {
                                output.push("(");
                            }
                            if overloaded && is_wildcard(argument) {
                                let mut wildcard = Rendered::default();
                                wildcard.push("_:");
                                wildcard.push(&context.sort_name_ref(argument.sort())?);
                                output.append(wildcard.finish(argument.origin().key(), 0));
                            } else {
                                output.append(render_term_with_binders(
                                    argument, context, false, names,
                                )?);
                            }
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
            output.push(&context.token(value, term.sort())?);
        }
        DefinitionTermKind::KSequence { items, .. } => {
            if items.is_empty() {
                output.push(".K");
            } else {
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        output.push(" ~> ");
                    }
                    output.append(render_term_with_binders(item, context, false, names)?);
                }
            }
        }
        DefinitionTermKind::Map(operands) => {
            render_map(term.sort(), operands, context, names, &mut output)?;
        }
        DefinitionTermKind::List(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            names,
            &mut output,
        )?,
        DefinitionTermKind::Set(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            names,
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
                output.append(render_term_with_binders(child, context, false, names)?);
            }
            if !children.is_empty() {
                output.push(" ");
            }
            output.push("</");
            output.push(name);
            output.push(">");
        }
        DefinitionTermKind::Rewrite { from, to } => {
            output.append(render_rewrite(from, to, context, root_rewrite, names)?);
        }
        // `name @ pattern` is K's `( PATTERN #as Name:Sort )`, always
        // parenthesised (X13).
        DefinitionTermKind::As { alias, pattern } => {
            output.push("( ");
            output.append(render_term_with_binders(pattern, context, false, names)?);
            output.push(" #as ");
            output.push(names.name(alias).ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "alias {:?} is not named in its sentence",
                    alias.as_str()
                ))
            })?);
            output.push(":");
            output.push(&context.sort_name_ref(term.sort())?);
            output.push(" )");
        }
        // `A | B | C` is K's `( A #Or B #Or C )`, always parenthesised and
        // left to right (X13).
        DefinitionTermKind::Or { alternatives } => {
            output.push("( ");
            for (index, alternative) in alternatives.iter().enumerate() {
                if index > 0 {
                    output.push(" #Or ");
                }
                output.append(render_term_with_binders(
                    alternative,
                    context,
                    false,
                    names,
                )?);
            }
            output.push(" )");
        }
        // `k::matches!(subject, pattern)` is K's `( PATTERN :=K SUBJECT )`:
        // operands in K order, always parenthesised (X13).
        DefinitionTermKind::Matches {
            subject, pattern, ..
        } => {
            output.push("( ");
            output.append(render_term_with_binders(pattern, context, false, names)?);
            output.push(" :=K ");
            output.append(render_term_with_binders(subject, context, false, names)?);
            output.push(" )");
        }
        // A `let` statement is K's `( #let PATTERN = VALUE #in BODY )`,
        // always parenthesised (X13); a block's statements nest to the right.
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            output.push("( #let ");
            output.append(render_term_with_binders(pattern, context, false, names)?);
            output.push(" = ");
            output.append(render_term_with_binders(value, context, false, names)?);
            output.push(" #in ");
            output.append(render_term_with_binders(body, context, false, names)?);
            output.push(" )");
        }
    }
    Ok(output.finish(term.origin().key(), start))
}

fn is_wildcard(term: &DefinitionTerm) -> bool {
    matches!(
        term.kind(),
        DefinitionTermKind::Variable { variable } if variable.kind() == SemanticIdKind::Wildcard
    )
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
    names: &SentenceVariables,
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
                output.append(render_builtin_argument(argument, context, names)?);
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
                output.append(render_term_with_binders(argument, context, false, names)?);
            }
            output.push(")");
        }
    }
    Ok(())
}

/// Renders K's generated sort predicate `isS(T)` or projection `{T}:>S`.
fn render_generated_application(
    operation: &GeneratedOperation<DefinitionSortRef>,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let [argument] = arguments else {
        return Err(EmitError::InvalidReference(format!(
            "a generated sort operation has invalid arity {}",
            arguments.len()
        )));
    };
    let operand = render_generated_operand(argument, context, names)?;
    match operation {
        GeneratedOperation::SortPredicate(sort) => {
            output.push("is");
            output.push(&context.sort_name_ref(sort)?);
            output.push("(");
            output.append(operand);
            output.push(")");
        }
        GeneratedOperation::SortProjection(sort) => {
            output.push("{");
            output.append(operand);
            output.push("}:>");
            output.push(&context.sort_name_ref(sort)?);
        }
    }
    Ok(())
}

/// Renders the operand of a generated sort operation. Both take an argument
/// of sort `K`, so a projected collection lookup is rendered at its declared
/// result sort, without its own projection, and the term has exactly one
/// cast.
fn render_generated_operand(
    argument: &DefinitionTerm,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    match argument.kind() {
        DefinitionTermKind::Map(operands) if operands.operation().spec().is_projected() => {
            render_collection_projected(
                argument.sort(),
                operands.operation().spec(),
                operands.operands(),
                context,
                names,
                &mut output,
                false,
            )?;
        }
        DefinitionTermKind::List(operands) if operands.operation().spec().is_projected() => {
            render_collection_projected(
                argument.sort(),
                operands.operation().spec(),
                operands.operands(),
                context,
                names,
                &mut output,
                false,
            )?;
        }
        DefinitionTermKind::Set(operands) if operands.operation().spec().is_projected() => {
            render_collection_projected(
                argument.sort(),
                operands.operation().spec(),
                operands.operands(),
                context,
                names,
                &mut output,
                false,
            )?;
        }
        _ => return render_term_with_binders(argument, context, false, names),
    }
    Ok(output.finish(argument.origin().key(), 0))
}

fn render_builtin_argument(
    argument: &DefinitionTerm,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
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
    output.append(render_term_with_binders(argument, context, false, names)?);
    if parenthesize {
        output.push(")");
    }
    Ok(output)
}

/// The open ends of an operator-shaped collection term: whether its K spelling
/// begins (`.0`) or ends (`.1`) with one of its own operands, as `S1 -Set S2`,
/// `K in S`, and `M [ K <- undef ]` (open at the left only) do. A projected
/// lookup is braced, so it is closed.
fn collection_open_ends(term: &DefinitionTerm) -> Option<(bool, bool)> {
    let spec = match term.kind() {
        DefinitionTermKind::Map(operands) => {
            if matches!(**operands, MapOperands::Items(_)) {
                return Some((true, true));
            }
            operands.operation().spec()
        }
        DefinitionTermKind::List(operands) => operands.operation().spec(),
        DefinitionTermKind::Set(operands) => operands.operation().spec(),
        _ => return None,
    };
    if spec.is_projected() {
        return None;
    }
    match spec.k_notation {
        CollectionNotation::Mixfix { pieces } if pieces.len() > 1 => Some((
            pieces.first().is_some_and(|piece| piece.is_empty()),
            pieces.last().is_some_and(|piece| piece.is_empty()),
        )),
        CollectionNotation::Mixfix { .. } | CollectionNotation::Call { .. } => None,
    }
}

/// Whether a collection operand of a collection operator must be
/// parenthesized: an open end of the operand faces operator text that does
/// not delimit it, so K could attach the operand's own operand to the outer
/// operator instead. The leftmost and rightmost operands face the outer
/// term's context, which the enclosing term handles. Nesting an associative
/// concatenation in itself, or the left-associative `|Set` in its own left
/// operand, needs no parentheses.
fn parenthesize_collection_operand(
    outer: &CollectionOperationSpec,
    position: usize,
    operand: &DefinitionTerm,
    before: &str,
    after: &str,
) -> bool {
    let Some((open_left, open_right)) = collection_open_ends(operand) else {
        return false;
    };
    if collection_label(operand) == Some(outer.k_label) {
        let associative = matches!(outer.k_label, "_List_" | "_Set_" | "_Map_" | "_|->_");
        let left_associative = outer.k_label == SetOperation::Union.spec().k_label;
        if associative || (left_associative && position == 0) {
            return false;
        }
    }
    let left_danger = open_left && !before.is_empty() && !encloses_left(before);
    let right_danger = open_right && !after.is_empty() && !encloses_right(after);
    left_danger || right_danger
}

/// The native label of a collection term's operation (map items count as `_|->_`).
fn collection_label(term: &DefinitionTerm) -> Option<&'static str> {
    match term.kind() {
        DefinitionTermKind::Map(operands) => Some(operands.operation().spec().k_label),
        DefinitionTermKind::List(operands) => Some(operands.operation().spec().k_label),
        DefinitionTermKind::Set(operands) => Some(operands.operation().spec().k_label),
        _ => None,
    }
}

/// Whether a mixfix piece ends with a delimiter that opens an operand slot.
fn encloses_left(piece: &str) -> bool {
    let piece = piece.trim_end();
    ["(", "[", "<-", ","]
        .iter()
        .any(|delimiter| piece.ends_with(delimiter))
}

/// Whether a mixfix piece begins with a delimiter that closes an operand slot.
fn encloses_right(piece: &str) -> bool {
    let piece = piece.trim_start();
    [")", "]", "<-", ","]
        .iter()
        .any(|delimiter| piece.starts_with(delimiter))
}

fn render_map(
    result_sort: &DefinitionSortRef,
    operands: &MapOperands<DefinitionTerm>,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let MapOperands::Items(entries) = operands else {
        return render_collection(
            result_sort,
            operands.operation().spec(),
            operands.operands(),
            context,
            names,
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
            names,
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
    names: &SentenceVariables,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    render_collection_projected(result_sort, spec, operands, context, names, output, true)
}

/// Renders a collection operation; `project` is false only for the operand
/// of a generated sort operation, which supplies the one cast itself.
fn render_collection_projected<'a>(
    result_sort: &DefinitionSortRef,
    spec: &CollectionOperationSpec,
    operands: impl Iterator<Item = &'a DefinitionTerm>,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    output: &mut Rendered,
    project: bool,
) -> Result<(), EmitError> {
    let project = project && spec.is_projected();
    if project {
        output.push("{");
    }
    match spec.k_notation {
        CollectionNotation::Mixfix { pieces } => {
            output.push(pieces[0]);
            for (position, ((operand, piece), before)) in
                operands.zip(&pieces[1..]).zip(pieces).enumerate()
            {
                let parenthesize =
                    parenthesize_collection_operand(spec, position, operand, before, piece);
                if parenthesize {
                    output.push("(");
                }
                output.append(render_term_with_binders(operand, context, false, names)?);
                if parenthesize {
                    output.push(")");
                }
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
                output.append(render_term_with_binders(operand, context, false, names)?);
            }
            output.push(")");
        }
    }
    if project {
        output.push("}:>");
        output.push(&context.sort_name_ref(result_sort)?);
    }
    Ok(())
}
