use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinOperationNotation, CollectionNotation,
    CollectionOperationSpec, GeneratedOperation, GrammarProductionItemKind, ItemKind, MapOperation,
    OriginFrame, ProductionAttribute, ProductionGroupId, SemanticId, SemanticIdKind, SetOperation,
    SourceMapKey, StableItemId, TransformationOriginKind,
};
use krs_ir_levels::{
    DefinitionMlPredicate, DefinitionSortRef, DefinitionTerm, DefinitionTermKind, IrMlKind,
    MapOperands, ProductionSentence, k_surface::SentenceVariables,
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
            if is_wildcard(item) {
                output.append(render_sequence_wildcard(item, context)?);
            } else {
                output.append(render_context_term(
                    item,
                    here,
                    here_origin,
                    context,
                    names,
                )?);
            }
        }
        if items.is_empty() {
            output.push(".K");
        }
        return Ok(output.finish(term.origin().key(), 0));
    }
    render_term(term, context, names, false)
}

/// `_` as an item of a K sequence, with its sort: `_:KItem`, one item, or the narrower sort it
/// stands for (`_:Stmt` at a `for Stmt` clause's root, as a bare name there is `S:Stmt`). K's
/// `~>` joins terms of sort `K`, a sequence of any length, so a bare `_` there could be read at
/// `K`, matching no item or several; the sort says it is the one item written.
fn render_sequence_wildcard(
    item: &DefinitionTerm,
    context: &EmitContext<'_>,
) -> Result<Rendered, EmitError> {
    let mut wildcard = Rendered::default();
    wildcard.push("_:");
    wildcard.push(&context.sort_name_ref(item.sort())?);
    Ok(wildcard.finish(item.origin().key(), 0))
}

#[derive(Default)]
pub(super) struct Rendered {
    pub(super) text: String,
    pub(super) ranges: Vec<(SourceMapKey, usize, usize)>,
}

impl Rendered {
    pub(super) fn push(&mut self, text: &str) {
        self.text.push_str(text);
    }

    pub(super) fn append(&mut self, child: Self) {
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
    render_term_with_binders(term, context, root_rewrite, names, None)
}

pub(super) fn render_rewrite(
    from: &DefinitionTerm,
    to: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    names: &SentenceVariables,
) -> Result<Rendered, EmitError> {
    render_rewrite_within(from, to, context, root_rewrite, names, None)
}

fn render_rewrite_within<'t>(
    from: &'t DefinitionTerm,
    to: &'t DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    if !root_rewrite {
        output.push("(");
    }
    output.append(render_term_with_binders(
        from, context, false, names, enclosing,
    )?);
    output.push(" => ");
    output.append(render_term_with_binders(
        to, context, false, names, enclosing,
    )?);
    if !root_rewrite {
        output.push(")");
    }
    Ok(output)
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps exhaustive term rendering and binder handling together."
)]
fn render_term_with_binders<'t>(
    term: &'t DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let start = 0;
    let within = within(term, enclosing);
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            // A wildcard at a `?` leaf cell's place names the cell's sort, whose values are the
            // cell and its absence: a bare `_` among a cell's children is placed by K's reading
            // of an untyped variable there, which with two of them depends on how K shares the
            // children out among them.
            if variable.kind() == SemanticIdKind::Wildcard
                && matches!(term.sort(), DefinitionSortRef::LeafCell(_))
            {
                output.push("_:");
                output.push(&context.sort_name_ref(term.sort())?);
            } else if variable.kind() == SemanticIdKind::Wildcard {
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
                render_builtin_application(
                    *operation,
                    arguments,
                    context,
                    names,
                    within,
                    &mut output,
                )?;
            }
            ApplicationRef::Generated(operation) => {
                render_generated_application(
                    operation,
                    arguments,
                    context,
                    names,
                    within,
                    &mut output,
                )?;
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
                                parenthesize_declared_child(production, index, argument, context)?;
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
                                    argument, context, false, names, within,
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
            // A literal that is the whole value of a constant the author wrote here names the
            // constant after it, `65295 /* IF */`, so a reader of the K finds the Rust. A K
            // comment is layout: the token, its range and every K reading of the sentence stay
            // as they were.
            if let Some((frames, constant)) = constant_use(term)
                && enclosing != Some(frames)
            {
                let mut output = output.finish(term.origin().key(), start);
                output.push(" /* ");
                output.push(constant.item_name());
                output.push(" */");
                return Ok(output);
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
                    if is_wildcard(item) {
                        output.append(render_sequence_wildcard(item, context)?);
                    } else {
                        output.append(render_term_with_binders(
                            item, context, false, names, within,
                        )?);
                    }
                }
            }
        }
        DefinitionTermKind::Map(operands) => {
            render_map(term.sort(), operands, context, names, within, &mut output)?;
        }
        DefinitionTermKind::List(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            names,
            within,
            &mut output,
        )?,
        DefinitionTermKind::Set(operands) => render_collection(
            term.sort(),
            operands.operation().spec(),
            operands.operands(),
            context,
            names,
            within,
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
                    child, context, false, names, within,
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
            output.append(render_rewrite_within(
                from,
                to,
                context,
                root_rewrite,
                names,
                within,
            )?);
        }
        // `name @ pattern` is K's `( PATTERN #as Name:Sort )`, always
        // parenthesised (X13).
        DefinitionTermKind::As { alias, pattern } => {
            output.push("( ");
            output.append(render_term_with_binders(
                pattern, context, false, names, within,
            )?);
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
                    within,
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
            output.append(render_term_with_binders(
                pattern, context, false, names, within,
            )?);
            output.push(" :=K ");
            output.append(render_term_with_binders(
                subject, context, false, names, within,
            )?);
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
            output.append(render_term_with_binders(
                pattern, context, false, names, within,
            )?);
            output.push(" = ");
            output.append(render_term_with_binders(
                value, context, false, names, within,
            )?);
            output.push(" #in ");
            output.append(render_term_with_binders(
                body, context, false, names, within,
            )?);
            output.push(" )");
        }
    }
    Ok(output.finish(term.origin().key(), start))
}

/// Renders a matching-logic predicate (KF-039, X13): `{ A #Equals B }` is
/// always braced, a binary connective nested in another connective or in
/// an `#Exists` body is parenthesized, `#Not` and `#Ceil` parenthesize
/// their operand, and no connective carries a sort parameter.
pub(super) fn render_predicate(
    predicate: &DefinitionMlPredicate,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    nested: bool,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let binary = |label: &str,
                  left: &DefinitionMlPredicate,
                  right: &DefinitionMlPredicate,
                  output: &mut Rendered|
     -> Result<(), EmitError> {
        if nested {
            output.push("( ");
        }
        output.append(render_predicate(left, context, names, true)?);
        output.push(" ");
        output.push(label);
        output.push(" ");
        output.append(render_predicate(right, context, names, true)?);
        if nested {
            output.push(" )");
        }
        Ok(())
    };
    match predicate.kind() {
        IrMlKind::Top => output.push("#Top"),
        IrMlKind::Bottom => output.push("#Bottom"),
        IrMlKind::Not { operand } => {
            output.push("#Not ( ");
            output.append(render_predicate(operand, context, names, false)?);
            output.push(" )");
        }
        IrMlKind::And { left, right } => binary("#And", left, right, &mut output)?,
        IrMlKind::Or { left, right } => binary("#Or", left, right, &mut output)?,
        IrMlKind::Implies { left, right } => binary("#Implies", left, right, &mut output)?,
        IrMlKind::Equals { left, right, .. } => {
            output.push("{ ");
            output.append(render_term_with_binders(left, context, false, names, None)?);
            output.push(" #Equals ");
            output.append(render_term_with_binders(
                right, context, false, names, None,
            )?);
            output.push(" }");
        }
        IrMlKind::Ceil { term, .. } => {
            output.push("#Ceil ( ");
            output.append(render_term_with_binders(term, context, false, names, None)?);
            output.push(" )");
        }
        IrMlKind::Exists { binder, body } => {
            output.push("#Exists ");
            let start = output.text.len();
            output.push(names.name(binder.id()).ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "ml::exists binder {:?} is not named in its sentence",
                    binder.id().as_str()
                ))
            })?);
            let name_end = output.text.len();
            output.push(":");
            let sort_start = output.text.len();
            output.push(&context.sort_name_ref(binder.sort())?);
            let end = output.text.len();
            output
                .ranges
                .push((binder.name_origin().key().clone(), start, name_end));
            output
                .ranges
                .push((binder.sort_origin().key().clone(), sort_start, end));
            output
                .ranges
                .push((binder.origin().key().clone(), start, end));
            output.push(" . ");
            output.append(render_predicate(body, context, names, true)?);
        }
    }
    Ok(output.finish(predicate.origin().key(), 0))
}

/// The use of a constant that the term being rendered stands inside: the frames of that use's
/// origin up to and including the one naming the constant ([`constant_use`]).
type Enclosing<'t> = Option<&'t [OriginFrame]>;

/// The constant `term` was substituted from, with the frames of its origin up to and including
/// the one frame naming it: the use the author wrote, which every node of the substituted value
/// shares. `None` when no frame names a constant, or more than one does, which leaves the
/// literal unnamed rather than naming one constant of several.
fn constant_use(term: &DefinitionTerm) -> Option<(&[OriginFrame], &StableItemId)> {
    let frames = term.origin().origin().frames();
    let mut found = None;
    for (index, frame) in frames.iter().enumerate() {
        if let OriginFrame::Transformation {
            kind: TransformationOriginKind::SemanticIr,
            item: Some(item),
            label: Some(label),
        } = frame
            && label == crate::semantic::CONSTANT_FRAME_LABEL
            && item.item_kind() == ItemKind::Constant
        {
            if found.is_some() {
                return None;
            }
            found = Some((&frames[..=index], item));
        }
    }
    found
}

/// What the children of `term` stand inside, `term` itself standing inside `enclosing`: the
/// constant use `term` is part of, so that a literal below it is a part of that value and not
/// the whole of it; for a node KRS inserted that is part of no constant's value (a test's
/// connective), what `term` stands inside; otherwise nothing.
///
/// A node KRS inserted with a constant use's frames, a copy of a node of the value, encloses its
/// children in that use too: the frames do not tell such a copy from a node inserted around the
/// value, so a literal below it is left unnamed rather than named as a whole value it may not be.
fn within<'t>(term: &'t DefinitionTerm, enclosing: Enclosing<'t>) -> Enclosing<'t> {
    match constant_use(term) {
        Some((frames, _)) => Some(frames),
        None if term.origin().origin().inserted().is_some() => enclosing,
        None => None,
    }
}

fn is_wildcard(term: &DefinitionTerm) -> bool {
    matches!(
        term.kind(),
        DefinitionTermKind::Variable { variable } if variable.kind() == SemanticIdKind::Wildcard
    )
}

/// Whether a declared child at `parent` item `index` needs parentheses for
/// K's rule parser to read it back as the same tree. K's priority filter
/// (`PriorityVisitor`) checks only the leftmost and rightmost items of a
/// production: there it rejects a child whose group binds looser than the
/// parent's, a child of a left-associative group on the right, and one of a
/// right-associative group on the left, so the unparenthesized text would
/// parse as a different tree or not at all. Every grouped child under a
/// non-associative or prefix-unary production is parenthesized as well.
fn parenthesize_declared_child(
    parent: &ProductionSentence,
    index: usize,
    child: &DefinitionTerm,
    context: &EmitContext<'_>,
) -> Result<bool, EmitError> {
    let Some(parent_group) = production_group(parent) else {
        return Ok(false);
    };
    let DefinitionTermKind::Application {
        application: ApplicationRef::Declared(child_symbol),
        ..
    } = child.kind()
    else {
        return Ok(false);
    };
    let Some(child_group) = production_group(context.production(child_symbol)?) else {
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
    let relations = context.group_relations();
    if relations.is_non_associative(parent_group) || prefix_unary {
        return Ok(true);
    }
    let leftmost = index == 0;
    let rightmost = index + 1 == parent.items().len();
    Ok(
        (leftmost || rightmost) && relations.binds_looser(child_group, parent_group)
            || leftmost && relations.rejects_left_child(parent_group, child_group)
            || rightmost && relations.rejects_right_child(parent_group, child_group),
    )
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

fn render_builtin_application<'t>(
    operation: BuiltinOperation,
    arguments: &'t [DefinitionTerm],
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
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
                output.append(render_builtin_argument(
                    argument, context, names, enclosing,
                )?);
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
                    argument, context, false, names, enclosing,
                )?);
            }
            output.push(")");
        }
    }
    Ok(())
}

/// Renders K's generated sort predicate `isS(T)` or projection `{T}:>S`.
fn render_generated_application<'t>(
    operation: &GeneratedOperation<DefinitionSortRef>,
    arguments: &'t [DefinitionTerm],
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let [argument] = arguments else {
        return Err(EmitError::InvalidReference(format!(
            "a generated sort operation has invalid arity {}",
            arguments.len()
        )));
    };
    let operand = render_generated_operand(argument, context, names, enclosing)?;
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
fn render_generated_operand<'t>(
    argument: &'t DefinitionTerm,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let within = within(argument, enclosing);
    match argument.kind() {
        DefinitionTermKind::Map(operands) if operands.operation().spec().is_projected() => {
            render_collection_projected(
                argument.sort(),
                operands.operation().spec(),
                operands.operands(),
                context,
                names,
                within,
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
                within,
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
                within,
                &mut output,
                false,
            )?;
        }
        _ => return render_term_with_binders(argument, context, false, names, enclosing),
    }
    Ok(output.finish(argument.origin().key(), 0))
}

fn render_builtin_argument<'t>(
    argument: &'t DefinitionTerm,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
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
        argument, context, false, names, enclosing,
    )?);
    if parenthesize {
        output.push(")");
    }
    Ok(output)
}

/// The open ends of an operator-shaped collection term: whether its K spelling
/// begins (`.0`) or ends (`.1`) with one of its own operands, as `S1 -Set S2`,
/// `K in S`, and `M [ K <- undef ]` (open at the left only) do. A projected
/// lookup is braced, or parenthesized at `KItem`, so it is closed.
fn collection_open_ends(term: &DefinitionTerm) -> Option<(bool, bool)> {
    let spec = match term.kind() {
        DefinitionTermKind::Map(operands) => {
            if matches!(
                **operands,
                MapOperands::Items(_) | MapOperands::ItemsWithRest { .. }
            ) {
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

fn render_map<'t>(
    result_sort: &DefinitionSortRef,
    operands: &'t MapOperands<DefinitionTerm>,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'t>,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    // Items, and a pattern's rest after them, are juxtaposed: K's associative `_Map_`.
    let (entries, rest) = match operands {
        MapOperands::Items(entries) => (entries, None),
        MapOperands::ItemsWithRest { items, rest } => (items, Some(rest)),
        _ => {
            return render_collection(
                result_sort,
                operands.operation().spec(),
                operands.operands(),
                context,
                names,
                enclosing,
                output,
            );
        }
    };
    for (index, entry) in entries.iter().enumerate() {
        if index != 0 {
            output.push(MapOperation::CONCATENATION.separator);
        }
        // A value wildcard declared at a sort narrower than `KItem` (a readable map read's `_`,
        // narrowed by `_: S` or at the cell's value sort) matches only values of that sort,
        // and K's map value position is `KItem`, where a bare `_` would match any: it names
        // its sort, `K |-> _:S`, as a variable read once there would.
        let spec = MapOperation::Item.spec();
        if is_wildcard(&entry.value)
            && context.sort_name_ref(entry.value.sort())? != "KItem"
            && let CollectionNotation::Mixfix { pieces } = spec.k_notation
            && let [open, arrow, close] = pieces
        {
            let parenthesize = parenthesize_collection_operand(spec, 0, &entry.key, open, arrow);
            output.push(open);
            if parenthesize {
                output.push("(");
            }
            output.append(render_term_with_binders(
                &entry.key, context, false, names, enclosing,
            )?);
            if parenthesize {
                output.push(")");
            }
            output.push(arrow);
            output.append(render_sequence_wildcard(&entry.value, context)?);
            output.push(close);
            continue;
        }
        render_collection(
            result_sort,
            spec,
            [&entry.key, &entry.value].into_iter(),
            context,
            names,
            enclosing,
            output,
        )?;
    }
    if let Some(rest) = rest {
        output.push(MapOperation::CONCATENATION.separator);
        output.append(render_term_with_binders(
            rest, context, false, names, enclosing,
        )?);
    }
    Ok(())
}

fn render_collection<'a>(
    result_sort: &DefinitionSortRef,
    spec: &CollectionOperationSpec,
    operands: impl Iterator<Item = &'a DefinitionTerm>,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'a>,
    output: &mut Rendered,
) -> Result<(), EmitError> {
    render_collection_projected(
        result_sort,
        spec,
        operands,
        context,
        names,
        enclosing,
        output,
        true,
    )
}

/// Renders a collection operation; `project` is false only for the operand
/// of a generated sort operation, which supplies the one cast itself. A
/// projected lookup read at `KItem`, the sort K's lookup already has, is the
/// lookup itself: its projection would be the identity, so it is written in
/// parentheses, which keep it one closed term as the braces do.
#[expect(
    clippy::too_many_arguments,
    reason = "The operands' rendering needs the sentence's names and the constant use they stand in."
)]
fn render_collection_projected<'a>(
    result_sort: &DefinitionSortRef,
    spec: &CollectionOperationSpec,
    operands: impl Iterator<Item = &'a DefinitionTerm>,
    context: &EmitContext<'_>,
    names: &SentenceVariables,
    enclosing: Enclosing<'a>,
    output: &mut Rendered,
    project: bool,
) -> Result<(), EmitError> {
    let project = project && spec.is_projected();
    let identity = project && context.sort_name_ref(result_sort)? == "KItem";
    if project {
        output.push(if identity { "(" } else { "{" });
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
                output.append(render_term_with_binders(
                    operand, context, false, names, enclosing,
                )?);
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
                output.append(render_term_with_binders(
                    operand, context, false, names, enclosing,
                )?);
            }
            output.push(")");
        }
    }
    if project && identity {
        output.push(")");
    } else if project {
        output.push("}:>");
        output.push(&context.sort_name_ref(result_sort)?);
    }
    Ok(())
}
