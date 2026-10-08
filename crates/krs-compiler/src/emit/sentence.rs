use std::collections::BTreeSet;

use krs_ir::{
    BuiltinSort, CellAttribute, CellContentFrame, CellPost, ClaimModality, ConfigurationRoot,
    FixedCell, FixedCellContent, FixedCellPattern, FixedConfiguration, FixedConfigurationVariable,
    FixedInitializerCell, FixedInitializerContent, FormatFragment, GrammarProductionItemKind,
    GroupAssociativity, MapOperation, ProductionAttribute, ProductionGroupId, SemanticId,
    SentenceKind, StrictnessKind,
};
use krs_ir_levels::{
    ContextAliasSentence, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, LabelIdentity, ProductionSentence, RuleBodyRef, RuleSentence, SymbolId,
    k_surface::SentenceVariables,
};

use super::{
    EmitContext, EmitError, Writer, quoted_kstring, quoted_outer,
    term::{render_context_term, render_rewrite, render_term},
};

pub(super) fn emit_sentence(
    sentence: &DefinitionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if let DefinitionSentence::Rule(rule) = sentence {
        for feature in crate::capability::sentence_features(rule) {
            writer.push("  // krs-capability: ");
            writer.push(feature.name());
            writer.push(" ");
            writer.push(rule.label().emitted_name());
            writer.push("\n");
        }
    }
    let start = writer.source.len();
    writer.push("  ");
    match sentence {
        DefinitionSentence::SyntaxSort(sentence) => {
            writer.push("syntax ");
            writer.push(sentence.symbol().emitted_name());
        }
        DefinitionSentence::Subsort(sentence) => {
            writer.push("syntax ");
            writer.push(context.sort_name_ref(sentence.supersort())?);
            writer.push(" ::= ");
            writer.push(context.sort_name_ref(sentence.subsort())?);
        }
        DefinitionSentence::Production(sentence) => emit_production(sentence, context, writer)?,
        DefinitionSentence::Precedence(sentence) => {
            writer.push("syntax priority ");
            emit_group_list(sentence.higher(), context, writer)?;
            writer.push(" > ");
            emit_group_list(sentence.lower(), context, writer)?;
        }
        DefinitionSentence::Associativity(sentence) => {
            writer.push(match sentence.associativity() {
                GroupAssociativity::Left => "syntax left ",
                GroupAssociativity::Right => "syntax right ",
                GroupAssociativity::NonAssociative => "syntax non-assoc ",
            });
            emit_group_list(sentence.groups(), context, writer)?;
        }
        DefinitionSentence::Configuration(sentence) => {
            emit_fixed_configuration(sentence, context, writer)?;
        }
        DefinitionSentence::ContextAlias(sentence) => {
            emit_context_alias(sentence, context, writer)?;
        }
        DefinitionSentence::Rule(sentence) => emit_rule(sentence, context, writer)?,
    }
    writer.push("\n");
    writer.record(sentence.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_production(
    sentence: &ProductionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for attribute in sentence.attributes() {
        if let ProductionAttribute::Documentation { text, .. } = attribute {
            let start = writer.source.len();
            writer.push("// ");
            writer.push(text);
            writer.record(attribute.origin().key(), start, writer.source.len())?;
            writer.push("\n  ");
        }
    }
    writer.push("syntax ");
    writer.push(context.sort_name_ref(sentence.result_sort())?);
    writer.push(" ::= ");
    for (index, item) in sentence.items().iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        let start = writer.source.len();
        match item.kind() {
            GrammarProductionItemKind::Terminal { text } => writer.push(&quoted_outer(text)),
            GrammarProductionItemKind::NonTerminal { sort, .. } => {
                writer.push(context.sort_name_ref(sort)?);
            }
            GrammarProductionItemKind::RegexTerminal { regex, .. } => {
                writer.push("r");
                writer.push(&quoted_outer(regex));
            }
        }
        writer.record(item.origin().key(), start, writer.source.len())?;
    }
    // A token production denotes domain values of its sort, not a
    // constructor, so it carries no symbol: K's Haskell backend rejects a
    // constructor on a sort that has domain values. A bracket production is
    // parse-only, so no term contains its symbol; Java K declares a labelled
    // bracket as a constructor in definition.kore while k-rust declares none
    // (bracket-production-constructor), so an unlabelled bracket is the form
    // on which both routes agree.
    let is_parse_only = sentence.attributes().iter().any(|attribute| {
        matches!(
            attribute,
            ProductionAttribute::Token { .. } | ProductionAttribute::Bracket { .. }
        )
    });
    writer.push(" [");
    let mut first = true;
    if !is_parse_only {
        writer.push("symbol(");
        writer.push(sentence.symbol().emitted_name());
        writer.push(")");
        first = false;
    }
    for attribute in sentence.attributes() {
        if matches!(attribute, ProductionAttribute::Documentation { .. }) {
            continue;
        }
        if !first {
            writer.push(", ");
        }
        first = false;
        let start = writer.source.len();
        emit_production_attribute(attribute, sentence, context, writer)?;
        writer.record(attribute.origin().key(), start, writer.source.len())?;
    }
    writer.push("]");
    Ok(())
}

fn emit_group_list(
    groups: &[ProductionGroupId],
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (index, group) in groups.iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        writer.push(context.group_name(group)?);
    }
    Ok(())
}

#[expect(
    clippy::too_many_lines,
    reason = "Keeps exhaustive production attribute emission in one match."
)]
fn emit_production_attribute(
    attribute: &krs_ir_levels::DefinitionProductionAttribute,
    sentence: &ProductionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    match attribute {
        ProductionAttribute::Documentation { .. } => {}
        ProductionAttribute::Function { .. } => writer.push("function"),
        ProductionAttribute::Total { .. } => writer.push("total"),
        ProductionAttribute::Hook { operation, .. } => {
            writer.push("hook(");
            writer.push(operation.spec().k_hook);
            writer.push(")");
        }
        ProductionAttribute::Alias { .. } => writer.push("alias"),
        ProductionAttribute::Token {
            lexical_precedence, ..
        } => {
            writer.push("token");
            if let Some(precedence) = lexical_precedence {
                writer.push(", prec(");
                writer.push(&precedence.to_string());
                writer.push(")");
            }
        }
        ProductionAttribute::Group { group, .. } => {
            writer.push("group(");
            writer.push(context.group_name(group)?);
            writer.push(")");
        }
        ProductionAttribute::Bracket { .. } => {
            writer.push("bracket, format(");
            for index in 1..=sentence.items().len() {
                writer.push("%");
                writer.push(&index.to_string());
            }
            writer.push(")");
        }
        ProductionAttribute::Avoid { .. } => writer.push("avoid"),
        ProductionAttribute::Prefer { .. } => writer.push("prefer"),
        ProductionAttribute::Private { .. } => writer.push("private"),
        ProductionAttribute::Overload { target, .. } => {
            writer.push("overload(");
            writer.push(context.production(target)?.symbol().emitted_name());
            writer.push(")");
        }
        ProductionAttribute::Format { fragments, .. } => {
            writer.push("format(");
            for fragment in fragments {
                match fragment {
                    FormatFragment::Literal(text) => {
                        for character in text.chars() {
                            if character == '%' {
                                writer.push("%%");
                            } else {
                                writer.push(&character.to_string());
                            }
                        }
                    }
                    FormatFragment::Item(index) => {
                        writer.push("%");
                        writer.push(&index.to_string());
                    }
                    FormatFragment::Newline => writer.push("%n"),
                    FormatFragment::Indent => writer.push("%i"),
                    FormatFragment::Dedent => writer.push("%d"),
                    FormatFragment::ColorNext => writer.push("%c"),
                    FormatFragment::ColorReset => writer.push("%r"),
                }
            }
            writer.push(")");
        }
        ProductionAttribute::Color { value, .. } => {
            writer.push("color(");
            writer.push(value);
            writer.push(")");
        }
        ProductionAttribute::Colors { values, .. } => {
            writer.push("colors(");
            writer.push(&values.join(","));
            writer.push(")");
        }
        ProductionAttribute::Internal { .. } | ProductionAttribute::Program { .. } => {
            return Err(EmitError::UnsupportedShape {
                node: "production attribute",
                detail: "`internal` and `program` are consumed by lowering".to_owned(),
            });
        }
        ProductionAttribute::Strictness {
            kind,
            using,
            fields,
            result_sort,
            ..
        } => {
            writer.push(match kind {
                StrictnessKind::Strict => "strict",
                StrictnessKind::SeqStrict => "seqstrict",
            });
            let nonterminals = sentence
                .items()
                .iter()
                .filter_map(|item| match item.kind() {
                    GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let selects_all = fields.len() == nonterminals.len()
                && fields
                    .iter()
                    .zip(&nonterminals)
                    .all(|(selected, field)| selected.field() == *field);
            if using.is_some() || !selects_all {
                writer.push("(");
                if let Some(using) = using {
                    let using_start = writer.source.len();
                    writer.push(&k_label_name(context.context_alias_name(using.alias())?));
                    writer.record(using.origin().key(), using_start, writer.source.len())?;
                    if !fields.is_empty() {
                        writer.push("; ");
                    }
                }
                for (index, field) in fields.iter().enumerate() {
                    if index != 0 {
                        writer.push(",");
                    }
                    let position = nonterminals
                        .iter()
                        .position(|candidate| **candidate == *field.field())
                        .ok_or_else(|| {
                            EmitError::InvalidReference(format!(
                                "strictness references missing field {:?}",
                                field.field().as_str()
                            ))
                        })?;
                    let field_start = writer.source.len();
                    writer.push(&(position + 1).to_string());
                    writer.record(field.origin().key(), field_start, writer.source.len())?;
                }
                writer.push(")");
            }
            writer.push(", result(");
            let result_start = writer.source.len();
            writer.push(context.sort_name_ref(result_sort.sort())?);
            writer.record(
                result_sort.origin().key(),
                result_start,
                writer.source.len(),
            )?;
            writer.push(")");
        }
    }
    Ok(())
}

fn emit_fixed_configuration(
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push("configuration");
    writer.push("\n");
    let names = context.naming.configuration(configuration);
    match configuration.root() {
        ConfigurationRoot::GeneratedTop => emit_fixed_cell_forest(
            configuration.cells(),
            configuration.initializer(),
            configuration.variables(),
            &names,
            4,
            context,
            writer,
        )?,
        ConfigurationRoot::Named { origin, name } => {
            let start = writer.source.len();
            writer.push("    <");
            writer.push(name);
            writer.push(">\n");
            emit_fixed_cell_forest(
                configuration.cells(),
                configuration.initializer(),
                configuration.variables(),
                &names,
                6,
                context,
                writer,
            )?;
            writer.push("    </");
            writer.push(name);
            writer.push(">");
            writer.record(origin.key(), start, writer.source.len())?;
        }
    }
    writer.record(
        configuration.initializer_origin().key(),
        writer.source.len(),
        writer.source.len(),
    )?;
    writer.push("\n");
    Ok(())
}

fn emit_fixed_cell_forest(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    names: &SentenceVariables,
    indent: usize,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (index, cell) in cells.iter().enumerate() {
        if index != 0 {
            writer.push("\n");
        }
        let initialized_cell = initializer
            .iter()
            .find(|value| value.cell() == cell.id())
            .ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "missing initializer for fixed cell {:?}",
                    cell.id().as_str()
                ))
            })?;
        emit_fixed_cell(
            cell,
            initialized_cell,
            variables,
            names,
            indent,
            context,
            writer,
        )?;
    }
    Ok(())
}

fn emit_fixed_cell(
    cell: &FixedCell<DefinitionSortRef, SymbolId>,
    initializer_cell: &FixedInitializerCell<SymbolId, DefinitionTerm>,
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    names: &SentenceVariables,
    indent: usize,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    writer.push(&" ".repeat(indent));
    writer.push("<");
    writer.push(cell.name());
    for attribute in cell.attributes() {
        match attribute {
            CellAttribute::Color { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" color=");
                writer.push(&quoted_kstring(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::Multiplicity { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" multiplicity=");
                writer.push(&quoted_kstring(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::CollectionType { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" type=");
                writer.push(&quoted_kstring(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
        }
    }
    writer.push(">");
    match (cell.content(), initializer_cell.content()) {
        (FixedCellContent::Term { .. }, FixedInitializerContent::Term { term }) => {
            writer.push(" ");
            emit_initializer_term(term, variables, names, context, writer)?;
            writer.push(" </");
            writer.push(cell.name());
            writer.push(">");
        }
        (
            FixedCellContent::Children { children },
            FixedInitializerContent::Children {
                children: initialized_children,
            },
        ) => {
            writer.push("\n");
            emit_fixed_cell_forest(
                children,
                initialized_children,
                variables,
                names,
                indent + 2,
                context,
                writer,
            )?;
            writer.push("\n");
            writer.push(&" ".repeat(indent));
            writer.push("</");
            writer.push(cell.name());
            writer.push(">");
        }
        _ => {
            return Err(EmitError::InvalidReference(format!(
                "fixed cell {:?} and initializer shapes disagree",
                cell.id().as_str()
            )));
        }
    }
    writer.record(initializer_cell.origin().key(), start, writer.source.len())?;
    writer.record(cell.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_initializer_term(
    term: &DefinitionTerm,
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let (term, sequence_origin) = match term.kind() {
        DefinitionTermKind::KSequence { items, .. } if items.len() == 1 => (&items[0], Some(term)),
        _ => (term, None),
    };
    if let DefinitionTermKind::Variable { variable } = term.kind()
        && let Some(declaration) = variables.iter().find(|value| value.id() == variable)
    {
        let start = writer.source.len();
        writer.push("$");
        writer.push(declaration.external_name());
        writer.push(":");
        writer.push(context.sort_name_ref(term.sort())?);
        writer.record(term.origin().key(), start, writer.source.len())?;
        writer.record(declaration.origin().key(), start, writer.source.len())?;
        if let Some(sequence) = sequence_origin {
            writer.record(sequence.origin().key(), start, writer.source.len())?;
        }
    } else {
        writer.append_rendered(render_term(term, context, names, false)?)?;
    }
    Ok(())
}

fn emit_rule(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let sentence_start = writer.source.len();
    let names = context.naming.rule(sentence);
    match sentence.relational_body() {
        RuleBodyRef::Configuration { body, .. } => {
            if sentence.kind() == SentenceKind::Claim {
                let claim_start = writer.source.len();
                writer.push("claim");
                if let Some(claim) = sentence.claim()
                    && claim.modality() == ClaimModality::AllPaths
                {
                    writer.record(
                        claim.modality_origin().key(),
                        claim_start,
                        writer.source.len(),
                    )?;
                }
                writer.push(" [");
            } else {
                writer.push("rule [");
            }
            emit_label(sentence.label(), writer);
            writer.push("]:");
            let mut emitted_repeated = BTreeSet::new();
            for clause in body.clauses() {
                let Some(ancestor) = context.repeated_ancestor(clause.cell()) else {
                    writer.push("\n");
                    emit_cell_clause(clause, &names, context, 4, writer)?;
                    continue;
                };
                if !emitted_repeated.insert(ancestor.clone()) {
                    continue;
                }
                writer.push("\n    <");
                writer.push(context.cell_name(ancestor)?);
                writer.push(">");
                for nested in body.clauses().iter().filter(|candidate| {
                    context.repeated_ancestor(candidate.cell()) == Some(ancestor)
                }) {
                    writer.push("\n");
                    emit_cell_clause(nested, &names, context, 8, writer)?;
                }
                writer.push("\n        ...\n    </");
                writer.push(context.cell_name(ancestor)?);
                writer.push(">");
            }
            emit_requires(sentence, &names, context, writer)?;
            emit_ensures(sentence, &names, context, writer)?;
            emit_rule_attributes(sentence, writer)?;
            record_claim_binders(sentence, &names, context, sentence_start, writer)?;
            Ok(())
        }
        RuleBodyRef::Term(body) => {
            writer.push("rule ");
            writer.append_rendered(
                render_rewrite(body.from(), body.to(), context, true, &names)?
                    .finish(body.origin().key(), 0),
            )?;
            emit_requires(sentence, &names, context, writer)?;
            emit_term_rule_attributes(sentence, writer)?;
            Ok(())
        }
    }
}

fn emit_term_rule_attributes(
    sentence: &RuleSentence,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push(" [");
    if let Some(simplification) = sentence.simplification() {
        let start = writer.source.len();
        writer.push("simplification");
        if let Some(priority) = simplification.priority() {
            writer.push("(");
            let priority_start = writer.source.len();
            writer.push(&priority.value().to_string());
            writer.record(priority.origin().key(), priority_start, writer.source.len())?;
            writer.push(")");
        }
        writer.record(simplification.origin().key(), start, writer.source.len())?;
        writer.push(", ");
    }
    if let Some(priority) = sentence.priority() {
        let start = writer.source.len();
        writer.push("priority(");
        writer.push(&priority.value().to_string());
        writer.push("), ");
        writer.record(priority.origin().key(), start, writer.source.len() - 2)?;
    }
    if let Some(anywhere) = sentence.anywhere() {
        let start = writer.source.len();
        writer.push("anywhere");
        writer.record(anywhere.key(), start, writer.source.len())?;
        writer.push(", ");
    }
    writer.push("label(");
    emit_label(sentence.label(), writer);
    writer.push(")]");
    Ok(())
}

fn record_claim_binders(
    sentence: &RuleSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    sentence_start: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let Some(claim) = sentence.claim() else {
        return Ok(());
    };
    for binder in claim.universals().iter().chain(claim.existentials()) {
        let name = names.name(binder.id()).ok_or_else(|| {
            EmitError::InvalidReference(format!(
                "claim binder {:?} is not named in its sentence",
                binder.id().as_str()
            ))
        })?;
        let rendered = format!("{name}:{}", context.sort_name_ref(binder.sort())?);
        let start = sentence_start
            + first_variable_occurrence(&writer.source[sentence_start..], &rendered).ok_or_else(
                || {
                    EmitError::InvalidReference(format!(
                        "claim binder {:?} has no rendered occurrence",
                        binder.id().as_str()
                    ))
                },
            )?;
        let end = start + rendered.len();
        for origin in [binder.origin(), binder.name_origin(), binder.sort_origin()] {
            writer.record(origin.key(), start, end)?;
        }
    }
    Ok(())
}

/// Finds `rendered` where it begins a whole variable, not inside a longer one.
fn first_variable_occurrence(source: &str, rendered: &str) -> Option<usize> {
    source
        .match_indices(rendered)
        .map(|(index, _)| index)
        .find(|index| {
            !source[..*index].ends_with(|character: char| {
                character.is_ascii_alphanumeric()
                    || matches!(character, '_' | '\'' | '?' | '!' | '@')
            })
        })
}

fn emit_ensures(
    sentence: &RuleSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let Some(ensures) = sentence.claim().and_then(|claim| claim.ensures()) else {
        return Ok(());
    };
    writer.push("\n    ensures ");
    let start = writer.source.len();
    writer.append_rendered(render_term(ensures.term(), context, names, false)?)?;
    writer.record(ensures.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_rule_attributes(sentence: &RuleSentence, writer: &mut Writer) -> Result<(), EmitError> {
    let mut attributes = Vec::<(
        &str,
        Option<u32>,
        Option<&krs_ir::NodeOrigin>,
        Option<&krs_ir::NodeOrigin>,
    )>::new();
    if let Some(priority) = sentence.priority() {
        attributes.push((
            "priority",
            Some(priority.value()),
            Some(priority.origin()),
            None,
        ));
    }
    if let Some(simplification) = sentence.simplification() {
        attributes.push((
            "simplification",
            simplification
                .priority()
                .map(krs_ir_levels::DefinitionSimplificationPriority::value),
            Some(simplification.origin()),
            simplification
                .priority()
                .map(krs_ir_levels::DefinitionSimplificationPriority::origin),
        ));
    }
    if let Some(claim) = sentence.claim() {
        if claim.modality() == ClaimModality::OnePath {
            attributes.push(("one-path", None, Some(claim.modality_origin()), None));
        }
        if let Some(origin) = claim.circularity_origin() {
            attributes.push(("circularity", None, Some(origin), None));
        }
    }
    if attributes.is_empty() {
        return Ok(());
    }
    writer.push("\n    [");
    for (index, (name, value, origin, value_origin)) in attributes.into_iter().enumerate() {
        if index != 0 {
            writer.push(", ");
        }
        let start = writer.source.len();
        writer.push(name);
        if let Some(value) = value {
            writer.push("(");
            let value_start = writer.source.len();
            writer.push(&value.to_string());
            if let Some(value_origin) = value_origin {
                writer.record(value_origin.key(), value_start, writer.source.len())?;
            }
            writer.push(")");
        }
        if let Some(origin) = origin {
            writer.record(origin.key(), start, writer.source.len())?;
        }
    }
    writer.push("]");
    Ok(())
}

fn emit_requires(
    sentence: &RuleSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if let Some(condition) = sentence.requires() {
        writer.push("\n    requires ");
        let start = writer.source.len();
        writer.append_rendered(render_term(condition.term(), context, names, false)?)?;
        writer.record(condition.origin().key(), start, writer.source.len())?;
    }
    Ok(())
}

fn emit_cell_clause(
    clause: &krs_ir::FixedCellClause<SymbolId, DefinitionTerm>,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(clause.cell())?;
    writer.push(&" ".repeat(indent));
    writer.push("<");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_term(clause.before(), context, names, false)?)?;
    match clause.after() {
        CellPost::Preserve => emit_single_frame(clause.frame(), names, writer)?,
        CellPost::Replace { term } => {
            match clause.frame() {
                CellContentFrame::KSequenceTail {
                    binding: Some(binding),
                    ..
                } => emit_named_frame_suffix(
                    writer,
                    names,
                    binding,
                    BuiltinSort::KSequence.k_name(),
                    " ~> ",
                )?,
                CellContentFrame::MapRemainder {
                    binding: Some(binding),
                    ..
                } => emit_named_frame_suffix(
                    writer,
                    names,
                    binding,
                    BuiltinSort::Map.k_name(),
                    MapOperation::CONCATENATION.separator,
                )?,
                CellContentFrame::Exact
                | CellContentFrame::KSequenceTail { binding: None, .. }
                | CellContentFrame::MapRemainder { binding: None, .. } => {}
            }
            writer.push(" => ");
            writer.append_rendered(render_term(term, context, names, false)?)?;
            emit_single_frame(clause.frame(), names, writer)?;
        }
    }
    writer.push(" </");
    writer.push(name);
    writer.push(">");
    writer.record(clause.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_single_frame(
    frame: &CellContentFrame,
    names: &SentenceVariables,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    match frame {
        CellContentFrame::Exact => {}
        CellContentFrame::KSequenceTail { origin, binding } => {
            let frame_start = writer.source.len();
            if let Some(binding) = binding {
                emit_named_frame_suffix(
                    writer,
                    names,
                    binding,
                    BuiltinSort::KSequence.k_name(),
                    " ~> ",
                )?;
            } else {
                writer.push(" ...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
        CellContentFrame::MapRemainder { origin, binding } => {
            let frame_start = writer.source.len();
            if let Some(binding) = binding {
                emit_named_frame_suffix(
                    writer,
                    names,
                    binding,
                    BuiltinSort::Map.k_name(),
                    MapOperation::CONCATENATION.separator,
                )?;
            } else {
                writer.push(" ...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
    }
    Ok(())
}

fn emit_named_frame_suffix(
    writer: &mut Writer,
    names: &SentenceVariables,
    binding: &SemanticId,
    sort: &str,
    separator: &str,
) -> Result<(), EmitError> {
    let name = names.name(binding).ok_or_else(|| {
        EmitError::InvalidReference(format!(
            "frame binding {:?} is not named in its sentence",
            binding.as_str()
        ))
    })?;
    writer.push(separator);
    writer.push(name);
    writer.push(":");
    writer.push(sort);
    Ok(())
}

fn emit_context_alias(
    sentence: &ContextAliasSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push("context alias [");
    let name_start = writer.source.len();
    writer.push(&k_label_name(sentence.name()));
    writer.record(
        sentence.name_origin().key(),
        name_start,
        writer.source.len(),
    )?;
    writer.push("]:");
    let names = context.naming.context_alias(sentence);
    for cell in sentence.body().cells() {
        writer.push("\n");
        emit_context_alias_cell(cell, sentence, &names, context, writer)?;
    }
    Ok(())
}

fn emit_context_alias_cell(
    cell: &FixedCellPattern<SymbolId, DefinitionTerm>,
    sentence: &ContextAliasSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(cell.cell())?;
    writer.push("    <");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_context_term(
        cell.pattern(),
        sentence.here(),
        sentence.here_origin(),
        context,
        names,
    )?)?;
    emit_single_frame(cell.frame(), names, writer)?;
    writer.push(" </");
    writer.push(name);
    writer.push(">");
    writer.record(cell.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_label(label: &LabelIdentity, writer: &mut Writer) {
    writer.push(label.emitted_name());
}

fn k_label_name(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut uppercase_next = false;
    for character in value.chars() {
        if character == '_' {
            uppercase_next = true;
        } else if uppercase_next {
            output.extend(character.to_uppercase());
            uppercase_next = false;
        } else {
            output.push(character);
        }
    }
    output
}
