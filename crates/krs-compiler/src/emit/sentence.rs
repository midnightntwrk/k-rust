use std::collections::BTreeSet;

use krs_ir::{
    BuiltinSort, CellAttribute, CellContentFrame, CellPost, ClaimModality, ConfigurationClause,
    ConfigurationRoot, FixedCell, FixedCellContent, FixedCellPattern, FixedConfiguration,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, FormatFragment,
    GrammarProductionItemKind, GroupAssociativity, MapOperation, ProductionAttribute,
    ProductionGroupId, SemanticId, SentenceKind, SmtFragment, StrictnessKind,
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
    // K generates a syntactic list's terminator production from its cons
    // sentence `List{..}`, so the terminator is not printed (KF-020).
    if let DefinitionSentence::Production(production) = sentence
        && is_list_terminator(production)
    {
        return Ok(());
    }
    if let DefinitionSentence::Configuration(configuration) = sentence {
        for (cell, _) in crate::capability::stream_cells(configuration.cells()) {
            writer.push("  // krs-capability: ");
            writer.push(crate::capability::CapabilityFeature::ConsoleIO.name());
            writer.push(" ");
            writer.push(&cell);
            writer.push("\n");
        }
    }
    if let DefinitionSentence::Raw(raw) = sentence {
        writer.push("  // raw_k! ");
        writer.push(&raw_location(raw));
        writer.push(" (opaque to KRS)\n");
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
            writer.push(&context.sort_name_ref(sentence.supersort())?);
            writer.push(" ::= ");
            writer.push(&context.sort_name_ref(sentence.subsort())?);
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
        DefinitionSentence::Rule(sentence) if sentence.kind() == SentenceKind::Context => {
            emit_context(sentence, context, writer)?;
        }
        DefinitionSentence::Rule(sentence) => emit_rule(sentence, context, writer)?,
        DefinitionSentence::Lexical(sentence) => {
            writer.push("syntax lexical ");
            writer.push(sentence.name());
            writer.push(" = r");
            writer.push(&quoted_outer(sentence.regex()));
        }
        DefinitionSentence::Layout(sentence) => {
            // Java K 7.1.337 requires `[token]` on a layout production
            // ("Symbol ..#Layout is not unique" otherwise).
            writer.push("syntax #Layout ::= r");
            writer.push(&quoted_outer(sentence.regex()));
            writer.push(" [token]");
        }
        DefinitionSentence::Raw(sentence) => writer.push(&sentence.text),
    }
    writer.push("\n");
    writer.record(sentence.origin().key(), start, writer.source.len())?;
    Ok(())
}

/// `src/lib.rs:12:1`: the package-relative file and position of a `raw_k!`.
pub(crate) fn raw_location(raw: &krs_ir::RawSentence) -> String {
    let file = raw.origin.origin().exact_authored_range().map_or_else(
        || "<unknown>".to_owned(),
        |range| range.file.package_relative_path().to_owned(),
    );
    format!("{file}:{}:{}", raw.line, raw.column)
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
    // K's `syntax {S, T} R ::= ..` declares a parametric production (KF-027).
    if !sentence.parameters().is_empty() {
        writer.push("{");
        for (index, parameter) in sentence.parameters().iter().enumerate() {
            if index != 0 {
                writer.push(", ");
            }
            writer.push(parameter.as_str());
        }
        writer.push("} ");
    }
    writer.push(&context.sort_name_ref(sentence.result_sort())?);
    writer.push(" ::= ");
    let list = sentence
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::ListCons {
                separator,
                non_empty,
                ..
            } => Some((separator.as_str(), *non_empty)),
            _ => None,
        });
    if let Some((separator, non_empty)) = list {
        emit_list_items(sentence, separator, non_empty, context, writer)?;
    } else {
        emit_production_items(sentence, context, writer)?;
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
    // A list's `terminator-symbol` follows its `symbol` (KF-020).
    let attributes = sentence
        .attributes()
        .iter()
        .filter(|attribute| matches!(attribute, ProductionAttribute::ListCons { .. }))
        .chain(
            sentence
                .attributes()
                .iter()
                .filter(|attribute| !matches!(attribute, ProductionAttribute::ListCons { .. })),
        );
    for attribute in attributes {
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

fn emit_production_items(
    sentence: &ProductionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (index, item) in sentence.items().iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        let start = writer.source.len();
        match item.kind() {
            GrammarProductionItemKind::Terminal { text } => writer.push(&quoted_outer(text)),
            GrammarProductionItemKind::NonTerminal { sort, .. } => {
                writer.push(&context.sort_name_ref(sort)?);
            }
            GrammarProductionItemKind::RegexTerminal { regex, .. } => {
                writer.push("r");
                writer.push(&quoted_outer(regex));
            }
        }
        writer.record(item.origin().key(), start, writer.source.len())?;
    }
    Ok(())
}

fn is_list_terminator(sentence: &ProductionSentence) -> bool {
    sentence
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::ListTerminator { .. }))
}

/// Renders an `smt_hook` template in K's positional form: each field becomes
/// `#N`, its one-based position among the production's nonterminals (KF-044).
pub(crate) fn smt_hook_text(
    template: &[SmtFragment],
    sentence: &ProductionSentence,
) -> Result<String, EmitError> {
    let nonterminals = sentence
        .items()
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut text = String::new();
    for fragment in template {
        match fragment {
            SmtFragment::Text(literal) => text.push_str(literal),
            SmtFragment::Field(field) => {
                let position = nonterminals
                    .iter()
                    .position(|candidate| *candidate == field)
                    .ok_or_else(|| EmitError::UnsupportedShape {
                        node: "smt-hook",
                        detail: format!("placeholder `{{{}}}` names no field", field.as_str()),
                    })?;
                text.push('#');
                text.push_str(&(position + 1).to_string());
            }
        }
    }
    Ok(text)
}

/// Prints the cons production of a syntactic list as K's `List{Elem, "sep"}`
/// or `NeList{..}`; the tail item is the list sort itself and is implicit.
fn emit_list_items(
    sentence: &ProductionSentence,
    separator: &str,
    non_empty: bool,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push(if non_empty { "NeList{" } else { "List{" });
    let mut items = sentence.items().iter();
    let head = items.next().ok_or_else(|| EmitError::UnsupportedShape {
        node: "syntactic list",
        detail: "a list cons production has a head item".to_owned(),
    })?;
    let GrammarProductionItemKind::NonTerminal { sort, .. } = head.kind() else {
        return Err(EmitError::UnsupportedShape {
            node: "syntactic list",
            detail: "a list head is a nonterminal".to_owned(),
        });
    };
    let start = writer.source.len();
    writer.push(&context.sort_name_ref(sort)?);
    writer.record(head.origin().key(), start, writer.source.len())?;
    writer.push(", ");
    let start = writer.source.len();
    writer.push(&quoted_outer(separator));
    if let Some(item) = items
        .next()
        .filter(|item| matches!(item.kind(), GrammarProductionItemKind::Terminal { .. }))
    {
        writer.record(item.origin().key(), start, writer.source.len())?;
    }
    writer.push("}");
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
        ProductionAttribute::Alias { recursive, .. } => {
            writer.push(if *recursive { "alias-rec" } else { "alias" });
        }
        ProductionAttribute::Desugar { recursive, .. } => {
            writer.push(if *recursive { "macro-rec" } else { "macro" });
        }
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
        ProductionAttribute::Memo { .. } => writer.push("memo"),
        ProductionAttribute::FreshGenerator { .. } => writer.push("freshGenerator"),
        ProductionAttribute::Smtlib { symbol, .. } => {
            writer.push("smtlib(");
            writer.push(symbol);
            writer.push(")");
        }
        ProductionAttribute::SmtHook { template, .. } => {
            writer.push("smt-hook(");
            writer.push(&smt_hook_text(template, sentence)?);
            writer.push(")");
        }
        ProductionAttribute::ListCons { terminator, .. } => {
            writer.push("terminator-symbol(");
            writer.push(context.production(terminator)?.symbol().emitted_name());
            writer.push(")");
        }
        ProductionAttribute::ListTerminator { .. } => {
            return Err(EmitError::UnsupportedShape {
                node: "syntactic list",
                detail: "a list terminator production is generated from its cons sentence"
                    .to_owned(),
            });
        }
        ProductionAttribute::RawHook {
            namespace, name, ..
        } => {
            writer.push("hook(");
            writer.push(namespace);
            writer.push(".");
            writer.push(name);
            writer.push(")");
        }
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
            writer.push(&context.sort_name_ref(result_sort.sort())?);
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
            CellAttribute::Stream { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" stream=");
                writer.push(&quoted_kstring(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::Exit { origin } => {
                let attribute_start = writer.source.len();
                writer.push(" exit=\"\"");
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::Initial { origin } => {
                let attribute_start = writer.source.len();
                writer.push(" initial=\"\"");
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
        writer.push(&context.sort_name_ref(term.sort())?);
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
            emit_configuration_clauses(body, &names, context, writer)?;
            emit_requires(sentence, &names, context, writer)?;
            emit_ensures(sentence, &names, context, writer)?;
            emit_rule_attributes(sentence, context, writer)?;
            record_claim_binders(sentence, &names, context, sentence_start, writer)?;
            Ok(())
        }
        RuleBodyRef::Term(body) => {
            writer.push("rule ");
            let function_context = sentence.function_context();
            if function_context.is_some() {
                // K's function context (KF-025): `[[ F => R ]]` and then the
                // configuration cells the equation reads.
                writer.push("[[ ");
            }
            // A single-body rule (KF-011) is K's local form: the rewrites
            // sit inside the term, `pair((A => B), B)`.
            let rendered = match body.local_term() {
                Some(local) => render_term(local, context, &names, false)?,
                None => render_rewrite(body.from(), body.to(), context, true, &names)?
                    .finish(body.origin().key(), 0),
            };
            writer.append_rendered(rendered)?;
            if let Some(function_context) = function_context {
                writer.push(" ]]");
                let start = writer.source.len();
                for cell in function_context.cells().cells() {
                    writer.push("\n");
                    emit_function_context_cell(cell, &names, context, writer)?;
                }
                writer.record(function_context.origin().key(), start, writer.source.len())?;
            }
            emit_requires(sentence, &names, context, writer)?;
            emit_ensures(sentence, &names, context, writer)?;
            emit_term_rule_attributes(sentence, &names, context, writer)?;
            record_claim_binders(sentence, &names, context, sentence_start, writer)?;
            Ok(())
        }
        // A predicate simplification (KF-039): `rule P => Q [simplification]`.
        RuleBodyRef::Predicate(body) => {
            writer.push("rule ");
            let mut rendered = super::term::render_predicate(body.lhs(), context, &names, false)?;
            rendered.push(" => ");
            rendered.append(super::term::render_predicate(
                body.rhs(),
                context,
                &names,
                false,
            )?);
            writer.append_rendered(rendered.finish(body.origin().key(), 0))?;
            emit_requires(sentence, &names, context, writer)?;
            emit_term_rule_attributes(sentence, &names, context, writer)?;
            Ok(())
        }
    }
}

/// Emits the cell clauses of a configuration rule or context, grouping the
/// cells of a repeated ancestor inside it.
fn emit_configuration_clauses(
    body: &krs_ir::FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let mut emitted_repeated = BTreeSet::new();
    for (index, clause) in body.clauses().iter().enumerate() {
        if let ConfigurationClause::Instances(instances) = clause {
            writer.push("\n");
            emit_instances_clause(instances, index, names, context, 4, writer)?;
            continue;
        }
        let Some(ancestor) = context.repeated_ancestor(clause.cell()) else {
            writer.push("\n");
            emit_clause_item(clause, names, context, 4, writer)?;
            continue;
        };
        if !emitted_repeated.insert(ancestor.clone()) {
            continue;
        }
        writer.push("\n    <");
        writer.push(context.cell_name(ancestor)?);
        writer.push(">");
        for nested in body
            .clauses()
            .iter()
            .filter(|candidate| context.repeated_ancestor(candidate.cell()) == Some(ancestor))
        {
            writer.push("\n");
            emit_clause_item(nested, names, context, 8, writer)?;
        }
        writer.push("\n        ...\n    </");
        writer.push(context.cell_name(ancestor)?);
        writer.push(">");
    }
    Ok(())
}

/// Emits one exactly-once or optional clause.
fn emit_clause_item(
    clause: &ConfigurationClause<SymbolId, DefinitionTerm>,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    match clause {
        ConfigurationClause::Fixed(clause) => {
            emit_cell_clause(clause, names, context, indent, writer)
        }
        ConfigurationClause::Optional(clause) => {
            emit_optional_clause(clause, names, context, indent, writer)
        }
        ConfigurationClause::Instances(_) => Err(EmitError::InvalidReference(
            "a collection clause is emitted on its own".into(),
        )),
    }
}

/// Emits an optional (`?`) cell (KF-023): read or updated in place,
/// `(.Bag => <c> V </c>)` when created, `(<c> V </c> => .Bag)` when deleted.
fn emit_optional_clause(
    clause: &krs_ir::OptionalCellClause<SymbolId, DefinitionTerm>,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let whole = clause.kind() == krs_ir::CellClauseKind::Whole;
    match (clause.before(), clause.after()) {
        (krs_ir::Presence::Present { term }, after) => {
            let post = match after {
                None => Some(CellPost::Preserve),
                Some(krs_ir::Presence::Present { term }) => {
                    Some(CellPost::Replace { term: term.clone() })
                }
                Some(krs_ir::Presence::Absent) => None,
            };
            if let Some(post) = post {
                let fixed = krs_ir::FixedCellClause::new(
                    clause.origin().clone(),
                    clause.cell().clone(),
                    term.clone(),
                    post,
                    clause.frame().clone(),
                )
                .with_kind(clause.kind());
                return emit_cell_clause(&fixed, names, context, indent, writer);
            }
            writer.push(&" ".repeat(indent));
            writer.push("(");
            emit_cell_image(
                clause.cell(),
                whole,
                term,
                clause.frame(),
                names,
                context,
                writer,
            )?;
            writer.push(" => .Bag)");
        }
        (krs_ir::Presence::Absent, Some(krs_ir::Presence::Present { term })) => {
            writer.push(&" ".repeat(indent));
            writer.push("(.Bag => ");
            emit_cell_image(
                clause.cell(),
                whole,
                term,
                &CellContentFrame::Exact,
                names,
                context,
                writer,
            )?;
            writer.push(")");
        }
        (krs_ir::Presence::Absent, _) => {
            return Err(EmitError::InvalidReference(
                "an absent optional cell is matched only by creating it".into(),
            ));
        }
    }
    writer.record(clause.origin().key(), start, writer.source.len())?;
    Ok(())
}

/// One side of a cell: `<c> T [frame] </c>`, or a whole group term.
fn emit_cell_image(
    cell: &SymbolId,
    whole: bool,
    term: &DefinitionTerm,
    frame: &CellContentFrame,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if whole {
        let mut rendered = render_term(term, context, names, false)?;
        if let DefinitionTermKind::Variable { variable } = term.kind()
            && variable.kind() == krs_ir::SemanticIdKind::Wildcard
        {
            rendered.text.push(':');
            rendered.text.push_str(&context.sort_name_ref(term.sort())?);
        }
        return writer.append_rendered(rendered);
    }
    let name = context.cell_name(cell)?;
    writer.push("<");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_term(term, context, names, false)?)?;
    emit_single_frame(frame, names, writer)?;
    writer.push(" </");
    writer.push(name);
    writer.push(">");
    Ok(())
}

/// Emits a collection (`*`) clause (KF-023): matched instances in place,
/// `(<c> .. </c> => .Bag)` for a removed one, `(.Bag => <c> .. </c>)` for a
/// new one. An open Set or Map entry leaves the parent cell to K; an exact
/// entry, and a List entry, is written inside its parent cell, and a List
/// entry's back instances follow the other instances, which a variable
/// names.
fn emit_instances_clause(
    clause: &krs_ir::InstancesClause<SymbolId, DefinitionTerm>,
    index: usize,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    // One emitted item: an instance, `...`, or the rest variable.
    enum Item<'a> {
        Instance(&'a krs_ir::InstanceClause<SymbolId, DefinitionTerm>),
        Dots,
        Rest,
    }
    let start = writer.source.len();
    let list = clause.ordering() == krs_ir::InstanceOrdering::List;
    let wrapped = list || !clause.is_open();
    let item_indent = if wrapped { indent + 4 } else { indent };
    let parent = if wrapped {
        let parent = context.parent_cell(clause.cell()).ok_or_else(|| {
            EmitError::InvalidReference(format!(
                "collection {} has no parent cell to write it in",
                clause.cell()
            ))
        })?;
        let name = context.cell_name(parent)?;
        writer.push(&" ".repeat(indent));
        writer.push("<");
        writer.push(name);
        writer.push(">");
        Some(name)
    } else {
        None
    };
    // The items in order: front instances, the other instances (`...`, or
    // a variable when back instances follow them), back instances.
    let mut items = clause
        .front()
        .iter()
        .map(Item::Instance)
        .collect::<Vec<_>>();
    if clause.is_open() {
        if !clause.back().is_empty() {
            items.push(Item::Rest);
        } else if wrapped {
            items.push(Item::Dots);
        }
    }
    items.extend(clause.back().iter().map(Item::Instance));
    for (position, item) in items.into_iter().enumerate() {
        if wrapped || position > 0 {
            writer.push("\n");
        }
        match item {
            Item::Instance(instance) => {
                emit_instance(instance, clause.cell(), names, context, item_indent, writer)?;
            }
            Item::Dots => {
                writer.push(&" ".repeat(item_indent));
                writer.push("...");
            }
            Item::Rest => {
                writer.push(&" ".repeat(item_indent));
                writer.push(&format!("_Instances{index}:Bag"));
            }
        }
    }
    if let Some(name) = parent {
        writer.push("\n");
        writer.push(&" ".repeat(indent));
        writer.push("</");
        writer.push(name);
        writer.push(">");
    }
    writer.record(clause.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_instance(
    instance: &krs_ir::InstanceClause<SymbolId, DefinitionTerm>,
    cell: &SymbolId,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(cell)?;
    // K's cell grammar has no `<c> ... </c>`: an instance that names no
    // child spells its open contents `.Bag ...`, which Java K reads as a
    // pattern over any instance and, on creation, as all-default children.
    let close = |writer: &mut Writer, open: bool, empty: bool| {
        if open {
            writer.push("\n");
            writer.push(&" ".repeat(indent + 4));
            writer.push(if empty { ".Bag ..." } else { "..." });
        }
        writer.push("\n");
        writer.push(&" ".repeat(indent));
        writer.push("</");
        writer.push(name);
        writer.push(">");
    };
    match instance {
        krs_ir::InstanceClause::Kept { children, open, .. } => {
            writer.push(&" ".repeat(indent));
            writer.push("<");
            writer.push(name);
            writer.push(">");
            for child in children {
                writer.push("\n");
                emit_cell_clause(child, names, context, indent + 4, writer)?;
            }
            close(writer, *open, children.is_empty());
        }
        krs_ir::InstanceClause::Removed { children, open, .. }
        | krs_ir::InstanceClause::Created {
            children,
            defaults: open,
            ..
        } => {
            let created = matches!(instance, krs_ir::InstanceClause::Created { .. });
            writer.push(&" ".repeat(indent));
            writer.push(if created { "(.Bag => <" } else { "(<" });
            writer.push(name);
            writer.push(">");
            for child in children {
                writer.push("\n");
                let child_start = writer.source.len();
                writer.push(&" ".repeat(indent + 4));
                emit_cell_image(
                    child.cell(),
                    child.kind() == krs_ir::CellClauseKind::Whole,
                    child.term(),
                    child.frame(),
                    names,
                    context,
                    writer,
                )?;
                writer.record(child.origin().key(), child_start, writer.source.len())?;
            }
            close(writer, *open, children.is_empty());
            writer.push(if created { ")" } else { " => .Bag)" });
        }
    }
    writer.record(instance.origin().key(), start, writer.source.len())?;
    Ok(())
}

/// Emits a context (KF-021): `context [label]: <pattern> requires <cond>
/// [result(S)]`. The pattern is term-shaped (K completes it to the
/// computation cell) or a configuration pattern, and holds the hole `HOLE`
/// and at most one rewrite of it.
fn emit_context(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let names = context.naming.rule(sentence);
    let start = writer.source.len();
    writer.push("context");
    if let Some(step) = sentence.evaluation() {
        writer.record(step.origin().key(), start, writer.source.len())?;
    }
    writer.push(" [");
    emit_label(sentence.label(), writer);
    writer.push("]:");
    match sentence.relational_body() {
        RuleBodyRef::Configuration { body, .. } => {
            emit_configuration_clauses(body, &names, context, writer)?;
        }
        RuleBodyRef::Term(body) => {
            writer.push(" ");
            let local = body.local_term().unwrap_or_else(|| body.from());
            writer.append_rendered(render_term(local, context, &names, false)?)?;
        }
        RuleBodyRef::Predicate(_) => {
            return Err(EmitError::UnsupportedShape {
                node: "context",
                detail: "a context's body is a term or a configuration pattern".to_owned(),
            });
        }
    }
    emit_requires(sentence, &names, context, writer)?;
    if let Some(result) = sentence.evaluation().and_then(|step| step.result()) {
        writer.push("\n    [result(");
        let start = writer.source.len();
        writer.push(&context.sort_name_ref(result.sort())?);
        writer.record(result.origin().key(), start, writer.source.len())?;
        writer.push(")]");
    }
    Ok(())
}

fn emit_term_rule_attributes(
    sentence: &RuleSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
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
    // `heat`/`cool` and `result(S)` (KF-014), in the source key order (X13).
    if let Some(step) = sentence.evaluation() {
        let start = writer.source.len();
        writer.push(step.kind().as_str());
        writer.record(step.origin().key(), start, writer.source.len())?;
        writer.push(", ");
        if let Some(result) = step.result() {
            writer.push("result(");
            let start = writer.source.len();
            writer.push(&context.sort_name_ref(result.sort())?);
            writer.record(result.origin().key(), start, writer.source.len())?;
            writer.push("), ");
        }
    }
    if let Some(anywhere) = sentence.anywhere() {
        let start = writer.source.len();
        writer.push("anywhere");
        writer.record(anywhere.key(), start, writer.source.len())?;
        writer.push(", ");
    }
    if let Some(restriction) = sentence.restriction() {
        emit_match_restriction(restriction, names, writer)?;
    }
    if let Some(unbound) = sentence.unbound_variables() {
        emit_unbound_variables(unbound, names, writer)?;
    }
    writer.push("label(");
    emit_label(sentence.label(), writer);
    writer.push(")]");
    Ok(())
}

/// Emits `concrete`, `symbolic`, and `smt-lemma` (KF-043), each followed by
/// `, `; listed binders use the sentence's K variable names.
fn emit_match_restriction(
    restriction: &krs_ir_levels::IrMatchRestriction,
    names: &SentenceVariables,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (key, attribute) in [
        (restriction.concrete(), "concrete"),
        (restriction.symbolic(), "symbolic"),
    ] {
        let Some(key) = key else {
            continue;
        };
        let start = writer.source.len();
        writer.push(attribute);
        if !key.is_bare() {
            writer.push("(");
            for (index, variable) in key.variables().iter().enumerate() {
                if index != 0 {
                    writer.push(", ");
                }
                let name = names.name(variable.id()).ok_or_else(|| {
                    EmitError::InvalidReference(format!(
                        "{attribute} binder {:?} is not named in its sentence",
                        variable.id().as_str()
                    ))
                })?;
                let variable_start = writer.source.len();
                writer.push(name);
                writer.record(variable.origin().key(), variable_start, writer.source.len())?;
            }
            writer.push(")");
        }
        writer.record(key.origin().key(), start, writer.source.len())?;
        writer.push(", ");
    }
    if let Some(origin) = restriction.smt_lemma() {
        let start = writer.source.len();
        writer.push("smt-lemma");
        writer.record(origin.key(), start, writer.source.len())?;
        writer.push(", ");
    }
    Ok(())
}

/// Emits `unboundVariables(X, _)` (KF-046) followed by `, `; named entries
/// use the sentence's K variable names and `_` stays `_`.
fn emit_unbound_variables(
    unbound: &krs_ir_levels::IrUnboundVariables,
    names: &SentenceVariables,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    writer.push("unboundVariables(");
    for (index, variable) in unbound.variables().iter().enumerate() {
        if index != 0 {
            writer.push(", ");
        }
        let name = match variable.id() {
            None => "_",
            Some(id) => names.name(id).ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "unbound variable {:?} is not named in its sentence",
                    id.as_str()
                ))
            })?,
        };
        let variable_start = writer.source.len();
        writer.push(name);
        writer.record(variable.origin().key(), variable_start, writer.source.len())?;
    }
    writer.push(")");
    writer.record(unbound.origin().key(), start, writer.source.len())?;
    writer.push(", ");
    Ok(())
}

fn record_claim_binders(
    sentence: &RuleSentence,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    sentence_start: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let universals = sentence
        .claim()
        .map_or(&[][..], krs_ir_levels::DefinitionClaim::universals);
    for binder in universals
        .iter()
        .chain(sentence.existentials())
        .chain(sentence.fresh())
    {
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
    // The `hole = x` binder maps to the first `HOLE` of a heat or cool rule (KF-014).
    if let Some(step) = sentence.evaluation() {
        let start = sentence_start
            + first_variable_occurrence(&writer.source[sentence_start..], "HOLE").ok_or_else(
                || {
                    EmitError::InvalidReference(format!(
                        "hole {:?} has no rendered occurrence",
                        step.hole().as_str()
                    ))
                },
            )?;
        writer.record(step.hole_origin().key(), start, start + "HOLE".len())?;
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
    let Some(ensures) = sentence.ensures() else {
        return Ok(());
    };
    writer.push("\n    ensures ");
    emit_condition(ensures, names, context, writer)
}

/// Writes one `requires` or `ensures` condition: an object Bool term, or a
/// matching-logic predicate (KF-039).
fn emit_condition(
    condition: &krs_ir_levels::DefinitionCondition,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    match condition {
        krs_ir_levels::IrCondition::Bool(condition) => {
            writer.append_rendered(render_term(condition.term(), context, names, false)?)?;
            writer.record(condition.origin().key(), start, writer.source.len())?;
        }
        krs_ir_levels::IrCondition::Predicate(predicate) => {
            writer.append_rendered(super::term::render_predicate(
                predicate, context, names, false,
            )?)?;
        }
    }
    Ok(())
}

fn emit_rule_attributes(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let mut attributes = Vec::<(
        &str,
        Option<String>,
        Option<&krs_ir::NodeOrigin>,
        Option<&krs_ir::NodeOrigin>,
    )>::new();
    if let Some(priority) = sentence.priority() {
        attributes.push((
            "priority",
            Some(priority.value().to_string()),
            Some(priority.origin()),
            None,
        ));
    }
    // `heat`/`cool` and `result(S)` (KF-014), in the source key order (X13).
    if let Some(step) = sentence.evaluation() {
        attributes.push((step.kind().as_str(), None, Some(step.origin()), None));
        if let Some(result) = step.result() {
            attributes.push((
                "result",
                Some(context.sort_name_ref(result.sort())?.into_owned()),
                None,
                Some(result.origin()),
            ));
        }
    }
    if let Some(simplification) = sentence.simplification() {
        attributes.push((
            "simplification",
            simplification
                .priority()
                .map(|priority| priority.value().to_string()),
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
        if let Some(origin) = claim.trusted_origin() {
            attributes.push(("trusted", None, Some(origin), None));
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
            writer.push(&value);
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
        emit_condition(condition, names, context, writer)?;
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
    if clause.kind() == krs_ir::CellClauseKind::Whole {
        // A whole group cell is a term of its generated cell sort, written
        // bare (KF-016): `F:FrameCell` or `(_Gen0:FrameCell => F:FrameCell)`.
        writer.push(&" ".repeat(indent));
        match clause.after() {
            // A single-body clause (KF-011) writes its rewrites in place.
            CellPost::Preserve | CellPost::Local => {
                writer.append_rendered(render_term(clause.before(), context, names, false)?)?;
            }
            CellPost::Replace { term } => {
                writer.push("(");
                let mut before = render_term(clause.before(), context, names, false)?;
                if let DefinitionTermKind::Variable { variable } = clause.before().kind()
                    && variable.kind() == krs_ir::SemanticIdKind::Wildcard
                {
                    // A bare `_` beside the cells gives K no sort to infer;
                    // name the generated cell sort: `(_:FrameCell => F:FrameCell)`.
                    before.text.push(':');
                    before
                        .text
                        .push_str(&context.sort_name_ref(clause.before().sort())?);
                }
                writer.append_rendered(before)?;
                writer.push(" => ");
                writer.append_rendered(render_term(term, context, names, false)?)?;
                writer.push(")");
            }
        }
        writer.record(clause.origin().key(), start, writer.source.len())?;
        return Ok(());
    }
    let name = context.cell_name(clause.cell())?;
    writer.push(&" ".repeat(indent));
    writer.push("<");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_term(clause.before(), context, names, false)?)?;
    match clause.after() {
        // A single-body clause (KF-011) is K's local form: the rewrites sit
        // inside the cell, framed once, `<k> (S => .K) ... </k>`.
        CellPost::Preserve | CellPost::Local => emit_single_frame(clause.frame(), names, writer)?,
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
                | CellContentFrame::MapRemainder { binding: None, .. }
                | CellContentFrame::ListRemainder { .. } => {}
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
        CellContentFrame::ListRemainder { origin } => {
            let frame_start = writer.source.len();
            writer.push(" ...");
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
    // `result = S`, K's `result(S)` (KF-021).
    if let Some(result) = sentence.result() {
        writer.push("\n    [result(");
        let start = writer.source.len();
        writer.push(&context.sort_name_ref(result.sort())?);
        writer.record(result.origin().key(), start, writer.source.len())?;
        writer.push(")]");
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

/// One cell an equation's function context reads (KF-025):
/// `<bar> B:Int </bar>`, framed like a configuration rule's cell.
fn emit_function_context_cell(
    cell: &FixedCellPattern<SymbolId, DefinitionTerm>,
    names: &SentenceVariables,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(cell.cell())?;
    writer.push("    <");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_term(cell.pattern(), context, names, false)?)?;
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
