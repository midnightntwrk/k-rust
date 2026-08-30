use std::collections::BTreeMap;

use serde_json::{Value, json};

use crate::{
    definition::{
        Associativity as FlatAssociativity, Attributes, Definition, FlatImport, FlatModule,
        LOCATION_ATTRIBUTE, ProductionItem as FlatProductionItem, SENTENCE_END_OFFSET_ATTRIBUTE,
        SENTENCE_START_OFFSET_ATTRIBUTE, SOURCE_ATTRIBUTE, SOURCE_ID_ATTRIBUTE,
        Sentence as FlatSentence,
    },
    kast::{Label, Sort},
};

use super::{
    Associativity, Attribute, Bubble, BubbleKind, Module, PriorityBlock, Production,
    ProductionItem, Sentence, SourceFile, Span, SyntaxBody, check_brackets,
    check_list_declarations,
};

/// Lower user-authored outer syntax into the flat definition model.
///
/// This is the Rust boundary corresponding to the syntax-shaped portion of
/// Java's `KILtoKORE`. Rule-like sentence bodies intentionally remain bubbles
/// for the inner parser to consume later.
pub fn lower(
    file: &SourceFile,
    main_module: impl Into<String>,
) -> Result<Definition, Vec<crate::diagnostic::Diagnostic>> {
    lower_files(std::slice::from_ref(file), main_module)
}

pub(crate) fn lower_files(
    files: &[SourceFile],
    main_module: impl Into<String>,
) -> Result<Definition, Vec<crate::diagnostic::Diagnostic>> {
    let mut diagnostics = Vec::new();
    for file in files {
        diagnostics.extend(check_list_declarations(file));
        diagnostics.extend(check_brackets(file));
    }
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }

    let tag_index = build_tag_index(files);
    Ok(Definition {
        main_module: main_module.into(),
        modules: files
            .iter()
            .flat_map(|file| {
                file.modules
                    .iter()
                    .map(|module| lower_module(file, module, &tag_index))
            })
            .collect(),
        attributes: Attributes::default(),
    })
}

type TagIndex = BTreeMap<String, Vec<String>>;

fn lower_module(file: &SourceFile, module: &Module, tag_index: &TagIndex) -> FlatModule {
    let mut local_sentences = Vec::new();
    for sentence in &module.sentences {
        lower_sentence(file, module, sentence, tag_index, &mut local_sentences);
    }

    let mut temporary_cell_sorts = Vec::new();
    for sentence in &local_sentences {
        let FlatSentence::Production { items, .. } = sentence else {
            continue;
        };
        for item in items {
            let FlatProductionItem::NonTerminal { sort, .. } = item else {
                continue;
            };
            if (sort.name.ends_with("Cell") || sort.name.ends_with("CellFragment"))
                && !temporary_cell_sorts.contains(sort)
            {
                temporary_cell_sorts.push(sort.clone());
            }
        }
    }
    for sort in temporary_cell_sorts {
        local_sentences.push(FlatSentence::SyntaxSort {
            parameters: Vec::new(),
            sort,
            attributes: attrs_with_entry(
                Attributes::default(),
                "temporary-cell-sort-decl",
                json!(""),
            ),
        });
    }

    FlatModule {
        name: module.name.clone(),
        imports: module
            .imports
            .iter()
            .map(|import| FlatImport {
                name: import.module.clone(),
                public: import.public,
            })
            .collect(),
        local_sentences,
        attributes: source_attributes(file, module.span, &module.attributes),
    }
}

fn lower_sentence(
    file: &SourceFile,
    module: &Module,
    sentence: &Sentence,
    tag_index: &TagIndex,
    output: &mut Vec<FlatSentence>,
) {
    match sentence {
        Sentence::Syntax(syntax) => match &syntax.body {
            SyntaxBody::Sort(attributes) => output.push(FlatSentence::SyntaxSort {
                parameters: syntax.parameters.clone(),
                sort: syntax.sort.clone(),
                attributes: sentence_source_attributes(file, syntax.span, attributes),
            }),
            SyntaxBody::Synonym {
                old_sort,
                attributes,
            } => output.push(FlatSentence::SortSynonym {
                new_sort: syntax.sort.clone(),
                old_sort: old_sort.clone(),
                attributes: sentence_source_attributes(file, syntax.span, attributes),
            }),
            SyntaxBody::Productions(blocks) => {
                if blocks.len() > 1 {
                    output.push(FlatSentence::SyntaxPriority {
                        priorities: blocks
                            .iter()
                            .map(|block| block_tags(module, &syntax.sort, block))
                            .collect(),
                        attributes: sentence_source_attributes(file, syntax.span, &[]),
                    });
                }
                for block in blocks {
                    let tags = block_tags(module, &syntax.sort, block);
                    if block.associativity != Associativity::Unspecified {
                        output.push(FlatSentence::SyntaxAssociativity {
                            associativity: lower_associativity(block.associativity),
                            tags,
                            attributes: sentence_source_attributes(file, block.span, &[]),
                        });
                    }
                    for production in &block.productions {
                        lower_production(
                            file,
                            module,
                            &syntax.parameters,
                            &syntax.sort,
                            production,
                            output,
                        );
                    }
                }
            }
        },
        Sentence::Priority(priority) => output.push(FlatSentence::SyntaxPriority {
            priorities: priority
                .groups
                .iter()
                .map(|group| resolve_tags(group, tag_index))
                .collect(),
            attributes: sentence_source_attributes(file, priority.span, &[]),
        }),
        Sentence::Associativity(associativity) => {
            output.push(FlatSentence::SyntaxAssociativity {
                associativity: lower_associativity(associativity.associativity),
                tags: resolve_tags(&associativity.tags, tag_index),
                attributes: sentence_source_attributes(file, associativity.span, &[]),
            });
        }
        Sentence::Lexical(lexical) => output.push(FlatSentence::SyntaxLexical {
            name: lexical.name.clone(),
            regex: lexical.regex.clone(),
            attributes: sentence_source_attributes(file, lexical.span, &lexical.attributes),
        }),
        Sentence::Bubble(bubble) => output.push(lower_bubble(file, module, bubble)),
    }
}

fn lower_production(
    file: &SourceFile,
    module: &Module,
    parameters: &[Sort],
    result_sort: &Sort,
    production: &Production,
    output: &mut Vec<FlatSentence>,
) {
    if let [
        ProductionItem::UserList {
            sort,
            separator,
            non_empty,
        },
    ] = production.items.as_slice()
    {
        lower_user_list(
            file,
            module,
            parameters,
            result_sort,
            production,
            sort,
            separator,
            *non_empty,
            output,
        );
        return;
    }

    let label = effective_label(module, result_sort, production, false);
    let mut attributes = sentence_source_attributes(file, production.span, &production.attributes);
    if has_attribute(&production.attributes, "bracket") {
        let bracket_label = prefix_label(module, result_sort, production, true);
        attributes.insert("bracketLabel", json!(bracket_label));
    }
    output.push(FlatSentence::Production {
        label: label.map(|name| Label::with_parameters(name, parameters.to_vec())),
        parameters: parameters.to_vec(),
        sort: result_sort.clone(),
        items: production.items.iter().map(lower_item).collect(),
        attributes,
    });

    for (key, associativity) in [
        ("left", FlatAssociativity::Left),
        ("right", FlatAssociativity::Right),
        ("non-assoc", FlatAssociativity::NonAssoc),
    ] {
        if has_attribute(&production.attributes, key)
            && let Some(tag) = effective_label(module, result_sort, production, false)
        {
            output.push(FlatSentence::SyntaxAssociativity {
                associativity,
                tags: vec![tag],
                attributes: sentence_source_attributes(file, production.span, &[]),
            });
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_user_list(
    file: &SourceFile,
    module: &Module,
    parameters: &[Sort],
    result_sort: &Sort,
    production: &Production,
    element_sort: &Sort,
    separator: &str,
    non_empty: bool,
    output: &mut Vec<FlatSentence>,
) {
    let recursive_label = effective_label(module, result_sort, production, false)
        .unwrap_or_else(|| prefix_label(module, result_sort, production, true));
    let mut recursive_attributes =
        sentence_source_attributes(file, production.span, &production.attributes);
    recursive_attributes.insert("userList", json!(if non_empty { "+" } else { "*" }));
    output.push(FlatSentence::Production {
        label: Some(Label::with_parameters(
            recursive_label.clone(),
            parameters.to_vec(),
        )),
        parameters: parameters.to_vec(),
        sort: result_sort.clone(),
        items: vec![
            FlatProductionItem::NonTerminal {
                sort: element_sort.clone(),
                name: None,
            },
            FlatProductionItem::Terminal(separator.to_owned()),
            FlatProductionItem::NonTerminal {
                sort: result_sort.clone(),
                name: None,
            },
        ],
        attributes: recursive_attributes,
    });

    let explicit_terminator = attribute_value(&production.attributes, "terminator-symbol");
    let has_symbol = production
        .attributes
        .iter()
        .any(|attribute| attribute.key == "symbol");
    let terminator = explicit_terminator.map_or_else(
        || {
            format!(
                ".List{{{}}}{}",
                serde_json::to_string(&recursive_label).expect("strings serialize"),
                if has_symbol {
                    String::new()
                } else {
                    format!("_{}", result_sort.name)
                }
            )
        },
        |label| label.replace(' ', ""),
    );
    let unqualified_terminator = explicit_terminator.map_or_else(
        || {
            let list_label = if has_symbol {
                recursive_label.clone()
            } else {
                let raw_label = raw_prefix_label(production).0;
                format!("{raw_label}_{}", module.name)
            };
            format!(
                ".List{{{}}}",
                serde_json::to_string(&list_label).expect("strings serialize")
            )
        },
        |label| label.replace(' ', ""),
    );
    let mut terminator_attributes =
        sentence_source_attributes(file, production.span, &production.attributes);
    for key in ["format", "strict", "terminator-symbol"] {
        terminator_attributes = without_attribute(terminator_attributes, key);
    }
    terminator_attributes.insert("userList", json!(if non_empty { "+" } else { "*" }));
    terminator_attributes.insert("symbol", json!(unqualified_terminator));
    output.push(FlatSentence::Production {
        label: Some(Label::with_parameters(terminator, parameters.to_vec())),
        parameters: parameters.to_vec(),
        sort: result_sort.clone(),
        items: vec![FlatProductionItem::Terminal(format!(
            ".{}",
            result_sort.name
        ))],
        attributes: terminator_attributes,
    });
}

fn lower_item(item: &ProductionItem) -> FlatProductionItem {
    match item {
        ProductionItem::Terminal(terminal) => FlatProductionItem::Terminal(terminal.clone()),
        ProductionItem::Regex(regex) => FlatProductionItem::regex(regex.clone()),
        ProductionItem::NonTerminal { name, sort } => FlatProductionItem::NonTerminal {
            sort: sort.clone(),
            name: name.clone(),
        },
        ProductionItem::UserList { .. } => unreachable!("list checks reject inline lists"),
    }
}

fn lower_bubble(file: &SourceFile, module: &Module, bubble: &Bubble) -> FlatSentence {
    let mut attributes = sentence_source_attributes(file, bubble.span, &bubble.attributes);
    attributes.insert(
        "contentStartOffset",
        json!(bubble.content_span.start.offset),
    );
    attributes.insert("contentStartLine", json!(bubble.content_span.start.line));
    attributes.insert(
        "contentStartColumn",
        json!(bubble.content_span.start.column),
    );
    if let Some(label) = &bubble.label {
        attributes.insert(
            "label",
            json!(if bubble.kind == BubbleKind::ContextAlias {
                label.clone()
            } else {
                format!("{}.{}", module.name, label)
            }),
        );
    }
    FlatSentence::Bubble {
        sentence_type: match bubble.kind {
            BubbleKind::Rule => "rule",
            BubbleKind::Claim => "claim",
            BubbleKind::Context => "context",
            BubbleKind::ContextAlias => "alias",
            BubbleKind::Configuration => "config",
        }
        .into(),
        contents: bubble.content.clone(),
        attributes,
    }
}

fn block_tags(module: &Module, result_sort: &Sort, block: &PriorityBlock) -> Vec<String> {
    block
        .productions
        .iter()
        .filter_map(|production| {
            effective_label(module, result_sort, production, false).or_else(|| {
                has_attribute(&production.attributes, "bracket")
                    .then(|| prefix_label(module, result_sort, production, true))
            })
        })
        .collect()
}

fn build_tag_index(files: &[SourceFile]) -> TagIndex {
    let mut index = TagIndex::new();
    for module in files.iter().flat_map(|file| &file.modules) {
        for sentence in &module.sentences {
            let Sentence::Syntax(syntax) = sentence else {
                continue;
            };
            let SyntaxBody::Productions(blocks) = &syntax.body else {
                continue;
            };
            for production in blocks.iter().flat_map(|block| &block.productions) {
                let compiled =
                    effective_label(module, &syntax.sort, production, false).or_else(|| {
                        has_attribute(&production.attributes, "bracket")
                            .then(|| prefix_label(module, &syntax.sort, production, true))
                    });
                let Some(compiled) = compiled else {
                    continue;
                };
                if let Some(source) = source_label(production, false).or_else(|| {
                    has_attribute(&production.attributes, "bracket")
                        .then(|| source_label(production, true))
                        .flatten()
                }) {
                    insert_tag(&mut index, source, compiled.clone());
                }
                if let Some(groups) = attribute_value(&production.attributes, "group") {
                    for group in groups
                        .split(',')
                        .map(str::trim)
                        .filter(|group| !group.is_empty())
                    {
                        insert_tag(&mut index, group.to_owned(), compiled.clone());
                    }
                }
            }
        }
    }
    index
}

fn source_label(production: &Production, bracket: bool) -> Option<String> {
    let symbol = attribute_value(&production.attributes, "symbol");
    let declared = symbol
        .filter(|symbol| !symbol.is_empty())
        .or_else(|| attribute_value(&production.attributes, "klabel"));
    let syntactic_subsort = matches!(
        production.items.as_slice(),
        [ProductionItem::NonTerminal { .. }]
    );
    if !bracket
        && declared.is_none()
        && (syntactic_subsort
            || has_attribute(&production.attributes, "token")
            || has_attribute(&production.attributes, "bracket"))
    {
        return None;
    }
    declared
        .map(|label| label.replace(' ', ""))
        .or_else(|| Some(raw_prefix_label(production).0))
}

fn insert_tag(index: &mut TagIndex, source: String, compiled: String) {
    let labels = index.entry(source).or_default();
    if !labels.contains(&compiled) {
        labels.push(compiled);
        labels.sort();
    }
}

fn resolve_tags(tags: &[String], index: &TagIndex) -> Vec<String> {
    tags.iter()
        .flat_map(|tag| index.get(tag).cloned().unwrap_or_else(|| vec![tag.clone()]))
        .collect()
}

fn effective_label(
    module: &Module,
    result_sort: &Sort,
    production: &Production,
    bracket: bool,
) -> Option<String> {
    let symbol = attribute_value(&production.attributes, "symbol");
    let declared = symbol
        .filter(|symbol| !symbol.is_empty())
        .or_else(|| attribute_value(&production.attributes, "klabel"));
    let syntactic_subsort = matches!(
        production.items.as_slice(),
        [ProductionItem::NonTerminal { .. }]
    );
    if !bracket
        && declared.is_none()
        && (syntactic_subsort
            || has_attribute(&production.attributes, "token")
            || has_attribute(&production.attributes, "bracket"))
    {
        return None;
    }
    if let Some(declared) = declared
        && production
            .attributes
            .iter()
            .any(|attribute| attribute.key == "symbol")
    {
        return Some(declared.replace(' ', ""));
    }
    Some(prefix_label(module, result_sort, production, true))
}

fn prefix_label(
    module: &Module,
    result_sort: &Sort,
    production: &Production,
    kore: bool,
) -> String {
    let (mut label, mut sorts) = raw_prefix_label(production);
    if matches!(
        production.items.as_slice(),
        [ProductionItem::UserList { .. }]
    ) {
        sorts.push(result_sort.name.clone());
    }
    if kore {
        label.push('_');
        label.push_str(&module.name);
        label.push('_');
        label.push_str(&result_sort.name);
        for sort in sorts {
            label.push('_');
            label.push_str(&sort);
        }
    }
    label.replace(' ', "")
}

fn raw_prefix_label(production: &Production) -> (String, Vec<String>) {
    let mut label = String::new();
    let mut sorts = Vec::new();
    for item in &production.items {
        match item {
            ProductionItem::Terminal(terminal) => label.push_str(terminal),
            ProductionItem::NonTerminal { sort, .. } => {
                label.push('_');
                sorts.push(sort.name.clone());
            }
            ProductionItem::UserList {
                sort, separator, ..
            } => {
                label.push('_');
                label.push_str(separator);
                label.push('_');
                sorts.push(sort.name.clone());
            }
            ProductionItem::Regex(_) => {}
        }
    }
    (label.replace(' ', ""), sorts)
}

fn lower_associativity(associativity: Associativity) -> FlatAssociativity {
    match associativity {
        Associativity::Left => FlatAssociativity::Left,
        Associativity::Right => FlatAssociativity::Right,
        Associativity::NonAssoc => FlatAssociativity::NonAssoc,
        Associativity::Unspecified => FlatAssociativity::Unspecified,
    }
}

fn source_attributes(file: &SourceFile, span: Span, attributes: &[Attribute]) -> Attributes {
    let mut result = Attributes::default();
    for attribute in attributes {
        result.insert(
            attribute.key.clone(),
            json!(
                attribute
                    .value
                    .as_deref()
                    .map(decode_attribute_value)
                    .unwrap_or_default()
            ),
        );
    }
    result.insert(SOURCE_ATTRIBUTE, json!(file.source));
    result.insert(SOURCE_ID_ATTRIBUTE, json!(file.source_id.0));
    result.insert(
        LOCATION_ATTRIBUTE,
        json!([
            span.start.line,
            span.start.column,
            span.end.line,
            span.end.column
        ]),
    );
    result
}

fn sentence_source_attributes(
    file: &SourceFile,
    span: Span,
    attributes: &[Attribute],
) -> Attributes {
    let mut result = source_attributes(file, span, attributes);
    result.insert(SENTENCE_START_OFFSET_ATTRIBUTE, json!(span.start.offset));
    result.insert(SENTENCE_END_OFFSET_ATTRIBUTE, json!(span.end.offset));
    result
}

fn decode_attribute_value(value: &str) -> String {
    if value.starts_with('"') && value.ends_with('"') {
        serde_json::from_str(value).unwrap_or_else(|_| value.to_owned())
    } else {
        value.to_owned()
    }
}

fn has_attribute(attributes: &[Attribute], key: &str) -> bool {
    attributes.iter().any(|attribute| attribute.key == key)
}

fn attribute_value<'a>(attributes: &'a [Attribute], key: &str) -> Option<&'a str> {
    attributes
        .iter()
        .find(|attribute| attribute.key == key)
        .and_then(|attribute| attribute.value.as_deref())
}

fn attrs_with_entry(mut attributes: Attributes, key: &str, value: Value) -> Attributes {
    attributes.insert(key, value);
    attributes
}

fn without_attribute(attributes: Attributes, key: &str) -> Attributes {
    Attributes::new(
        attributes
            .entries()
            .iter()
            .filter(|(attribute, _)| attribute.as_str() != key)
            .map(|(attribute, value)| (attribute.clone(), value.clone()))
            .collect(),
    )
}
