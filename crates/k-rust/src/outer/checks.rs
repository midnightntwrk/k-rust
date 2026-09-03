use std::sync::LazyLock;

use regex::Regex;

use crate::{
    definition::{
        Location,
        attribute_keys::{builtin_key, is_internal_key},
    },
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::Sort,
};

use super::{Attribute, Production, ProductionItem, SourceFile, Span, SyntaxBody};

const BASE_SORTS: &[&str] = &["K", "KResult", "KItem", "KList", "Bag", "KLabel"];
const INVALID_GROUP_MESSAGE: &str = "group(_) attribute expects a comma separated list of groups, each of which consists of a lower case letter followed by any number of alphanumeric or '-' characters.";
static GROUPS: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"\A[ \t\n\x0B\x0C\r]*[a-z][a-zA-Z0-9-]*[ \t\n\x0B\x0C\r]*(,[ \t\n\x0B\x0C\r]*[a-z][a-zA-Z0-9-]*[ \t\n\x0B\x0C\r]*)*\z",
    )
    .unwrap()
});

pub(crate) fn check_user_attributes(file: &SourceFile) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for module in &file.modules {
        check_attribute_list(
            file,
            module.span,
            &module.attributes,
            false,
            &mut diagnostics,
        );
        for sentence in &module.sentences {
            match sentence {
                super::Sentence::Syntax(syntax) => match &syntax.body {
                    SyntaxBody::Sort(attributes) | SyntaxBody::Synonym { attributes, .. } => {
                        check_attribute_list(file, syntax.span, attributes, false, &mut diagnostics)
                    }
                    SyntaxBody::Productions(blocks) => {
                        for production in blocks.iter().flat_map(|block| &block.productions) {
                            check_attribute_list(
                                file,
                                production.span,
                                &production.attributes,
                                true,
                                &mut diagnostics,
                            );
                        }
                    }
                },
                super::Sentence::Lexical(lexical) => check_attribute_list(
                    file,
                    lexical.span,
                    &lexical.attributes,
                    false,
                    &mut diagnostics,
                ),
                super::Sentence::Bubble(bubble) => check_attribute_list(
                    file,
                    bubble.span,
                    &bubble.attributes,
                    false,
                    &mut diagnostics,
                ),
                super::Sentence::Priority(_) | super::Sentence::Associativity(_) => {}
            }
        }
    }
    diagnostics
}

fn check_attribute_list(
    file: &SourceFile,
    span: Span,
    attributes: &[Attribute],
    production: bool,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut internal = attributes
        .iter()
        .filter(|attribute| {
            builtin_key(&attribute.key).is_none() && is_internal_key(&attribute.key)
        })
        .map(|attribute| attribute.key.as_str())
        .collect::<Vec<_>>();
    internal.sort_unstable();
    if !internal.is_empty() {
        diagnostics.push(Diagnostic::error_at_location(
            DiagnosticCode::UnrecognizedAttribute,
            format!("Unrecognized attributes: [{}]", internal.join(", ")),
            file.source.clone(),
            location(span),
        ));
    }

    if production
        && let Some(group) = attributes
            .iter()
            .find(|attribute| attribute.key == "group")
            .and_then(|attribute| attribute.value.as_deref())
        && !GROUPS.is_match(group)
    {
        diagnostics.push(Diagnostic::error_at_location(
            DiagnosticCode::InvalidAttribute,
            INVALID_GROUP_MESSAGE,
            file.source.clone(),
            location(span),
        ));
    }
}

pub fn check_list_declarations(file: &SourceFile) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for module in &file.modules {
        for sentence in &module.sentences {
            let super::Sentence::Syntax(syntax) = sentence else {
                continue;
            };
            let SyntaxBody::Productions(blocks) = &syntax.body else {
                continue;
            };
            for production in blocks.iter().flat_map(|block| &block.productions) {
                check_production(file, &syntax.sort, production, &mut diagnostics);
            }
        }
    }
    diagnostics
}

pub fn check_brackets(file: &SourceFile) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for module in &file.modules {
        for sentence in &module.sentences {
            let super::Sentence::Syntax(syntax) = sentence else {
                continue;
            };
            let SyntaxBody::Productions(blocks) = &syntax.body else {
                continue;
            };
            for production in blocks.iter().flat_map(|block| &block.productions) {
                if !has_attribute(production, "bracket") {
                    continue;
                }
                let nonterminals: Vec<_> = production
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        ProductionItem::NonTerminal { sort, .. } => Some(sort),
                        _ => None,
                    })
                    .collect();
                if nonterminals.as_slice() != [&syntax.sort] {
                    diagnostics.push(Diagnostic::error_at_location(
                        DiagnosticCode::InvalidBracketProduction,
                        "bracket productions should have exactly one non-terminal of the same sort as the production.",
                        file.source.clone(),
                        location(production.span),
                    ));
                }
            }
        }
    }
    diagnostics
}

fn has_attribute(production: &Production, key: &str) -> bool {
    production
        .attributes
        .iter()
        .any(|attribute| attribute.key == key)
}

fn check_production(
    file: &SourceFile,
    list_sort: &Sort,
    production: &Production,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let lists: Vec<_> = production
        .items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::UserList { sort, .. } => Some(sort),
            _ => None,
        })
        .collect();
    if lists.is_empty() {
        return;
    }
    if production.items.len() != 1 {
        diagnostics.push(error(
            file,
            production.span,
            "Inline list declarations are not allowed.",
        ));
        return;
    }
    for element_sort in lists {
        if BASE_SORTS.contains(&list_sort.name.as_str()) {
            diagnostics.push(error(
                file,
                production.span,
                format!("{} can not be extended to be a list sort.", list_sort.name),
            ));
        }
        if element_sort == list_sort {
            diagnostics.push(error(
                file,
                production.span,
                "Circular lists are not allowed.",
            ));
        }
    }
}

fn error(file: &SourceFile, span: Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error_at_location(
        DiagnosticCode::InvalidListDeclaration,
        message,
        file.source.clone(),
        location(span),
    )
}

fn location(span: Span) -> Location {
    Location {
        start_line: span.start.line,
        start_column: span.start.column,
        end_line: span.end.line,
        end_column: span.end.column,
    }
}
