use crate::{
    definition::Location,
    diagnostic::{Diagnostic, DiagnosticCode},
    kast::Sort,
};

use super::{Production, ProductionItem, SourceFile, Span, SyntaxBody};

const BASE_SORTS: &[&str] = &["K", "KResult", "KItem", "KList", "Bag", "KLabel"];

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
