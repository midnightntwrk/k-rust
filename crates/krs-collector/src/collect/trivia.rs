//! Validation of comment trivia inside the DSL macro bodies of an authored source.

use krs_syntax::{
    parse_cells_expression_source_with_trivia, parse_cells_pattern_source_with_trivia,
    parse_map_expression_source_with_trivia, parse_map_pattern_source_with_trivia,
    parse_rule_block_source_with_trivia, surface::FunctionMacro,
};
use syn::visit::Visit;

use super::invocation::source_syntax_at;
use super::provenance::line_index_error;
use crate::facade::AttributeResolver;
use crate::{CollectionError, CollectionErrorKind};
use krs_ir::LineIndex;

struct DslTriviaVisitor<'source, 'file> {
    source: &'source str,
    line_index: &'source LineIndex,
    resolver: AttributeResolver<'file>,
    error: Option<CollectionError>,
}

impl<'ast> Visit<'ast> for DslTriviaVisitor<'_, '_> {
    fn visit_file(&mut self, file: &'ast syn::File) {
        self.resolver = self.resolver.scoped(&file.items);
        syn::visit::visit_file(self, file);
    }

    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        let parent = self.resolver.clone();
        if let Some((_, items)) = &module.content {
            self.resolver = self.resolver.scoped(items);
        }
        syn::visit::visit_item_mod(self, module);
        self.resolver = parent;
    }

    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        if self.error.is_some() {
            return;
        }
        let result = match self.resolver.resolve_macro(&invocation.path) {
            Some(FunctionMacro::Rules) => {
                macro_body_source(self.source, self.line_index, invocation).and_then(|body| {
                    parse_rule_block_source_with_trivia(body.source)
                        .map(|_| ())
                        .map_err(|error| source_syntax_at(error, body.byte_offset))
                })
            }
            Some(FunctionMacro::Cells) => {
                macro_body_source(self.source, self.line_index, invocation)
                    .and_then(validate_cells_trivia)
            }
            Some(FunctionMacro::Map) => macro_body_source(self.source, self.line_index, invocation)
                .and_then(validate_map_trivia),
            _ => Ok(()),
        };
        if let Err(error) = result {
            self.error = Some(error);
            return;
        }
        syn::visit::visit_macro(self, invocation);
    }
}

pub(super) fn validate_dsl_trivia(
    syntax: &syn::File,
    source: &str,
    line_index: &LineIndex,
    resolver: &AttributeResolver<'_>,
) -> Result<(), CollectionError> {
    let mut visitor = DslTriviaVisitor {
        source,
        line_index,
        resolver: resolver.clone(),
        error: None,
    };
    visitor.visit_file(syntax);
    visitor.error.map_or(Ok(()), Err)
}

#[derive(Clone, Copy)]
struct MacroBody<'source> {
    source: &'source str,
    byte_offset: usize,
}

fn validate_cells_trivia(body: MacroBody<'_>) -> Result<(), CollectionError> {
    let expression = parse_cells_expression_source_with_trivia(body.source);
    if expression.is_ok() {
        return Ok(());
    }
    let expression_error = expression.expect_err("the success case returned above");
    if matches!(
        expression_error.kind(),
        krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
    ) {
        return Err(source_syntax_at(expression_error, body.byte_offset));
    }
    match parse_cells_pattern_source_with_trivia(body.source) {
        Err(error)
            if matches!(
                error.kind(),
                krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
            ) =>
        {
            Err(source_syntax_at(error, body.byte_offset))
        }
        Ok(_) | Err(_) => Ok(()),
    }
}

fn validate_map_trivia(body: MacroBody<'_>) -> Result<(), CollectionError> {
    let expression = parse_map_expression_source_with_trivia(body.source);
    if expression.is_ok() {
        return Ok(());
    }
    let expression_error = expression.expect_err("the success case returned above");
    if matches!(
        expression_error.kind(),
        krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
    ) {
        return Err(source_syntax_at(expression_error, body.byte_offset));
    }
    match parse_map_pattern_source_with_trivia(body.source) {
        Err(error)
            if matches!(
                error.kind(),
                krs_syntax::SyntaxErrorKind::UnsupportedDslBlockComment { .. }
            ) =>
        {
            Err(source_syntax_at(error, body.byte_offset))
        }
        Ok(_) | Err(_) => Ok(()),
    }
}

fn macro_body_source<'source>(
    source: &'source str,
    line_index: &LineIndex,
    invocation: &syn::Macro,
) -> Result<MacroBody<'source>, CollectionError> {
    let start = invocation.delimiter.span().open().end();
    let end = invocation.delimiter.span().close().start();
    let start = line_index
        .line_column_to_byte(start)
        .map_err(line_index_error)?;
    let end = line_index
        .line_column_to_byte(end)
        .map_err(line_index_error)?;
    source
        .get(start..end)
        .map(|body| MacroBody {
            source: body,
            byte_offset: start,
        })
        .ok_or_else(|| {
            CollectionError::new(
                CollectionErrorKind::SourcePositionOutOfBounds,
                "a DSL macro delimiter span is outside the exact authored source",
            )
        })
}
