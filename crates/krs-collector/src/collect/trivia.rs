//! Validation of comment trivia inside the DSL macro bodies of an authored source.

use krs_syntax::{
    parse_cells_expression_source_with_trivia, parse_cells_pattern_source_with_trivia,
    parse_map_expression_source_with_trivia, parse_map_pattern_source_with_trivia,
    parse_rule_block_source_with_trivia,
    surface::{FunctionMacro, Invocation, InvocationKind},
};

use super::invocation::source_syntax_at;
use super::provenance::line_index_error;
use crate::{CollectionError, CollectionErrorKind};
use krs_ir::LineIndex;

/// Validates the DSL bodies reached through Rust syntax in source order and reports the first error.
/// Opaque token calls carry no syntax delimiter and are not checked.
pub(super) fn validate_dsl_trivia(
    invocations: &[Invocation<'_>],
    source: &str,
    line_index: &LineIndex,
) -> Result<(), CollectionError> {
    let mut bodies = invocations
        .iter()
        .filter_map(|invocation| match &invocation.kind {
            InvocationKind::Function {
                entry,
                delimiter: Some(delimiter),
                ..
            } => Some((invocation.call_site.start(), *entry, *delimiter)),
            _ => None,
        })
        .collect::<Vec<_>>();
    bodies.sort_by_key(|(start, _, _)| (start.line, start.column));
    for (_, entry, delimiter) in bodies {
        match entry {
            FunctionMacro::Rules => {
                let body = macro_body_source(source, line_index, delimiter)?;
                parse_rule_block_source_with_trivia(body.source)
                    .map_err(|error| source_syntax_at(error, body.byte_offset))?;
            }
            FunctionMacro::Cells => {
                validate_cells_trivia(macro_body_source(source, line_index, delimiter)?)?;
            }
            FunctionMacro::Map => {
                validate_map_trivia(macro_body_source(source, line_index, delimiter)?)?;
            }
            _ => {}
        }
    }
    Ok(())
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
    delimiter: &syn::MacroDelimiter,
) -> Result<MacroBody<'source>, CollectionError> {
    let start = delimiter.span().open().end();
    let end = delimiter.span().close().start();
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

#[cfg(test)]
mod tests {
    use super::validate_dsl_trivia;
    use krs_ir::LineIndex;
    use krs_syntax::surface::{self, FacadeScope};
    use std::collections::BTreeSet;

    fn validate(source: &str) -> Result<(), crate::CollectionError> {
        let syntax = syn::parse_file(source).unwrap();
        let scope = FacadeScope::new(BTreeSet::from(["k".to_owned()]));
        validate_dsl_trivia(
            &surface::invocations(&syntax, &scope),
            source,
            &LineIndex::new(source),
        )
    }

    #[test]
    fn macro_tokens_and_attribute_arguments_are_not_trivia_checked() {
        validate(
            r"other! { k::rules! { invalid /* opaque */ } }
k::id!(k::rules! { invalid /* opaque */ });
#[k::function(k::rules! { invalid /* argument */ })]
fn fixture() {}
",
        )
        .unwrap();
    }

    #[test]
    fn attributed_rust_bodies_report_the_first_exact_comment_range() {
        let source = r"#[k::function]
fn first() { let _ = k::cells! { k: KCell(value /* first */, ..tail), ..state }; }
fn second() { let _ = k::map! { name /* second */ -> value, rest @ .. }; }
";
        let error = validate(source).unwrap_err();
        let start = source.find("/* first */").unwrap();
        let end = start + "/* first */".len();
        assert!(error.detail().contains(&format!("bytes {start}..{end}")));
        assert!(error.detail().contains("cells!"));
    }

    #[test]
    fn invalid_facade_attributes_do_not_hide_rust_body_trivia() {
        for attributes in [
            "#[derive(Clone)] #[k::function]",
            "#[k::unknown]",
            "#[k::rules]",
            "#[k::function = \"wrong\"]",
        ] {
            let source = format!(
                "{attributes}\nfn fixture() {{ let _ = k::cells! {{ k: KCell(value /* body */, ..tail), ..state }}; }}"
            );
            let error = validate(&source).unwrap_err();
            let start = source.find("/* body */").unwrap();
            let end = start + "/* body */".len();
            assert!(error.detail().contains(&format!("bytes {start}..{end}")));
        }
    }

    #[test]
    fn inline_module_aliases_apply_to_nested_rust_macros() {
        let source = r"mod nested {
    use k as local;
    fn fixture() { let _ = local::map! { name /* local */ -> value, rest @ .. }; }
}
";
        let error = validate(source).unwrap_err();
        assert!(error.detail().contains("map!"));
    }

    #[test]
    fn name_value_attribute_expressions_precede_item_macro_trivia() {
        let source = r"#[other = k::cells! { k: KCell(value /* attribute */, ..tail), ..state }]
k::rules! { invalid /* body */ }
";
        let error = validate(source).unwrap_err();
        let start = source.find("/* attribute */").unwrap();
        let end = start + "/* attribute */".len();
        assert!(error.detail().contains(&format!("bytes {start}..{end}")));
        assert!(error.detail().contains("cells!"));
    }
}
