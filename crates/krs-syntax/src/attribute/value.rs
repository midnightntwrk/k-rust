use proc_macro2::TokenStream;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, ExprPath, Ident, Lit, LitBool, LitStr, Path};

use crate::parse::ParseError;
use crate::path::{is_plain_path, unqualified_path_ident};
use crate::{SyntaxError, SyntaxErrorKind};

pub(super) fn parse_empty_tokens(
    tokens: TokenStream,
    attribute: &'static str,
) -> Result<(), SyntaxError> {
    if let Some(first) = tokens.into_iter().next() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnexpectedAttributePayload { attribute },
            first.span(),
        ));
    }
    Ok(())
}

pub(super) fn parse_empty_attribute(
    input: ParseStream<'_>,
    attribute: &'static str,
) -> syn::Result<()> {
    if input.is_empty() {
        Ok(())
    } else {
        Err(SyntaxError::new(
            SyntaxErrorKind::UnexpectedAttributePayload { attribute },
            input.span(),
        )
        .into())
    }
}

pub(super) fn parse_string_value(name: &'static str, value: Expr) -> Result<LitStr, ParseError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Str(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "a Rust string literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unadorned Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

pub(super) fn parse_unqualified_identifier_value(
    name: &'static str,
    value: Expr,
) -> Result<Ident, ParseError> {
    let Expr::Path(ExprPath {
        attrs,
        qself: None,
        path,
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unqualified Rust identifier",
            },
            value.span(),
        )
        .into());
    };
    match unqualified_path_ident(&path) {
        Some(ident) if attrs.is_empty() => Ok(ident.clone()),
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unqualified Rust identifier",
            },
            path.span(),
        )
        .into()),
    }
}

pub(super) fn parse_sort_value(value: Expr) -> Result<Path, ParseError> {
    let Expr::Path(ExprPath {
        attrs,
        qself: None,
        path,
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a Rust trait path",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() || !is_plain_path(&path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a plain Rust trait path without generic arguments",
            },
            path.span(),
        )
        .into());
    }
    Ok(path)
}

pub(super) fn parse_parent_paths_value(value: Expr) -> Result<Vec<Path>, ParseError> {
    let Expr::Array(array) = value else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an array of plain Rust sort paths",
            },
            value.span(),
        )
        .into());
    };
    if !array.attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an unadorned array of plain Rust sort paths",
            },
            array.span(),
        )
        .into());
    }
    array
        .elems
        .into_iter()
        .map(|value| {
            let span = value.span();
            let Expr::Path(ExprPath {
                attrs,
                qself: None,
                path,
            }) = value
            else {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "parents",
                        expected: "an array of plain Rust sort paths",
                    },
                    span,
                )
                .into());
            };
            if !attrs.is_empty() || !is_plain_path(&path) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "parents",
                        expected: "an array of plain Rust sort paths without generic arguments",
                    },
                    path.span(),
                )
                .into());
            }
            Ok(path)
        })
        .collect()
}

pub(super) fn parse_syntax_value(value: Expr) -> Result<LitStr, ParseError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Str(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "syntax",
                expected: "a Rust string literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "syntax",
                expected: "an unadorned Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

pub(super) fn parse_group_value(value: Expr) -> Result<LitStr, ParseError> {
    let literal = parse_string_value("group", value)?;
    let spelling = literal.value();
    let mut characters = spelling.chars();
    let valid = characters
        .next()
        .is_some_and(|character| character == '_' || character.is_ascii_alphabetic())
        && characters.all(|character| character == '_' || character.is_ascii_alphanumeric());
    if !valid {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "group",
                expected: "a nonempty identifier-shaped Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

pub(super) fn parse_rule_label_value(value: Expr) -> Result<LitStr, ParseError> {
    let literal = parse_string_value("label", value)?;
    let spelling = literal.value();
    let valid = spelling
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic())
        && spelling
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'));
    if !valid {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

pub(super) fn parse_avoid_value(value: Expr) -> Result<LitBool, ParseError> {
    parse_true_flag_value("avoid", value)
}

pub(super) fn parse_prefer_value(value: Expr) -> Result<LitBool, ParseError> {
    parse_true_flag_value("prefer", value)
}

/// Parses the reference spelling `key = true` of a parser-preference flag;
/// `false` is rejected because it is not metadata.
fn parse_true_flag_value(name: &'static str, value: Expr) -> Result<LitBool, ParseError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Bool(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "a Rust Boolean literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unadorned Rust Boolean literal",
            },
            literal.span(),
        )
        .into());
    }
    if !literal.value {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "the Rust Boolean literal `true`",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

pub(super) fn parse_format_value(value: Expr) -> Result<LitStr, ParseError> {
    parse_string_value("format", value)
}
