//! `k::equations!`: a table of labelled equations of one function.
//!
//! ```ignore
//! k::equations! {
//!     for R8;
//!     use Operand::*;
//!     use Register::*;
//!     r8_b: 0 => Reg(B);
//!     r8_hl_indirect: 6 => HlIndirect;
//! }
//! ```
//!
//! Each row is the equation `fn label(R8(args): R8) -> R8 { result }`, whose
//! sort is the result sort of the header's function. Rows are unordered and
//! named by their labels, never by their position. The arguments are one
//! pattern for a one-argument function, or a parenthesized list.

use std::collections::BTreeMap;

use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote};
use syn::ext::IdentExt;
use syn::parse::{ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemFn, ItemUse, Pat, Path, Token};

use super::block::RuleClauseLayout;
use super::item::RuleItem;
use super::pattern::NegativeLiteralSpans;
use crate::parse::{KrsSyntax, ParseError, structured};
use crate::surface::{AttributeMacro, helper_entry};
use crate::{EquationAttribute, ProvenanceAnchor, SyntaxError, SyntaxErrorKind, TokenRange};

/// K's default rule priority, which an equation without `owise` or
/// `priority = N` has.
const DEFAULT_PRIORITY: u32 = 50;

/// One `label: args => result;` row of a `k::equations!` table.
#[derive(Clone, Debug)]
pub struct EquationRow {
    rule: RuleItem,
    equation: EquationAttribute,
    equation_keys: Option<TokenStream>,
    arguments: Group,
    arity: usize,
    source_range: TokenRange,
    layout: RuleClauseLayout,
}

impl EquationRow {
    /// The row's equation, as the ordinary equation fn it stands for.
    #[must_use]
    pub const fn rule(&self) -> &RuleItem {
        &self.rule
    }

    /// The row's `#[k::equation(..)]` keys; empty when it has none.
    #[must_use]
    pub const fn equation(&self) -> &EquationAttribute {
        &self.equation
    }

    /// The authored keys of the row's `#[k::equation(..)]`, when it has one.
    #[must_use]
    pub const fn equation_keys(&self) -> Option<&TokenStream> {
        self.equation_keys.as_ref()
    }

    /// The row's label, the equation's name.
    #[must_use]
    pub fn label(&self) -> &Ident {
        &self.rule.item().sig.ident
    }

    /// The argument list, authored or wrapping the one authored pattern.
    #[must_use]
    pub const fn arguments(&self) -> &Group {
        &self.arguments
    }

    /// The row from its first attribute through its `;`.
    #[must_use]
    pub const fn source_range(&self) -> TokenRange {
        self.source_range
    }

    /// The authored label, arguments, and result; a row has no conditions.
    #[must_use]
    pub const fn layout(&self) -> RuleClauseLayout {
        self.layout
    }

    /// The number of arguments the row applies the function to.
    #[must_use]
    pub const fn arity(&self) -> usize {
        self.arity
    }

    /// The row's anchors: the equation's and its `#[k::equation]` keys'.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.rule.full_provenance()?;
        anchors.extend(self.equation.provenance()?);
        Ok(anchors)
    }
}

/// A `k::equations!` table: the function, its `use` items, and its rows.
#[derive(Clone, Debug)]
pub struct EquationTable {
    function: Path,
    imports: Vec<ItemUse>,
    rows: Vec<EquationRow>,
}

impl EquationTable {
    /// The function the header names.
    #[must_use]
    pub const fn function(&self) -> &Path {
        &self.function
    }

    /// The table's `use` items, in scope for every row.
    #[must_use]
    pub fn imports(&self) -> &[ItemUse] {
        &self.imports
    }

    /// The rows in authored order, which has no meaning.
    #[must_use]
    pub fn rows(&self) -> &[EquationRow] {
        &self.rows
    }

    fn from_stream(input: ParseStream<'_>) -> Result<Self, ParseError> {
        if !input.peek(Token![for]) {
            return Err(table_error(
                "a `k::equations!` table starts with `for Function;`, naming the function its rows define",
                input.span(),
            )
            .into());
        }
        input.parse::<Token![for]>()?;
        let function: Path = input.parse()?;
        if !crate::path::is_plain_path(&function) {
            return Err(table_error(
                "the header names a non-parametric `#[k::function]` by a plain path",
                function.span(),
            )
            .into());
        }
        input.parse::<Token![;]>()?;
        let mut imports = Vec::new();
        while input.peek(Token![use]) {
            imports.push(input.parse::<ItemUse>()?);
        }
        let mut rows: Vec<EquationRow> = Vec::new();
        while !input.is_empty() {
            let row = parse_row(input, &function)?;
            if let Some(previous) = rows
                .iter()
                .find(|previous| previous.label().unraw() == row.label().unraw())
            {
                return Err(table_error(
                    &format!(
                        "duplicate row label `{}`: a label names its equation",
                        previous.label().unraw()
                    ),
                    row.label().span(),
                )
                .into());
            }
            rows.push(row);
        }
        if rows.is_empty() {
            return Err(table_error(
                "a `k::equations!` table needs at least one `label: args => result;` row",
                input.span(),
            )
            .into());
        }
        check_rows(&rows)?;
        Ok(Self {
            function,
            imports,
            rows,
        })
    }
}

impl KrsSyntax for EquationTable {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, Self::from_stream)
    }
}

/// Parses a `k::equations!` body together with lossless source trivia.
///
/// # Errors
///
/// Returns the errors of [`EquationTable::parse_tokens`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_equation_table_source_with_trivia(
    source: &str,
) -> Result<(EquationTable, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("k::equations")?;
    Ok((EquationTable::parse_tokens(tokens)?, trivia))
}

fn parse_row(input: ParseStream<'_>, function: &Path) -> Result<EquationRow, ParseError> {
    let row_start = input.cursor().span();
    let attributes = input.call(Attribute::parse_outer)?;
    let label = input.call(Ident::parse_any)?;
    input.parse::<Token![:]>()?;
    let mut tokens = Vec::new();
    while !input.is_empty() && !input.peek(Token![=>]) && !input.peek(Token![;]) {
        tokens.push(input.parse::<TokenTree>()?);
    }
    let arguments = match tokens.as_slice() {
        [] => {
            return Err(table_error(
                "a row applies the function to its arguments before `=>`; a nullary function writes `()`",
                label.span(),
            )
            .into());
        }
        [TokenTree::Group(group)] if group.delimiter() == Delimiter::Parenthesis => group.clone(),
        [.., last] => {
            let mut group = Group::new(
                Delimiter::Parenthesis,
                tokens.iter().cloned().collect::<TokenStream>(),
            );
            group.set_span(last.span());
            group
        }
    };
    let arguments_range = TokenRange::for_tokens(&tokens.iter().cloned().collect::<TokenStream>())?;
    let patterns = argument_patterns(&arguments)?;
    let arity = patterns.len();
    input.parse::<Token![=>]>()?;
    let result: Expr = input.parse()?;
    if input.peek(Token![where]) {
        return Err(table_error(
            "a `k::equations!` row takes no `where` narrowing; declare the binder sorts in a `#[k::equation]` fn",
            input.span(),
        )
        .into());
    }
    let semicolon = input.parse::<Token![;]>()?;
    let layout = RuleClauseLayout {
        label: TokenRange::for_tokens(&label)?,
        pattern: arguments_range,
        result: TokenRange::for_tokens(&result)?,
        conditions: None,
    };

    let RowAttributes {
        equation,
        equation_keys,
        retained,
    } = row_attributes(attributes)?;
    let subject = quote!(#function #arguments);
    let signs = NegativeLiteralSpans::scan(subject.clone());
    let item: ItemFn = syn::parse2(quote! {
        #(#retained)*
        fn #label(#subject: #function) -> #function { #result }
    })?;
    let rule = RuleItem::from_table_item(item, signs)?;
    if rule.function_context().is_some() {
        return Err(table_error(
            "a `k::equations!` row has no function context",
            label.span(),
        )
        .into());
    }
    Ok(EquationRow {
        rule,
        equation: equation.unwrap_or_default(),
        equation_keys,
        arguments,
        arity,
        source_range: TokenRange::new(row_start, semicolon.span),
        layout,
    })
}

/// A row's attributes: its `#[k::equation(..)]` keys, parsed and authored,
/// and the attributes its equation fn keeps (`#[k::requires]`, documentation).
struct RowAttributes {
    equation: Option<EquationAttribute>,
    equation_keys: Option<TokenStream>,
    retained: Vec<Attribute>,
}

fn row_attributes(attributes: Vec<Attribute>) -> Result<RowAttributes, ParseError> {
    let mut row = RowAttributes {
        equation: None,
        equation_keys: None,
        retained: Vec::new(),
    };
    for attribute in attributes {
        match helper_entry(attribute.path()) {
            Some(AttributeMacro::Equation) => {
                if row.equation.is_some() {
                    return Err(table_error(
                        "a row takes one `#[k::equation(..)]`",
                        attribute.span(),
                    )
                    .into());
                }
                let tokens = match &attribute.meta {
                    syn::Meta::List(list) => list.tokens.clone(),
                    _ => TokenStream::new(),
                };
                row.equation = Some(EquationAttribute::parse_tokens(tokens.clone())?);
                row.equation_keys = Some(tokens);
            }
            Some(AttributeMacro::Requires) | None => row.retained.push(attribute),
            Some(entry) => {
                return Err(table_error(
                    &format!(
                        "a `k::equations!` row is an equation; it takes `#[k::equation(..)]` and `#[k::requires(..)]`, not `#[k::{}]`",
                        entry.name()
                    ),
                    attribute.span(),
                )
                .into());
            }
        }
    }
    Ok(row)
}

/// The fail-fast checks between rows: two unguarded rows at one priority
/// with the same literal arguments, and a catch-all row that shares its
/// priority with another row.
fn check_rows(rows: &[EquationRow]) -> Result<(), SyntaxError> {
    let priority = |row: &EquationRow| {
        row.equation
            .equation_priority()
            .map_or(DEFAULT_PRIORITY, |(_, value)| value)
    };
    let mut literal_rows = BTreeMap::<(u32, Vec<String>), &EquationRow>::new();
    for row in rows {
        let patterns = row_patterns(row);
        let unguarded = row.rule.requires().is_none();
        if unguarded && let Some(literals) = literal_tuple(&patterns) {
            if let Some(previous) = literal_rows.get(&(priority(row), literals.clone())) {
                let same = previous
                    .rule
                    .result()
                    .zip(row.rule.result())
                    .is_some_and(|(left, right)| left.spelling() == right.spelling());
                let reason = if same {
                    format!(
                        "rows `{}` and `{}` state the same equation; remove one",
                        previous.label().unraw(),
                        row.label().unraw()
                    )
                } else {
                    format!(
                        "rows `{}` and `{}` give one application two results, so the definition would state that they are equal; equations are unordered, so give the rows different arguments, guards, or priorities",
                        previous.label().unraw(),
                        row.label().unraw()
                    )
                };
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateEquationRow { reason },
                    row.arguments.span(),
                ));
            }
            literal_rows.insert((priority(row), literals), row);
        }
        if unguarded
            && is_catch_all(&patterns)
            && let Some(other) = rows
                .iter()
                .find(|other| !std::ptr::eq(*other, row) && priority(other) == priority(row))
        {
            return Err(SyntaxError::new(
                SyntaxErrorKind::CatchAllEquationRow {
                    reason: format!(
                        "row `{}` matches every application, so it overlaps row `{}` at the same priority; equations are unordered, not first-match, so mark the catch-all `#[k::equation(owise)]`",
                        row.label().unraw(),
                        other.label().unraw()
                    ),
                },
                row.arguments.span(),
            ));
        }
    }
    Ok(())
}

fn row_patterns(row: &EquationRow) -> Vec<Pat> {
    argument_patterns(&row.arguments)
        .map(|patterns| patterns.into_iter().collect())
        .unwrap_or_default()
}

/// The comma-separated argument patterns of a row; each may be `A | B`.
fn argument_patterns(arguments: &Group) -> syn::Result<Punctuated<Pat, Token![,]>> {
    (|input: ParseStream<'_>| {
        Punctuated::<Pat, Token![,]>::parse_terminated_with(input, Pat::parse_multi)
    })
    .parse2(arguments.stream())
}

/// The canonical spelling of every argument when all are literals.
fn literal_tuple(patterns: &[Pat]) -> Option<Vec<String>> {
    patterns
        .iter()
        .map(|pattern| match pattern {
            Pat::Lit(literal) if literal.attrs.is_empty() => Some(match &literal.lit {
                syn::Lit::Int(integer) => canonical_integer(integer.base10_digits()),
                other => other.to_token_stream().to_string(),
            }),
            Pat::Paren(inner) => {
                literal_tuple(std::slice::from_ref(&inner.pat)).and_then(|mut values| values.pop())
            }
            _ => None,
        })
        .collect()
}

fn canonical_integer(digits: &str) -> String {
    let (sign, digits) = digits
        .strip_prefix('-')
        .map_or(("", digits), |rest| ("-", rest));
    let digits = digits.replace('_', "");
    let trimmed = digits.trim_start_matches('0');
    if trimmed.is_empty() {
        "0".to_owned()
    } else {
        format!("{sign}{trimmed}")
    }
}

/// Whether every argument is certainly a wildcard. A bare identifier is not
/// counted: syn reads a unit variant brought in by a `use` item, such as `A`,
/// as an identifier pattern, and only rustc's name resolution tells it from a
/// binder, so this fail-fast check would otherwise reject a table keyed on
/// unit variants.
fn is_catch_all(patterns: &[Pat]) -> bool {
    patterns
        .iter()
        .all(|pattern| matches!(pattern, Pat::Wild(_)))
}

fn table_error(reason: &str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidEquationTable {
            reason: reason.to_owned(),
        },
        span,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> Result<EquationTable, SyntaxError> {
        EquationTable::parse_tokens(source.parse().expect("table tokens"))
    }

    #[test]
    fn rows_are_equations_of_the_header_function() {
        let table = parse(
            "for R8; use Operand::*; use Register::*;
             r8_b: 0 => Reg(B);
             r8_hl: 6 => HlIndirect;
             #[k::requires(int::gt(n, 0))] r8_pos: n => Reg(A);
             #[k::equation(owise)] r8_other: _ => Immediate;",
        )
        .expect("valid table");
        assert_eq!(table.function().segments[0].ident, "R8");
        assert_eq!(table.imports().len(), 2);
        assert_eq!(table.rows().len(), 4);
        assert_eq!(table.rows()[0].label(), "r8_b");
        assert_eq!(table.rows()[0].arity(), 1);
        assert!(table.rows()[2].rule().requires().is_some());
        assert!(table.rows()[3].equation().is_owise());
        assert!(
            table.rows()[0]
                .rule()
                .parameter()
                .term_sort
                .is_function_result()
        );
    }

    #[test]
    fn parenthesized_rows_list_several_arguments() {
        for (source, arity) in [
            ("for Pair; both: (0, -1) => 3; other: (1, x) => x;", 2),
            ("for Zero; none: () => 0;", 0),
            ("for Id; one: (x) => x;", 1),
            ("for Bit; either: 0 | 1 => true;", 1),
        ] {
            let table = parse(source).expect(source);
            assert!(
                table.rows().iter().all(|row| row.arity() == arity),
                "{source}"
            );
        }
    }

    #[test]
    fn table_mistakes_are_reported() {
        for (source, expected) in [
            ("r8_b: 0 => B;", "starts with `for Function;`"),
            ("for R8;", "at least one"),
            ("for R8; a: 0 => B; a: 1 => C;", "duplicate row label `a`"),
            ("for R8; a: 0 => B; b: 0 => C;", "two results"),
            ("for R8; a: 0 => B; b: 00 => B;", "same equation"),
            ("for R8; a: 0 => B; b: _ => C;", "mark the catch-all"),
            ("for R8; a: => B;", "nullary function writes `()`"),
            ("#[k::rule] for R8;", "starts with `for Function;`"),
            ("for R8; #[k::rule] a: 0 => B;", "not `#[k::rule]`"),
            ("for R8; a: x => B where x: Int;", "no `where`"),
        ] {
            let error = parse(source).expect_err(source);
            assert!(error.to_string().contains(expected), "{source}: {error}");
        }
    }

    #[test]
    fn rows_keyed_on_unit_variants_are_not_catch_alls() {
        // syn reads `A` and `B` as identifier patterns; only rustc knows
        // whether they name the variants the table's `use` brings in.
        let table = parse("for Index; use Register::*; a: A => 0; b: B => 1;")
            .expect("unit-variant rows are not certain catch-alls");
        assert_eq!(table.rows().len(), 2);
    }

    #[test]
    fn guarded_or_prioritized_rows_may_share_arguments() {
        parse(
            "for F;
             #[k::requires(bool::not(f))] a: (0, f) => B;
             #[k::requires(f)] b: (0, f) => C;
             #[k::equation(owise)] c: (_, _) => D;",
        )
        .expect("guards and owise separate the rows");
    }
}
