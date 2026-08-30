use std::cell::RefCell;
use std::collections::BTreeSet;

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::quote;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Expr, Ident, Path, Token, parenthesized};

use crate::attribute::{is_plain_path, path_spelling};
use crate::{
    ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TermExpression, TokenRange,
};

/// Whether a compiler-owned state island occurs in pattern or expression position.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateMacroContext {
    /// Bindings use `name @ ..` and expression-style spread is rejected.
    Pattern,
    /// Reuse uses `..name` and pattern-style binding is rejected.
    Expression,
}

/// Exact, anonymous, bound-pattern, or reused-expression associative tail.
#[derive(Clone, Debug)]
pub enum StateMacroRemainder {
    /// No content is omitted.
    Exact,
    /// Anonymous pattern remainder (`..`).
    Anonymous(TokenRange),
    /// Pattern remainder binding (`name @ ..`).
    Bind {
        /// Introduced pattern binding.
        binding: Ident,
        /// Complete `binding @ ..` range.
        range: TokenRange,
    },
    /// Expression remainder reuse (`..name`).
    Reuse {
        /// Previously introduced frame binding.
        binding: Ident,
        /// Complete `..binding` range.
        range: TokenRange,
    },
}

impl StateMacroRemainder {
    /// Returns the optional binding name.
    #[must_use]
    pub const fn binding(&self) -> Option<&Ident> {
        match self {
            Self::Bind { binding, .. } | Self::Reuse { binding, .. } => Some(binding),
            Self::Exact | Self::Anonymous(_) => None,
        }
    }

    fn range(&self) -> Option<TokenRange> {
        match self {
            Self::Exact => None,
            Self::Anonymous(range) | Self::Bind { range, .. } | Self::Reuse { range, .. } => {
                Some(*range)
            }
        }
    }
}

/// Surface notation used for an exact K sequence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KSequenceNotation {
    /// Comma-delimited host notation.
    Comma,
    /// K's authored `~>` connective.
    Operator,
    /// Explicit empty `.K`.
    DotK,
}

/// Parsed `k!` payload with an ordered prefix and explicit associative tail.
#[derive(Clone, Debug)]
pub struct KSequence {
    tokens: TokenStream,
    items: Vec<TermExpression>,
    tail: StateMacroRemainder,
    notation: KSequenceNotation,
}

impl KSequence {
    /// Ordered K items before the tail.
    #[must_use]
    pub fn items(&self) -> &[TermExpression] {
        &self.items
    }

    /// Exact or framed sequence tail.
    #[must_use]
    pub const fn tail(&self) -> &StateMacroRemainder {
        &self.tail
    }

    /// Authored comma/operator/`.K` notation.
    #[must_use]
    pub const fn notation(&self) -> KSequenceNotation {
        self.notation
    }

    /// Whether the sequence denotes exact `.K` (explicitly or as `k![]`).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty() && matches!(self.tail, StateMacroRemainder::Exact)
    }

    /// Returns payload, item, and tail anchors.
    ///
    /// Empty `k![]` has no inner token endpoint; its enclosing macro node owns
    /// that shell range, so this method returns no payload anchor for it.
    ///
    /// # Errors
    ///
    /// Returns an endpoint or ordinal-overflow error.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = Vec::new();
        if !self.tokens.is_empty() {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::KSequencePayload,
                0,
                TokenRange::for_tokens(&self.tokens)?,
            ));
        }
        for (index, item) in self.items.iter().enumerate() {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::KSequenceItem,
                ordinal(
                    ProvenanceRole::KSequenceItem,
                    index,
                    item.expression().span(),
                )?,
                TokenRange::for_tokens(item.expression())?,
            ));
        }
        if let Some(range) = self.tail.range() {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::KSequenceTail,
                0,
                range,
            ));
        } else if self.notation == KSequenceNotation::DotK {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::KSequenceTail,
                0,
                TokenRange::for_tokens(&self.tokens)?,
            ));
        }
        Ok(output)
    }
}

/// One associative map item.
#[derive(Clone, Debug)]
pub struct MapItem {
    key: TermExpression,
    value: TermExpression,
}

impl MapItem {
    /// Returns the authored key term.
    #[must_use]
    pub const fn key(&self) -> &TermExpression {
        &self.key
    }

    /// Returns the authored value term.
    #[must_use]
    pub const fn value(&self) -> &TermExpression {
        &self.value
    }
}

/// Empty, associative-item, or functional-update `map!` payload.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Span-preserving term nodes are the public parser contract.
pub enum MapBody {
    /// Empty `.Map` unit (also represented by `map![]`).
    Empty {
        /// Whether `.Map` was authored instead of an empty payload.
        explicit_dot: bool,
    },
    /// Ordered authored items plus an exact or associative remainder.
    Items {
        /// Key/value items.
        items: Vec<MapItem>,
        /// Exact or framed map remainder.
        remainder: StateMacroRemainder,
    },
    /// Functional update of a base map at one key.
    Update {
        /// Existing map term.
        base: TermExpression,
        /// Updated key.
        key: TermExpression,
        /// Replacement value.
        value: TermExpression,
    },
}

/// Parsed `map!` payload.
#[derive(Clone, Debug)]
pub struct MapExpression {
    tokens: TokenStream,
    body: MapBody,
}

impl MapExpression {
    /// Returns the classified map operation.
    #[must_use]
    pub const fn body(&self) -> &MapBody {
        &self.body
    }

    /// Returns payload and structural map anchors.
    ///
    /// # Errors
    ///
    /// Returns endpoint or ordinal-overflow errors only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = Vec::new();
        if !self.tokens.is_empty() {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::MapPayload,
                0,
                TokenRange::for_tokens(&self.tokens)?,
            ));
        }
        match &self.body {
            MapBody::Empty { .. } => {}
            MapBody::Items { items, remainder } => {
                for (index, item) in items.iter().enumerate() {
                    let ordinal =
                        ordinal(ProvenanceRole::MapKey, index, item.key.expression().span())?;
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::MapKey,
                        ordinal,
                        TokenRange::for_tokens(item.key.expression())?,
                    ));
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::MapValue,
                        ordinal,
                        TokenRange::for_tokens(item.value.expression())?,
                    ));
                }
                if let Some(range) = remainder.range() {
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::MapRemainder,
                        0,
                        range,
                    ));
                }
            }
            MapBody::Update { base, key, value } => {
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::MapUpdateBase,
                    0,
                    TokenRange::for_tokens(base.expression())?,
                ));
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::MapKey,
                    0,
                    TokenRange::for_tokens(key.expression())?,
                ));
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::MapValue,
                    0,
                    TokenRange::for_tokens(value.expression())?,
                ));
            }
        }
        Ok(output)
    }
}

/// Term families admitted as fixed leaf-cell contents.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Avoid hiding parser AST ownership behind allocation.
pub enum StateTerm {
    /// Ordinary M3A named term.
    Term(TermExpression),
    /// Compiler-parsed K sequence.
    KSequence(KSequence),
    /// Compiler-parsed map operation.
    Map(MapExpression),
}

/// One selected fixed leaf in a `cells!` payload.
#[derive(Clone, Debug)]
pub struct CellsEntry {
    name: Ident,
    owner: Option<Path>,
    wrapper: Path,
    value: StateTerm,
}

impl CellsEntry {
    /// Returns the declared Rust field name used for identity resolution.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns an explicit nested declaration owner, when the field was
    /// written as an owner-qualified path such as `Account::storage`.
    ///
    /// Unqualified authored fields continue to resolve against the rule's
    /// top-level configuration.
    #[must_use]
    pub const fn owner(&self) -> Option<&Path> {
        self.owner.as_ref()
    }

    /// Returns the authored `Cell`/`KCell` wrapper path.
    #[must_use]
    pub const fn wrapper(&self) -> &Path {
        &self.wrapper
    }

    /// Returns the compiler-parsed leaf contents.
    #[must_use]
    pub const fn value(&self) -> &StateTerm {
        &self.value
    }
}

/// Parsed `cells!` pattern or expression payload.
#[derive(Clone, Debug)]
pub struct CellsExpression {
    tokens: TokenStream,
    context: StateMacroContext,
    entries: Vec<CellsEntry>,
    remainder: StateMacroRemainder,
}

impl CellsExpression {
    /// Pattern versus expression context used for frame validation.
    #[must_use]
    pub const fn context(&self) -> StateMacroContext {
        self.context
    }

    /// Selected cells in authored order.
    #[must_use]
    pub fn entries(&self) -> &[CellsEntry] {
        &self.entries
    }

    /// Exact, anonymous, bound, or reused configuration frame.
    #[must_use]
    pub const fn remainder(&self) -> &StateMacroRemainder {
        &self.remainder
    }

    /// Returns payload, field, wrapper, and remainder anchors.
    ///
    /// Nested `k!`/`map!` provenance is returned by each entry's [`StateTerm`].
    ///
    /// # Errors
    ///
    /// Returns endpoint or ordinal-overflow errors only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = vec![ProvenanceAnchor::new(
            ProvenanceRole::CellsPayload,
            0,
            TokenRange::for_tokens(&self.tokens)?,
        )];
        for (index, entry) in self.entries.iter().enumerate() {
            let ordinal = ordinal(ProvenanceRole::CellsField, index, entry.name.span())?;
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::CellsField,
                ordinal,
                TokenRange::for_tokens(&entry.name)?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::CellsWrapper,
                ordinal,
                TokenRange::for_tokens(&entry.wrapper)?,
            ));
        }
        if let Some(range) = self.remainder.range() {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::CellsRemainder,
                0,
                range,
            ));
        }
        Ok(output)
    }
}

/// Parses a `k!` pattern payload.
///
/// # Errors
///
/// Rejects malformed separators, misplaced `.K`, duplicate tails, and
/// expression-style `..tail` at the responsible token.
pub fn parse_k_sequence_pattern(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Pattern)
}

/// Parses a `k!` expression payload.
///
/// # Errors
///
/// Rejects pattern-only tail bindings and malformed sequence syntax.
pub fn parse_k_sequence_expression(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Expression)
}

/// Parses a `k!` pattern payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_k_sequence_pattern`].
pub fn parse_k_sequence_pattern_source(source: &str) -> Result<KSequence, SyntaxError> {
    parse_k_sequence_pattern(source_tokens(source)?)
}

/// Parses a `k!` expression payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_k_sequence_expression`].
pub fn parse_k_sequence_expression_source(source: &str) -> Result<KSequence, SyntaxError> {
    parse_k_sequence_expression(source_tokens(source)?)
}

/// Parses a `map!` pattern payload.
///
/// # Errors
///
/// Rejects updates and expression-style remainders in pattern position.
pub fn parse_map_pattern(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Pattern)
}

/// Parses a `map!` expression payload, including functional updates.
///
/// # Errors
///
/// Rejects pattern-only remainder bindings and malformed items/updates.
pub fn parse_map_expression(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Expression)
}

/// Parses a `map!` pattern payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_map_pattern`].
pub fn parse_map_pattern_source(source: &str) -> Result<MapExpression, SyntaxError> {
    parse_map_pattern(source_tokens(source)?)
}

/// Parses a `map!` pattern payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_map_pattern`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_map_pattern_source_with_trivia(
    source: &str,
) -> Result<(MapExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("map")?;
    Ok((parse_map_pattern(tokens)?, trivia))
}

/// Parses a `map!` expression payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_map_expression`].
pub fn parse_map_expression_source(source: &str) -> Result<MapExpression, SyntaxError> {
    parse_map_expression(source_tokens(source)?)
}

/// Parses a `map!` expression payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_map_expression`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_map_expression_source_with_trivia(
    source: &str,
) -> Result<(MapExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("map")?;
    Ok((parse_map_expression(tokens)?, trivia))
}

/// Parses a `cells!` pattern payload.
///
/// # Errors
///
/// Rejects duplicate cells, malformed wrappers, and expression-only frames.
pub fn parse_cells_pattern(tokens: TokenStream) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Pattern)
}

/// Parses a `cells!` expression payload.
///
/// # Errors
///
/// Rejects duplicate cells, malformed wrappers, and pattern-only frames.
pub fn parse_cells_expression(tokens: TokenStream) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Expression)
}

/// Parses a `cells!` pattern payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_cells_pattern`].
pub fn parse_cells_pattern_source(source: &str) -> Result<CellsExpression, SyntaxError> {
    parse_cells_pattern(source_tokens(source)?)
}

/// Parses a `cells!` pattern payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_cells_pattern`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_cells_pattern_source_with_trivia(
    source: &str,
) -> Result<(CellsExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("cells")?;
    Ok((parse_cells_pattern(tokens)?, trivia))
}

/// Parses a `cells!` expression payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_cells_expression`].
pub fn parse_cells_expression_source(source: &str) -> Result<CellsExpression, SyntaxError> {
    parse_cells_expression(source_tokens(source)?)
}

/// Parses a `cells!` expression payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_cells_expression`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_cells_expression_source_with_trivia(
    source: &str,
) -> Result<(CellsExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("cells")?;
    Ok((parse_cells_expression(tokens)?, trivia))
}

#[allow(clippy::too_many_lines)] // One closed sequence grammar keeps tail diagnostics local.
fn parse_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<KSequence, SyntaxError> {
    let original = tokens.clone();
    parse_structured(tokens, "k", move |input| {
        if input.is_empty() {
            return Ok(KSequence {
                tokens: original.clone(),
                items: Vec::new(),
                tail: StateMacroRemainder::Exact,
                notation: KSequenceNotation::Comma,
            });
        }
        if starts_remainder(input) {
            let tail = parse_remainder(input, context, "k")?;
            if !input.is_empty() {
                return Err(state_error(
                    "k",
                    "the sequence tail must be last",
                    input.span(),
                ));
            }
            return Ok(KSequence {
                tokens: original.clone(),
                items: Vec::new(),
                tail,
                notation: KSequenceNotation::Comma,
            });
        }
        if input.peek(Token![.]) {
            let range = parse_dot_unit(input, "K")?;
            if !input.is_empty() {
                return Err(state_error(
                    "k",
                    "`.K` must be the complete empty sequence",
                    input.span(),
                ));
            }
            let _ = range;
            return Ok(KSequence {
                tokens: original.clone(),
                items: Vec::new(),
                tail: StateMacroRemainder::Exact,
                notation: KSequenceNotation::DotK,
            });
        }

        let mut items = Vec::new();
        let mut tail = StateMacroRemainder::Exact;
        let mut notation = None;
        loop {
            if starts_remainder(input) {
                tail = parse_remainder(input, context, "k")?;
                break;
            }
            let expression = input
                .call(Expr::parse_without_eager_brace)
                .map_err(SyntaxError::from)?;
            items.push(state_term_expression(expression, context)?);
            if input.is_empty() {
                break;
            }
            let separator = if input.peek(Token![,]) {
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
                KSequenceNotation::Comma
            } else if input.peek(Token![~]) {
                input.parse::<Token![~]>().map_err(SyntaxError::from)?;
                input.parse::<Token![>]>().map_err(SyntaxError::from)?;
                KSequenceNotation::Operator
            } else {
                return Err(state_error(
                    "k",
                    "expected `,`, `~>`, or a sequence tail",
                    input.span(),
                ));
            };
            if let Some(previous) = notation
                && previous != separator
            {
                return Err(state_error(
                    "k",
                    "cannot mix `,` and `~>` separators",
                    input.span(),
                ));
            }
            notation = Some(separator);
            if input.is_empty() {
                return Err(state_error(
                    "k",
                    "a sequence separator requires another item",
                    input.span(),
                ));
            }
            if input.peek(Token![.]) && !input.peek(Token![..]) {
                parse_dot_unit(input, "K")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "k",
                        "`.K` must terminate the sequence",
                        input.span(),
                    ));
                }
                break;
            }
        }
        if !input.is_empty() {
            return Err(state_error(
                "k",
                "the sequence tail must be last",
                input.span(),
            ));
        }
        Ok(KSequence {
            tokens: original.clone(),
            items,
            tail,
            notation: notation.unwrap_or(KSequenceNotation::Comma),
        })
    })
}

#[allow(clippy::too_many_lines)] // One closed grammar keeps update/item diagnostics local.
fn parse_map(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<MapExpression, SyntaxError> {
    if let Some((base, bracket)) = split_bracket_update(&tokens) {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                bracket.span(),
            ));
        }
        let base = crate::parse_term_expression(base)?;
        let (key, value) = parse_update_inner(bracket.stream())?;
        return Ok(MapExpression {
            tokens,
            body: MapBody::Update { base, key, value },
        });
    }
    if let Some((base_tokens, update_tokens)) = split_once_punct(&tokens, ';') {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                tokens.span(),
            ));
        }
        let base = crate::parse_term_expression(base_tokens)?;
        let (key, value) = parse_update_inner(update_tokens)?;
        return Ok(MapExpression {
            tokens,
            body: MapBody::Update { base, key, value },
        });
    }
    let original = tokens.clone();
    parse_structured(tokens, "map", move |input| {
        if input.is_empty() {
            return Ok(MapExpression {
                tokens: original.clone(),
                body: MapBody::Empty {
                    explicit_dot: false,
                },
            });
        }
        if input.peek(Token![.]) {
            parse_dot_unit(input, "Map")?;
            if !input.is_empty() {
                return Err(state_error(
                    "map",
                    "`.Map` must be the complete empty map",
                    input.span(),
                ));
            }
            return Ok(MapExpression {
                tokens: original.clone(),
                body: MapBody::Empty { explicit_dot: true },
            });
        }

        if starts_remainder(input) {
            let remainder = parse_remainder(input, context, "map")?;
            if !input.is_empty() {
                return Err(state_error(
                    "map",
                    "the map remainder must be the complete payload",
                    input.span(),
                ));
            }
            return Ok(MapExpression {
                tokens: original.clone(),
                body: MapBody::Items {
                    items: Vec::new(),
                    remainder,
                },
            });
        }

        let first = parse_map_item_key(input)?;
        parse_map_item_arrow(input)?;
        let value = input
            .call(Expr::parse_without_eager_brace)
            .map_err(SyntaxError::from)?;
        let mut items = vec![MapItem {
            key: state_term_expression(first, context)?,
            value: state_term_expression(value, context)?,
        }];
        let mut remainder = StateMacroRemainder::Exact;
        while !input.is_empty() {
            input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            if input.is_empty() {
                break;
            }
            if starts_remainder(input) {
                remainder = parse_remainder(input, context, "map")?;
                break;
            }
            let key = parse_map_item_key(input)?;
            parse_map_item_arrow(input)?;
            let value = input
                .call(Expr::parse_without_eager_brace)
                .map_err(SyntaxError::from)?;
            items.push(MapItem {
                key: state_term_expression(key, context)?,
                value: state_term_expression(value, context)?,
            });
        }
        if !input.is_empty() {
            return Err(state_error(
                "map",
                "the map remainder must be last",
                input.span(),
            ));
        }
        Ok(MapExpression {
            tokens: original.clone(),
            body: MapBody::Items { items, remainder },
        })
    })
}

fn parse_map_item_arrow(input: ParseStream<'_>) -> Result<(), SyntaxError> {
    if input.peek(Token![=>]) {
        return Err(state_error(
            "map",
            "`=>` is reserved for rewrites; map entries use `->`",
            input.span(),
        ));
    }
    input
        .parse::<Token![->]>()
        .map(|_| ())
        .map_err(|_| state_error("map", "expected `->` after a map-item key", input.span()))
}

fn parse_map_item_key(input: ParseStream<'_>) -> Result<Expr, SyntaxError> {
    let mut tokens = TokenStream::new();
    while !input.is_empty() && !input.peek(Token![->]) && !input.peek(Token![=>]) {
        tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    if tokens.is_empty() {
        return Err(state_error("map", "expected a map-item key", input.span()));
    }
    syn::parse2(tokens).map_err(SyntaxError::from)
}

fn parse_cells(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<CellsExpression, SyntaxError> {
    let original = tokens.clone();
    parse_structured(tokens, "cells", move |input| {
        let mut entries = Vec::new();
        let mut names = BTreeSet::new();
        let mut remainder = StateMacroRemainder::Exact;
        while !input.is_empty() {
            if starts_remainder(input) {
                remainder = parse_remainder(input, context, "cells")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "cells",
                        "the configuration remainder must be last",
                        input.span(),
                    ));
                }
                break;
            }
            let mut field: Path = input.parse().map_err(SyntaxError::from)?;
            if !is_plain_path(&field) {
                return Err(state_error(
                    "cells",
                    "cell fields must be plain Rust paths",
                    field.span(),
                ));
            }
            let name = field
                .segments
                .pop()
                .expect("a plain cell field path is nonempty")
                .into_value()
                .ident;
            field.segments.pop_punct();
            let owner = if field.segments.is_empty() {
                None
            } else {
                Some(field)
            };
            let identity = owner.as_ref().map_or_else(
                || name.to_string(),
                |owner| format!("{}::{name}", path_spelling(owner)),
            );
            if !names.insert(identity) {
                return Err(state_error(
                    "cells",
                    "an owner-qualified cell field occurs more than once",
                    name.span(),
                ));
            }
            input.parse::<Token![:]>().map_err(SyntaxError::from)?;
            let wrapper: Path = input.parse().map_err(SyntaxError::from)?;
            if !is_plain_path(&wrapper) {
                return Err(state_error(
                    "cells",
                    "cell wrappers must be plain Rust paths",
                    wrapper.span(),
                ));
            }
            let value_tokens = parse_parenthesized_tokens(input).map_err(SyntaxError::from)?;
            let wrapper_name = wrapper
                .segments
                .last()
                .expect("plain path is nonempty")
                .ident
                .to_string();
            let value = match wrapper_name.as_str() {
                "KCell" => StateTerm::KSequence(parse_k_sequence(value_tokens, context)?),
                "Cell" => parse_state_term(value_tokens, context)?,
                _ => {
                    return Err(state_error(
                        "cells",
                        "entries require `Cell(...)` or `KCell(...)`",
                        wrapper.span(),
                    ));
                }
            };
            entries.push(CellsEntry {
                name,
                owner,
                wrapper,
                value,
            });
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>().map_err(SyntaxError::from)?;
        }
        if entries.is_empty() {
            return Err(state_error(
                "cells",
                "at least one cell clause is required",
                input.span(),
            ));
        }
        Ok(CellsExpression {
            tokens: original.clone(),
            context,
            entries,
            remainder,
        })
    })
}

fn parse_state_term(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<StateTerm, SyntaxError> {
    if let Some((name, payload)) = macro_payload(&tokens) {
        return match name.as_str() {
            "k" => Ok(StateTerm::KSequence(parse_k_sequence(payload, context)?)),
            "map" => Ok(StateTerm::Map(parse_map(payload, context)?)),
            _ => Err(state_error(
                "cells",
                "cell contents use only `k!` or `map!` state macros",
                tokens.span(),
            )),
        };
    }
    let expression = syn::parse2::<Expr>(tokens)?;
    Ok(StateTerm::Term(state_term_expression(expression, context)?))
}

fn state_term_expression(
    expression: Expr,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => TermExpression::from_pattern_expression(expression),
        StateMacroContext::Expression => TermExpression::from_expression(expression),
    }
}

fn parse_remainder(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
) -> Result<StateMacroRemainder, SyntaxError> {
    if input.peek(Token![..]) {
        let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
        if input.peek(Ident) {
            let binding: Ident = input.parse().map_err(SyntaxError::from)?;
            if context == StateMacroContext::Pattern {
                return Err(state_error(
                    macro_name,
                    "patterns bind remainders as `name @ ..`",
                    binding.span(),
                ));
            }
            return Ok(StateMacroRemainder::Reuse {
                range: TokenRange::for_tokens(&quote!(#dots #binding))?,
                binding,
            });
        }
        if context == StateMacroContext::Expression {
            return Err(state_error(
                macro_name,
                "expression remainders must reuse a named binding as `..name`",
                dots.span(),
            ));
        }
        return Ok(StateMacroRemainder::Anonymous(TokenRange::for_tokens(
            &dots,
        )?));
    }
    let binding: Ident = input.parse().map_err(SyntaxError::from)?;
    input.parse::<Token![@]>().map_err(SyntaxError::from)?;
    let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
    if context == StateMacroContext::Expression {
        return Err(state_error(
            macro_name,
            "expressions reuse remainders as `..name`",
            binding.span(),
        ));
    }
    Ok(StateMacroRemainder::Bind {
        range: TokenRange::for_tokens(&quote!(#binding #dots))?,
        binding,
    })
}

fn starts_remainder(input: ParseStream<'_>) -> bool {
    input.peek(Token![..]) || (input.peek(Ident) && input.peek2(Token![@]))
}

fn parse_dot_unit(
    input: ParseStream<'_>,
    expected: &'static str,
) -> Result<TokenRange, SyntaxError> {
    let dot: Token![.] = input.parse().map_err(SyntaxError::from)?;
    let name: Ident = input.parse().map_err(SyntaxError::from)?;
    if name != expected {
        return Err(state_error(
            if expected == "K" { "k" } else { "map" },
            if expected == "K" {
                "expected `.K`"
            } else {
                "expected `.Map`"
            },
            name.span(),
        ));
    }
    TokenRange::for_tokens(&quote!(#dot #name))
}

fn parse_parenthesized_tokens(input: ParseStream<'_>) -> syn::Result<TokenStream> {
    let content;
    parenthesized!(content in input);
    content.parse()
}

fn split_bracket_update(tokens: &TokenStream) -> Option<(TokenStream, proc_macro2::Group)> {
    let mut trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let TokenTree::Group(group) = trees.pop()? else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket || trees.is_empty() {
        return None;
    }
    Some((trees.into_iter().collect(), group))
}

fn parse_update_inner(
    tokens: TokenStream,
) -> Result<(TermExpression, TermExpression), SyntaxError> {
    let trees = tokens.into_iter().collect::<Vec<_>>();
    if let Some(legacy_arrow) = trees.windows(2).position(|window| {
        matches!(&window[0], TokenTree::Punct(value) if value.as_char() == '=')
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == '>')
    }) {
        return Err(state_error(
            "map",
            "`=>` is reserved for rewrites; map updates use `<-`",
            trees[legacy_arrow].span(),
        ));
    }
    let split = trees.windows(2).position(|window| {
        matches!(&window[0], TokenTree::Punct(value) if value.as_char() == '<')
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == '-')
    });
    let Some(split) = split else {
        return Err(state_error(
            "map",
            "functional updates require `key <- value`",
            Span::call_site(),
        ));
    };
    if split == 0 || split + 2 == trees.len() {
        return Err(state_error(
            "map",
            "functional update key and value must be nonempty",
            Span::call_site(),
        ));
    }
    let key = trees[..split].iter().cloned().collect();
    let value = trees[split + 2..].iter().cloned().collect();
    Ok((
        crate::parse_term_expression(key)?,
        crate::parse_term_expression(value)?,
    ))
}

fn split_once_punct(tokens: &TokenStream, expected: char) -> Option<(TokenStream, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let split = trees
        .iter()
        .position(|tree| matches!(tree, TokenTree::Punct(value) if value.as_char() == expected))?;
    if split == 0 || split + 1 == trees.len() {
        return None;
    }
    Some((
        trees[..split].iter().cloned().collect(),
        trees[split + 1..].iter().cloned().collect(),
    ))
}

fn macro_payload(tokens: &TokenStream) -> Option<(String, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    if trees.len() != 3 {
        return None;
    }
    let TokenTree::Ident(name) = &trees[0] else {
        return None;
    };
    let TokenTree::Punct(bang) = &trees[1] else {
        return None;
    };
    let TokenTree::Group(group) = &trees[2] else {
        return None;
    };
    (bang.as_char() == '!').then(|| (name.to_string(), group.stream()))
}

fn parse_structured<T>(
    tokens: TokenStream,
    macro_name: &'static str,
    parser: impl Fn(ParseStream<'_>) -> Result<T, SyntaxError>,
) -> Result<T, SyntaxError> {
    let structured = RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parser(input) {
        Ok(value) => Ok(value),
        Err(error) => {
            structured.replace(Some(error.clone()));
            Err(error.into_syn_error())
        }
    };
    parser.parse2(tokens).map_err(|error| {
        structured.borrow_mut().take().unwrap_or_else(|| {
            state_error(
                macro_name,
                "malformed compiler-owned state syntax",
                error.span(),
            )
        })
    })
}

fn source_tokens(source: &str) -> Result<TokenStream, SyntaxError> {
    source.parse().map_err(|error: proc_macro2::LexError| {
        SyntaxError::new(
            SyntaxErrorKind::RustSyntax(error.to_string()),
            Span::call_site(),
        )
    })
}

fn state_error(macro_name: &'static str, reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidStateMacro { macro_name, reason },
        span,
    )
}

fn ordinal(role: ProvenanceRole, value: usize, span: Span) -> Result<u32, SyntaxError> {
    u32::try_from(value).map_err(|_| {
        SyntaxError::new(
            SyntaxErrorKind::TooManyProvenanceOccurrences {
                role: role.as_str(),
            },
            span,
        )
    })
}

/// Deterministic spelling helper for state-macro reference paths.
#[must_use]
pub fn state_path_spelling(path: &Path) -> String {
    path_spelling(path)
}
