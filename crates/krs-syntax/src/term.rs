use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{
    Expr, ExprCall, ExprGroup, ExprLit, ExprMacro, ExprParen, ExprPath, ExprStruct, Lit, LitBool,
    LitByteStr, LitInt, LitStr, Member, Path, Token,
};

use crate::attribute::is_plain_path;
use crate::parse::{KrsSyntax, checked_ordinal};
use crate::surface::path_text;
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// Syntactic shape at the root of an accepted term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermRootKind {
    /// Bare named path: a variable/reference or a unit constructor after resolution.
    Named,
    /// Tuple/unit-like named constructor application, `path(arguments...)`.
    Call,
    /// Record named constructor application, `path { fields... }`.
    Record,
    /// Integer or Boolean Rust literal.
    Literal,
    /// Anonymous wildcard admitted only by a structured rule pattern.
    Wildcard,
}

/// Exact literal families admitted by the term grammar.
#[derive(Clone, Debug)]
pub enum TermLiteral {
    /// Unsuffixed decimal Rust integer literal.
    Integer(LitInt),
    /// Rust Boolean literal.
    Boolean(LitBool),
}

impl TermLiteral {
    /// Returns a canonical literal spelling suitable for target-neutral
    /// lowering. Integer separators are removed.
    #[must_use]
    pub fn spelling(&self) -> String {
        match self {
            Self::Integer(literal) => literal.base10_digits().replace('_', ""),
            Self::Boolean(literal) => literal.value.to_string(),
        }
    }

    fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Integer(literal) => TokenRange::for_tokens(literal),
            Self::Boolean(literal) => TokenRange::for_tokens(literal),
        }
    }
}

/// Typed semantic node retained in deterministic expression preorder.
#[derive(Clone, Debug)]
pub enum TermNode {
    /// Head path of a named call or record construction.
    ApplicationHead(Path),
    /// Bare path awaiting binder/constructor resolution.
    Reference(Path),
    /// Integer or Boolean literal.
    Literal(TermLiteral),
    /// Compiler-owned concrete token of builtin sort `Id`.
    IdToken(LitStr),
    /// Compiler-owned concrete token of builtin sort `Bytes`.
    BytesToken(LitByteStr),
    /// One fresh typed anonymous-variable occurrence.
    Anonymous {
        /// Explicit object-language sort.
        sort: Path,
        /// Exact display spelling.
        spelling: LitStr,
    },
    /// Compiler-owned associative object-Bool disjunction shell.
    OrBool(TokenRange),
}

impl TermNode {
    /// Returns the path for a named node and `None` for a literal.
    #[must_use]
    pub const fn path(&self) -> Option<&Path> {
        match self {
            Self::ApplicationHead(path) | Self::Reference(path) => Some(path),
            Self::Literal(_)
            | Self::IdToken(_)
            | Self::BytesToken(_)
            | Self::Anonymous { .. }
            | Self::OrBool(_) => None,
        }
    }

    /// Returns the literal for a literal node.
    #[must_use]
    pub const fn literal(&self) -> Option<&TermLiteral> {
        match self {
            Self::Literal(literal) => Some(literal),
            Self::ApplicationHead(_)
            | Self::Reference(_)
            | Self::IdToken(_)
            | Self::BytesToken(_)
            | Self::Anonymous { .. }
            | Self::OrBool(_) => None,
        }
    }

    fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::ApplicationHead(path) | Self::Reference(path) => TokenRange::for_tokens(path),
            Self::Literal(literal) => literal.range(),
            Self::IdToken(literal) => TokenRange::for_tokens(literal),
            Self::BytesToken(literal) => TokenRange::for_tokens(literal),
            Self::Anonymous { spelling, .. } => TokenRange::for_tokens(spelling),
            Self::OrBool(range) => Ok(*range),
        }
    }
}

/// Structured application arguments preserving Rust call-versus-record
/// semantics.
#[derive(Clone, Debug)]
pub enum TermArguments {
    /// Ordered positional arguments of `head(first, second)`.
    Positional(Vec<TermTree>),
    /// Authored named arguments of `head { second: y, first: x }`.
    Named(Vec<TermNamedArgument>),
}

impl TermArguments {
    /// Returns positional arguments, or `None` for a record application.
    #[must_use]
    pub fn positional(&self) -> Option<&[TermTree]> {
        match self {
            Self::Positional(arguments) => Some(arguments),
            Self::Named(_) => None,
        }
    }

    /// Returns named arguments, or `None` for a call application.
    #[must_use]
    pub fn named(&self) -> Option<&[TermNamedArgument]> {
        match self {
            Self::Named(arguments) => Some(arguments),
            Self::Positional(_) => None,
        }
    }
}

/// One named record argument with its exact authored Rust field identity.
#[derive(Clone, Debug)]
pub struct TermNamedArgument {
    pub(crate) name: syn::Ident,
    pub(crate) value: TermTree,
}

impl TermNamedArgument {
    /// Returns the exact record field identifier and its authored span.
    #[must_use]
    pub const fn name(&self) -> &syn::Ident {
        &self.name
    }

    /// Returns the field's structured term or pattern value.
    #[must_use]
    pub const fn value(&self) -> &TermTree {
        &self.value
    }
}

/// One named constructor or builtin application in the structured term tree.
#[derive(Clone, Debug)]
pub struct TermApplication {
    pub(crate) head: Path,
    pub(crate) arguments: TermArguments,
}

/// One compiler-owned complete parent-cell term.
#[derive(Clone, Debug)]
pub struct CellTerm {
    pub(crate) range: TokenRange,
    pub(crate) owner: Path,
    pub(crate) fields: Vec<TermNamedArgument>,
}

impl CellTerm {
    /// Returns the complete `fragment!` invocation range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the nominal `#[k::cell]` owner.
    #[must_use]
    pub const fn owner(&self) -> &Path {
        &self.owner
    }

    /// Returns authored child fields in source order.
    #[must_use]
    pub fn fields(&self) -> &[TermNamedArgument] {
        &self.fields
    }
}

impl TermApplication {
    /// Returns the rustc-resolvable application-head path.
    #[must_use]
    pub const fn head(&self) -> &Path {
        &self.head
    }

    /// Returns positional call arguments or named record arguments.
    #[must_use]
    pub const fn arguments(&self) -> &TermArguments {
        &self.arguments
    }
}

/// Structured term/pattern shape used for deterministic argument lowering.
///
/// Parentheses and invisible `syn` groups are transparent. A wildcard occurs
/// only in a rule pattern, never in a result or standalone term expression.
#[derive(Clone, Debug)]
pub enum TermTree {
    /// Named application retaining positional-versus-record arguments.
    Application(TermApplication),
    /// Bare path awaiting binder or zero-argument constructor resolution.
    Reference(Path),
    /// Integer or Boolean literal.
    Literal(TermLiteral),
    /// Native Rust pattern wildcard.
    Wildcard(TokenRange),
    /// `k::id!("$name")` concrete builtin token.
    IdToken {
        /// Exact validated token literal.
        literal: LitStr,
    },
    /// `k::bytes!(b"...")` concrete builtin token.
    BytesToken {
        /// Exact validated byte-string literal.
        literal: LitByteStr,
    },
    /// `k::anonymous!(Sort, "_Name")` fresh anonymous occurrence.
    Anonymous {
        /// Explicit object-language sort path.
        sort: Path,
        /// Exact authored display spelling.
        spelling: LitStr,
    },
    /// `k::or_bool![...]` associative Boolean disjunction.
    OrBool {
        /// Complete macro invocation range.
        range: TokenRange,
        /// Ordered operands (at least two).
        arguments: Vec<TermTree>,
    },
    /// `k::fragment![Parent { ... }]` complete nested-cell term.
    Cell(CellTerm),
}

impl TermTree {
    /// Returns an application node, if this is a call or record application.
    #[must_use]
    pub const fn application(&self) -> Option<&TermApplication> {
        match self {
            Self::Application(application) => Some(application),
            Self::Reference(_)
            | Self::Literal(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_) => None,
        }
    }

    /// Returns the bare reference path, if present.
    #[must_use]
    pub const fn reference(&self) -> Option<&Path> {
        match self {
            Self::Reference(path) => Some(path),
            Self::Application(_)
            | Self::Literal(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_) => None,
        }
    }

    /// Returns the literal, if present.
    #[must_use]
    pub const fn literal(&self) -> Option<&TermLiteral> {
        match self {
            Self::Literal(literal) => Some(literal),
            Self::Application(_)
            | Self::Reference(_)
            | Self::Wildcard(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_) => None,
        }
    }

    /// Returns the wildcard token range, if this is a native pattern `_`.
    #[must_use]
    pub const fn wildcard_range(&self) -> Option<TokenRange> {
        match self {
            Self::Wildcard(range) => Some(*range),
            Self::Application(_)
            | Self::Reference(_)
            | Self::Literal(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. }
            | Self::OrBool { .. }
            | Self::Cell(_) => None,
        }
    }

    pub(crate) fn record_field_names_preorder(&self, output: &mut Vec<syn::Ident>) {
        let arguments = match self {
            Self::Application(application) => &application.arguments,
            Self::Cell(cell) => {
                for argument in &cell.fields {
                    output.push(argument.name.clone());
                    argument.value.record_field_names_preorder(output);
                }
                return;
            }
            _ => return,
        };
        match arguments {
            TermArguments::Positional(arguments) => {
                for argument in arguments {
                    argument.record_field_names_preorder(output);
                }
            }
            TermArguments::Named(arguments) => {
                for argument in arguments {
                    output.push(argument.name.clone());
                    argument.value.record_field_names_preorder(output);
                }
            }
        }
    }

    pub(crate) fn wildcard_ranges_preorder(&self, output: &mut Vec<TokenRange>) {
        match self {
            Self::Application(application) => match &application.arguments {
                TermArguments::Positional(arguments) => {
                    for argument in arguments {
                        argument.wildcard_ranges_preorder(output);
                    }
                }
                TermArguments::Named(arguments) => {
                    for argument in arguments {
                        argument.value.wildcard_ranges_preorder(output);
                    }
                }
            },
            Self::Wildcard(range) => output.push(*range),
            Self::OrBool { arguments, .. } => {
                for argument in arguments {
                    argument.wildcard_ranges_preorder(output);
                }
            }
            Self::Cell(cell) => {
                for argument in &cell.fields {
                    argument.value.wildcard_ranges_preorder(output);
                }
            }
            Self::Reference(_)
            | Self::Literal(_)
            | Self::IdToken { .. }
            | Self::BytesToken { .. }
            | Self::Anonymous { .. } => {}
        }
    }
}

/// Role of one path within a term expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermSymbolKind {
    /// Head of a call or record constructor application.
    ApplicationHead,
    /// Bare path whose constructor/reference meaning awaits Rust/KRS resolution.
    Reference,
}

/// One named path retained in deterministic preorder.
#[derive(Clone, Debug)]
pub struct TermSymbol {
    path: Path,
    kind: TermSymbolKind,
}

impl TermSymbol {
    /// Returns the authored path with its original token spans.
    #[must_use]
    pub const fn path(&self) -> &Path {
        &self.path
    }

    /// Returns whether this path is an application head or a bare reference.
    #[must_use]
    pub const fn kind(&self) -> TermSymbolKind {
        self.kind
    }
}

/// A validated Rust-expression term in the deliberately small term grammar.
///
/// Accepted nodes are plain paths, named calls, named record construction,
/// parentheses/groups, and Rust literals below a named root. No operator,
/// method, closure, control-flow, assignment, macro, update-rest, or arbitrary
/// block expression is silently retained.
#[derive(Clone, Debug)]
pub struct TermExpression {
    expression: Expr,
    root_kind: TermRootKind,
    symbols: Vec<TermSymbol>,
    nodes: Vec<TermNode>,
    tree: TermTree,
}

impl TermExpression {
    /// Validates a previously parsed Rust expression as a term.
    ///
    /// # Errors
    ///
    /// Returns a structured error at the first expression outside the closed
    /// named-term subset.
    pub fn from_expression(expression: Expr) -> Result<Self, SyntaxError> {
        Self::from_expression_context(expression, TermExpressionContext::Expression)
    }

    pub(crate) fn from_pattern_expression(expression: Expr) -> Result<Self, SyntaxError> {
        Self::from_expression_context(expression, TermExpressionContext::Pattern)
    }

    fn from_expression_context(
        expression: Expr,
        context: TermExpressionContext,
    ) -> Result<Self, SyntaxError> {
        let root = transparent_expression(&expression);
        let root_kind = match root {
            Expr::Path(_) => TermRootKind::Named,
            Expr::Call(_) => TermRootKind::Call,
            Expr::Struct(_) => TermRootKind::Record,
            Expr::Lit(literal) if is_supported_literal(literal) => TermRootKind::Literal,
            Expr::Infer(_) if context == TermExpressionContext::Pattern => TermRootKind::Wildcard,
            Expr::Macro(value) if special_macro_name(&value.mac.path).is_some() => {
                match special_macro_name(&value.mac.path) {
                    Some("or_bool" | "fragment") => TermRootKind::Call,
                    Some("id" | "bytes" | "anonymous") => TermRootKind::Literal,
                    _ => unreachable!(),
                }
            }
            other => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "the root must be a named path/call/record or an Int/Bool literal",
                    },
                    other.span(),
                ));
            }
        };
        let mut symbols = Vec::new();
        let mut nodes = Vec::new();
        let tree = validate_expression(&expression, context, &mut symbols, &mut nodes)?;
        Ok(Self {
            expression,
            root_kind,
            symbols,
            nodes,
            tree,
        })
    }

    /// Returns the original span-preserving Rust expression.
    #[must_use]
    pub const fn expression(&self) -> &Expr {
        &self.expression
    }

    /// Returns the syntactic root kind.
    #[must_use]
    pub const fn root_kind(&self) -> TermRootKind {
        self.root_kind
    }

    /// Returns all named paths in deterministic preorder.
    #[must_use]
    pub fn symbols(&self) -> &[TermSymbol] {
        &self.symbols
    }

    /// Returns application heads, references, and literals in deterministic
    /// expression preorder.
    #[must_use]
    pub fn nodes(&self) -> &[TermNode] {
        &self.nodes
    }

    /// Returns the structured argument-preserving term tree.
    #[must_use]
    pub const fn tree(&self) -> &TermTree {
        &self.tree
    }

    /// Returns the token spelling used by the deterministic reference surface.
    #[must_use]
    pub fn spelling(&self) -> String {
        self.expression.to_token_stream().to_string()
    }

    /// Returns standalone term-payload provenance anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.provenance_with_roles(ProvenanceRole::TermPayload, ProvenanceRole::TermPath)
    }

    /// Returns payload plus typed application/reference/literal anchors for
    /// protocol-v6 lowering. The compact path catalog remains available via
    /// [`Self::provenance`].
    ///
    /// # Errors
    ///
    /// Returns an endpoint or occurrence-overflow error.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.full_provenance_with_roles(
            ProvenanceRole::TermPayload,
            ProvenanceRole::TermApplicationHead,
            ProvenanceRole::TermReference,
            ProvenanceRole::TermLiteral,
            ProvenanceRole::TermRecordFieldName,
        )
    }

    pub(crate) fn full_provenance_with_roles(
        &self,
        payload_role: ProvenanceRole,
        application_role: ProvenanceRole,
        reference_role: ProvenanceRole,
        literal_role: ProvenanceRole,
        record_field_role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            payload_role,
            0,
            TokenRange::for_tokens(&self.expression)?,
        )];
        let mut application_ordinal = 0_usize;
        let mut reference_ordinal = 0_usize;
        let mut literal_ordinal = 0_usize;
        for node in &self.nodes {
            let (role, ordinal) = match node {
                TermNode::ApplicationHead(_) => {
                    let ordinal = application_ordinal;
                    application_ordinal += 1;
                    (application_role, ordinal)
                }
                TermNode::Reference(_) => {
                    let ordinal = reference_ordinal;
                    reference_ordinal += 1;
                    (reference_role, ordinal)
                }
                TermNode::Literal(_) => {
                    let ordinal = literal_ordinal;
                    literal_ordinal += 1;
                    (literal_role, ordinal)
                }
                TermNode::IdToken(_)
                | TermNode::BytesToken(_)
                | TermNode::Anonymous { .. }
                | TermNode::OrBool(_) => {
                    continue;
                }
            };
            let range = node.range()?;
            anchors.push(ProvenanceAnchor::new(
                role,
                checked_ordinal(ordinal, role, range.first())?,
                range,
            ));
        }
        push_record_field_anchors(&mut anchors, &self.tree, record_field_role)?;
        Ok(anchors)
    }

    pub(crate) fn provenance_with_roles(
        &self,
        payload_role: ProvenanceRole,
        path_role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(self.symbols.len() + 1);
        anchors.push(ProvenanceAnchor::new(
            payload_role,
            0,
            TokenRange::for_tokens(&self.expression)?,
        ));
        for (ordinal, symbol) in self.symbols.iter().enumerate() {
            let ordinal = checked_ordinal(ordinal, path_role, symbol.path.span())?;
            anchors.push(ProvenanceAnchor::new(
                path_role,
                ordinal,
                TokenRange::for_tokens(&symbol.path)?,
            ));
        }
        Ok(anchors)
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TermExpressionContext {
    Pattern,
    Expression,
}

impl KrsSyntax for TermExpression {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let expression = syn::parse2::<Expr>(tokens)?;
        Self::from_expression(expression)
    }
}

fn validate_expression(
    expression: &Expr,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    match expression {
        Expr::Path(path) => validate_path_expression(path, symbols, nodes),
        Expr::Call(call) => validate_call(call, context, symbols, nodes),
        Expr::Struct(record) => validate_record(record, context, symbols, nodes),
        Expr::Paren(ExprParen { attrs, expr, .. }) | Expr::Group(ExprGroup { attrs, expr, .. }) => {
            reject_attributes(attrs, expression.span())?;
            validate_expression(expr, context, symbols, nodes)
        }
        Expr::Lit(literal) => validate_literal(literal, nodes),
        Expr::Infer(infer) if context == TermExpressionContext::Pattern => {
            reject_attributes(&infer.attrs, infer.span())?;
            Ok(TermTree::Wildcard(TokenRange::for_tokens(infer)?))
        }
        Expr::Macro(value) => validate_special_macro(value, context, symbols, nodes),
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "expected paths, named calls/records, parentheses, or literal arguments",
            },
            expression.span(),
        )),
    }
}

fn special_macro_name(path: &Path) -> Option<&'static str> {
    let name = path.segments.last()?.ident.to_string();
    match name.as_str() {
        "id" => Some("id"),
        "bytes" => Some("bytes"),
        "anonymous" => Some("anonymous"),
        "or_bool" => Some("or_bool"),
        "fragment" => Some("fragment"),
        _ => None,
    }
}

fn validate_special_macro(
    value: &ExprMacro,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&value.attrs, value.span())?;
    match special_macro_name(&value.mac.path) {
        Some("id") => {
            let literal: LitStr = syn::parse2(value.mac.tokens.clone())?;
            let text = literal.value();
            if !valid_extended_id(&text) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "invalid builtin `Id` token; expected `$` followed by ASCII letters, digits, or `_`",
                    },
                    literal.span(),
                ));
            }
            nodes.push(TermNode::IdToken(literal.clone()));
            Ok(TermTree::IdToken { literal })
        }
        Some("bytes") => {
            let literal: LitByteStr = syn::parse2(value.mac.tokens.clone())?;
            nodes.push(TermNode::BytesToken(literal.clone()));
            Ok(TermTree::BytesToken { literal })
        }
        Some("anonymous") => {
            let parser = |input: syn::parse::ParseStream<'_>| -> syn::Result<(Path, LitStr)> {
                let sort: Path = input.parse()?;
                input.parse::<Token![,]>()?;
                let spelling: LitStr = input.parse()?;
                if !input.is_empty() {
                    return Err(input.error("anonymous! accepts exactly `Sort, \"_Name\"`"));
                }
                Ok((sort, spelling))
            };
            let (sort, spelling) = parser.parse2(value.mac.tokens.clone())?;
            let text = spelling.value();
            if !text.starts_with('_')
                || text.len() < 2
                || !text[1..]
                    .chars()
                    .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
            {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "anonymous spelling must begin with `_` and contain only ASCII letters, digits, or `_`",
                    },
                    spelling.span(),
                ));
            }
            nodes.push(TermNode::Anonymous {
                sort: sort.clone(),
                spelling: spelling.clone(),
            });
            Ok(TermTree::Anonymous { sort, spelling })
        }
        Some("or_bool") => {
            let expressions = syn::punctuated::Punctuated::<Expr, Token![,]>::parse_terminated
                .parse2(value.mac.tokens.clone())?;
            if expressions.len() < 2 {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnsupportedTermExpression {
                        reason: "or_bool! requires at least two object-Bool operands",
                    },
                    value.span(),
                ));
            }
            let range = TokenRange::for_tokens(value)?;
            nodes.push(TermNode::OrBool(range));
            let arguments = expressions
                .iter()
                .map(|expression| validate_expression(expression, context, symbols, nodes))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(TermTree::OrBool { range, arguments })
        }
        Some("fragment") => validate_cell_term(value, context, symbols, nodes),
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "macros are not terms unless they are compiler-owned `id!`, `anonymous!`, or `or_bool!` islands",
            },
            value.span(),
        )),
    }
}

fn validate_cell_term(
    value: &ExprMacro,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    let record: ExprStruct = syn::parse2(value.mac.tokens.clone())?;
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    if let Some(rest) = &record.rest {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms do not admit record update/rest syntax",
            },
            rest.span(),
        ));
    }
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let mut fields = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "complete cell terms require unadorned named fields",
                },
                field.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "complete cell terms require unadorned named fields",
                },
                field.span(),
            ));
        }
        fields.push(TermNamedArgument {
            name: name.clone(),
            value: validate_expression(&field.expr, context, symbols, nodes)?,
        });
    }
    if fields.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "complete cell terms require at least one child field",
            },
            record.span(),
        ));
    }
    Ok(TermTree::Cell(CellTerm {
        range: TokenRange::for_tokens(value)?,
        owner: record.path,
        fields,
    }))
}

fn valid_extended_id(value: &str) -> bool {
    value.strip_prefix('$').is_some_and(|tail| {
        !tail.is_empty()
            && tail
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    })
}

fn validate_path_expression(
    expression: &ExprPath,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&expression.attrs, expression.span())?;
    if expression.qself.is_some() || !is_plain_path(&expression.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            expression.span(),
        ));
    }
    symbols.push(TermSymbol {
        path: expression.path.clone(),
        kind: TermSymbolKind::Reference,
    });
    nodes.push(TermNode::Reference(expression.path.clone()));
    Ok(TermTree::Reference(expression.path.clone()))
}

fn validate_call(
    call: &ExprCall,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&call.attrs, call.span())?;
    let Expr::Path(head) = &*call.func else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "a term call must have a plain named path as its head",
            },
            call.func.span(),
        ));
    };
    if head.qself.is_some() || !head.attrs.is_empty() || !is_plain_path(&head.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            head.span(),
        ));
    }
    symbols.push(TermSymbol {
        path: head.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(head.path.clone()));
    let mut arguments = Vec::with_capacity(call.args.len());
    for argument in &call.args {
        arguments.push(validate_expression(argument, context, symbols, nodes)?);
    }
    Ok(TermTree::Application(TermApplication {
        head: head.path.clone(),
        arguments: TermArguments::Positional(arguments),
    }))
}

fn validate_record(
    record: &ExprStruct,
    context: TermExpressionContext,
    symbols: &mut Vec<TermSymbol>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    reject_attributes(&record.attrs, record.span())?;
    if record.qself.is_some() || !is_plain_path(&record.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedPath,
            record.path.span(),
        ));
    }
    if let Some(rest) = &record.rest {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "record update/rest syntax is not supported in term construction",
            },
            rest.span(),
        ));
    }
    symbols.push(TermSymbol {
        path: record.path.clone(),
        kind: TermSymbolKind::ApplicationHead,
    });
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let mut arguments = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "record terms require unadorned named fields",
                },
                field.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "record terms require unadorned named fields",
                },
                field.span(),
            ));
        }
        arguments.push(TermNamedArgument {
            name: name.clone(),
            value: validate_expression(&field.expr, context, symbols, nodes)?,
        });
    }
    Ok(TermTree::Application(TermApplication {
        head: record.path.clone(),
        arguments: TermArguments::Named(arguments),
    }))
}

fn validate_literal(literal: &ExprLit, nodes: &mut Vec<TermNode>) -> Result<TermTree, SyntaxError> {
    reject_attributes(&literal.attrs, literal.span())?;
    let literal = match &literal.lit {
        Lit::Int(integer)
            if integer.suffix().is_empty()
                && integer
                    .to_string()
                    .chars()
                    .all(|character| character.is_ascii_digit() || character == '_') =>
        {
            TermLiteral::Integer(integer.clone())
        }
        Lit::Bool(boolean) => TermLiteral::Boolean(boolean.clone()),
        Lit::Int(_) => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "Int literals must be unsuffixed decimal Rust integers",
                },
                literal.span(),
            ));
        }
        _ => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnsupportedTermExpression {
                    reason: "only Int and Bool Rust literals are term values",
                },
                literal.span(),
            ));
        }
    };
    nodes.push(TermNode::Literal(literal.clone()));
    Ok(TermTree::Literal(literal))
}

pub(crate) fn push_record_field_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    tree: &TermTree,
    role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut fields = Vec::new();
    tree.record_field_names_preorder(&mut fields);
    for (ordinal, field) in fields.iter().enumerate() {
        anchors.push(ProvenanceAnchor::new(
            role,
            checked_ordinal(ordinal, role, field.span())?,
            TokenRange::for_tokens(field)?,
        ));
    }
    Ok(())
}

fn is_supported_literal(literal: &ExprLit) -> bool {
    match &literal.lit {
        Lit::Bool(_) => literal.attrs.is_empty(),
        Lit::Int(integer) => {
            literal.attrs.is_empty()
                && integer.suffix().is_empty()
                && integer
                    .to_string()
                    .chars()
                    .all(|character| character.is_ascii_digit() || character == '_')
        }
        _ => false,
    }
}

fn transparent_expression(mut expression: &Expr) -> &Expr {
    loop {
        expression = match expression {
            Expr::Paren(paren) => &paren.expr,
            Expr::Group(group) => &group.expr,
            _ => return expression,
        };
    }
}

fn reject_attributes(
    attributes: &[syn::Attribute],
    span: proc_macro2::Span,
) -> Result<(), SyntaxError> {
    if attributes.is_empty() {
        Ok(())
    } else {
        Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: "expression attributes are not supported in term payloads",
            },
            span,
        ))
    }
}

pub(crate) fn is_term_macro(path: &Path) -> bool {
    is_plain_path(path)
        && path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "term")
}

pub(crate) fn unexpected_macro(path: &Path) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnexpectedMacro {
            path: path_text(path),
        },
        path.span(),
    )
}

#[cfg(test)]
mod bytes_token_tests {
    use super::{TermExpression, TermNode, TermTree};
    use crate::KrsSyntax;

    #[test]
    fn byte_string_macro_parses_as_one_intrinsic_token() {
        let expression = TermExpression::parse_source(r#"k::bytes!(b"\x00A\xff")"#).unwrap();
        let TermTree::BytesToken { literal } = expression.tree() else {
            panic!("bytes! must retain its intrinsic token node");
        };
        assert_eq!(literal.value(), b"\x00A\xff");
        assert!(matches!(expression.nodes(), [TermNode::BytesToken(_)]));
        assert_eq!(expression.spelling(), r#"k :: bytes ! (b"\x00A\xff")"#);
    }

    #[test]
    fn byte_string_macro_rejects_non_byte_literals() {
        assert!(TermExpression::parse_source(r#"k::bytes!("not bytes")"#).is_err());
    }
}
