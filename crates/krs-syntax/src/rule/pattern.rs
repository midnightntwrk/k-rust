use krs_ir::ProvenanceKey;
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{Expr, Ident, Member, Pat, PatIdent, PatMacro, Path};

use crate::attribute::is_plain_path;
use crate::parse::{checked_ordinal, unsupported_rule_pattern as unsupported_pattern};
use crate::term::{is_term_macro, unexpected_macro};
use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, TermApplication,
    TermArguments, TermExpression, TermLiteral, TermNamedArgument, TermNode, TermSymbolKind,
    TermTree, TokenRange,
};

/// Supported subject-pattern shell.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Public variant field types are a compatibility contract.
pub enum RulePattern {
    /// Ordinary Rust named constructor pattern.
    Native {
        /// Original span-preserving pattern.
        pattern: Pat,
        /// Constructor paths and binding identifiers in deterministic preorder.
        paths: Vec<Path>,
        /// Plain bindings introduced by nested constructor arguments.
        bindings: Vec<Ident>,
        /// Typed application/reference/literal nodes in pattern preorder.
        nodes: Vec<TermNode>,
    },
    /// `term![RustExpression]` in Rust pattern position.
    TermMacro {
        /// Original macro pattern, including its invocation shell.
        pattern: PatMacro,
        /// Shared-parser term payload.
        term: TermExpression,
        /// Plain bindings introduced by nested bare paths in the payload.
        bindings: Vec<Ident>,
    },
}

impl RulePattern {
    /// Returns the native pattern, or `None` for a `term!` pattern.
    #[must_use]
    pub const fn native_pattern(&self) -> Option<&Pat> {
        match self {
            Self::Native { pattern, .. } => Some(pattern),
            Self::TermMacro { .. } => None,
        }
    }

    /// Returns the shared term payload, or `None` for a native pattern.
    #[must_use]
    pub const fn term(&self) -> Option<&TermExpression> {
        match self {
            Self::Native { .. } => None,
            Self::TermMacro { term, .. } => Some(term),
        }
    }

    /// Returns plain subject bindings in deterministic preorder.
    ///
    /// The root bare path is a unit constructor, not a binding. Within a
    /// `term!` subject, nested unqualified bare paths are bindings while
    /// qualified paths and application heads remain constructor references.
    #[must_use]
    pub fn bindings(&self) -> &[Ident] {
        match self {
            Self::Native { bindings, .. } | Self::TermMacro { bindings, .. } => bindings,
        }
    }

    /// Returns typed application/reference/literal nodes in deterministic
    /// subject-pattern preorder.
    #[must_use]
    pub fn nodes(&self) -> &[TermNode] {
        match self {
            Self::Native { nodes, .. } => nodes,
            Self::TermMacro { term, .. } => term.nodes(),
        }
    }

    /// Returns the deterministic reference-surface spelling.
    #[must_use]
    pub fn spelling(&self) -> String {
        match self {
            Self::Native { pattern, .. } => pattern.to_token_stream().to_string(),
            Self::TermMacro { term, .. } => term.spelling(),
        }
    }

    pub(super) fn path_ranges(&self) -> Result<Vec<TokenRange>, SyntaxError> {
        match self {
            Self::Native { paths, .. } => paths.iter().map(TokenRange::for_tokens).collect(),
            Self::TermMacro { term, .. } => term
                .symbols()
                .iter()
                .map(|symbol| TokenRange::for_tokens(symbol.path()))
                .collect(),
        }
    }

    pub(super) fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Native { pattern, .. } => TokenRange::for_tokens(pattern),
            Self::TermMacro { pattern, .. } => TokenRange::for_tokens(pattern),
        }
    }
}

pub(super) fn append_rule_pattern_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    pattern: &RulePattern,
    tree: &TermTree,
    counters: &mut RuleTermCounters,
) -> Result<(), SyntaxError> {
    for range in pattern.path_ranges()? {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::RuleLeftPath,
            checked_ordinal(counters.path, ProvenanceRole::RuleLeftPath, range.first())?,
            range,
        ));
        counters.path += 1;
    }
    for node in pattern.nodes() {
        let (role, counter) = match node {
            TermNode::ApplicationHead(_) => (
                ProvenanceRole::RuleLeftApplicationHead,
                &mut counters.application,
            ),
            TermNode::Reference(_) => (ProvenanceRole::RuleLeftReference, &mut counters.reference),
            TermNode::Literal(_) => (ProvenanceRole::RuleLeftLiteral, &mut counters.literal),
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => continue,
        };
        let range = match node {
            TermNode::ApplicationHead(path) | TermNode::Reference(path) => {
                TokenRange::for_tokens(path)?
            }
            TermNode::Literal(TermLiteral::Integer(value)) => TokenRange::for_tokens(value)?,
            TermNode::Literal(TermLiteral::Boolean(value)) => TokenRange::for_tokens(value)?,
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => {
                unreachable!("special nodes were skipped above")
            }
        };
        anchors.push(ProvenanceAnchor::new(
            role,
            checked_ordinal(*counter, role, range.first())?,
            range,
        ));
        *counter += 1;
    }
    let mut fields = Vec::new();
    tree.record_field_names_preorder(&mut fields);
    for field in fields {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::RuleLeftRecordFieldName,
            checked_ordinal(
                counters.field,
                ProvenanceRole::RuleLeftRecordFieldName,
                field.span(),
            )?,
            TokenRange::for_tokens(&field)?,
        ));
        counters.field += 1;
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub(super) enum RuleTermSide {
    Left,
    Right,
}

#[derive(Default)]
pub(super) struct RuleTermCounters {
    path: usize,
    application: usize,
    reference: usize,
    literal: usize,
    pub(super) field: usize,
}

impl RuleTermCounters {
    pub(super) fn from_rule_pattern(nodes: &[TermNode]) -> Self {
        let mut counters = Self {
            path: nodes.iter().filter(|node| node.path().is_some()).count(),
            ..Self::default()
        };
        for node in nodes {
            match node {
                TermNode::ApplicationHead(_) => counters.application += 1,
                TermNode::Reference(_) => counters.reference += 1,
                TermNode::Literal(_) => counters.literal += 1,
                TermNode::IdToken(_)
                | TermNode::BytesToken(_)
                | TermNode::Anonymous { .. }
                | TermNode::OrBool(_) => {}
            }
        }
        counters
    }
}

pub(super) fn append_rule_term_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    term: &TermExpression,
    side: RuleTermSide,
    counters: &mut RuleTermCounters,
) -> Result<(), SyntaxError> {
    let (path_role, application_role, reference_role, literal_role, field_role) = match side {
        RuleTermSide::Left => (
            ProvenanceRole::RuleLeftPath,
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftLiteral,
            ProvenanceRole::RuleLeftRecordFieldName,
        ),
        RuleTermSide::Right => (
            ProvenanceRole::RuleRightPath,
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightLiteral,
            ProvenanceRole::RuleRightRecordFieldName,
        ),
    };
    for symbol in term.symbols() {
        anchors.push(ProvenanceAnchor::new(
            path_role,
            checked_ordinal(counters.path, path_role, symbol.path().span())?,
            TokenRange::for_tokens(symbol.path())?,
        ));
        counters.path += 1;
    }
    for node in term.nodes() {
        let (role, counter) = match node {
            TermNode::ApplicationHead(_) => (application_role, &mut counters.application),
            TermNode::Reference(_) => (reference_role, &mut counters.reference),
            TermNode::Literal(_) => (literal_role, &mut counters.literal),
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => continue,
        };
        let span = match node {
            TermNode::ApplicationHead(path) | TermNode::Reference(path) => {
                TokenRange::for_tokens(path)?
            }
            TermNode::Literal(TermLiteral::Integer(value)) => TokenRange::for_tokens(value)?,
            TermNode::Literal(TermLiteral::Boolean(value)) => TokenRange::for_tokens(value)?,
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => {
                unreachable!("special nodes were skipped above")
            }
        };
        anchors.push(ProvenanceAnchor::new(
            role,
            checked_ordinal(*counter, role, span.first())?,
            span,
        ));
        *counter += 1;
    }
    let mut fields = Vec::new();
    term.tree().record_field_names_preorder(&mut fields);
    for field in fields {
        anchors.push(ProvenanceAnchor::new(
            field_role,
            checked_ordinal(counters.field, field_role, field.span())?,
            TokenRange::for_tokens(&field)?,
        ));
        counters.field += 1;
    }
    Ok(())
}

pub(super) fn parse_rule_pattern(
    pattern: Pat,
    allow_record_rest: bool,
    root_identifier_is_binding: bool,
) -> Result<(RulePattern, TermTree), SyntaxError> {
    match pattern {
        Pat::Macro(macro_pattern) => {
            if !is_term_macro(&macro_pattern.mac.path) {
                return Err(unexpected_macro(&macro_pattern.mac.path));
            }
            let term = TermExpression::from_pattern_expression(syn::parse2::<Expr>(
                macro_pattern.mac.tokens.clone(),
            )?)?;
            let bindings = term_pattern_bindings(&term);
            let tree = term.tree().clone();
            Ok((
                RulePattern::TermMacro {
                    pattern: macro_pattern,
                    term,
                    bindings,
                },
                tree,
            ))
        }
        pattern => {
            let mut paths = Vec::new();
            let mut bindings = Vec::new();
            let mut nodes = Vec::new();
            let tree = if root_identifier_is_binding {
                match &pattern {
                    Pat::Ident(identifier) => {
                        validate_native_binding(identifier, &mut paths, &mut bindings, &mut nodes)?
                    }
                    _ => validate_native_pattern(
                        &pattern,
                        true,
                        allow_record_rest,
                        &mut paths,
                        &mut bindings,
                        &mut nodes,
                    )?,
                }
            } else {
                validate_native_pattern(
                    &pattern,
                    true,
                    allow_record_rest,
                    &mut paths,
                    &mut bindings,
                    &mut nodes,
                )?
            };
            Ok((
                RulePattern::Native {
                    pattern,
                    paths,
                    bindings,
                    nodes,
                },
                tree,
            ))
        }
    }
}

#[allow(clippy::too_many_lines)] // Exhaustive validation over syn's closed pattern variants.
fn validate_native_pattern(
    pattern: &Pat,
    is_root: bool,
    allow_record_rest: bool,
    paths: &mut Vec<Path>,
    bindings: &mut Vec<Ident>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    match pattern {
        Pat::Ident(identifier) if is_root => validate_root_identifier(identifier, paths, nodes),
        Pat::Ident(identifier) => validate_native_binding(identifier, paths, bindings, nodes),
        Pat::Path(path) => {
            if path.qself.is_some() || !path.attrs.is_empty() || !is_plain_path(&path.path) {
                return Err(unsupported_pattern(
                    "expected a plain constructor path",
                    path.span(),
                ));
            }
            paths.push(path.path.clone());
            nodes.push(TermNode::Reference(path.path.clone()));
            Ok(TermTree::Reference(path.path.clone()))
        }
        Pat::TupleStruct(tuple) => {
            if tuple.qself.is_some() || !tuple.attrs.is_empty() || !is_plain_path(&tuple.path) {
                return Err(unsupported_pattern(
                    "expected a plain tuple constructor path",
                    tuple.span(),
                ));
            }
            paths.push(tuple.path.clone());
            nodes.push(TermNode::ApplicationHead(tuple.path.clone()));
            let mut arguments = Vec::with_capacity(tuple.elems.len());
            for element in &tuple.elems {
                arguments.push(validate_native_pattern(
                    element,
                    false,
                    allow_record_rest,
                    paths,
                    bindings,
                    nodes,
                )?);
            }
            Ok(TermTree::Application(TermApplication {
                head: tuple.path.clone(),
                arguments: TermArguments::Positional(arguments),
            }))
        }
        Pat::Struct(record) => {
            if record.qself.is_some() || !record.attrs.is_empty() || !is_plain_path(&record.path) {
                return Err(unsupported_pattern(
                    "expected a plain record constructor path",
                    record.span(),
                ));
            }
            if !allow_record_rest && let Some(rest) = &record.rest {
                return Err(unsupported_pattern(
                    "record rest patterns are outside the simple rule shape",
                    rest.span(),
                ));
            }
            paths.push(record.path.clone());
            nodes.push(TermNode::ApplicationHead(record.path.clone()));
            let mut arguments = Vec::with_capacity(record.fields.len());
            for field in &record.fields {
                let Member::Named(name) = &field.member else {
                    return Err(unsupported_pattern(
                        "record patterns require unadorned named fields",
                        field.span(),
                    ));
                };
                if !field.attrs.is_empty() {
                    return Err(unsupported_pattern(
                        "record patterns require unadorned named fields",
                        field.span(),
                    ));
                }
                arguments.push(TermNamedArgument {
                    name: name.clone(),
                    value: validate_native_pattern(
                        &field.pat,
                        false,
                        allow_record_rest,
                        paths,
                        bindings,
                        nodes,
                    )?,
                });
            }
            Ok(TermTree::Application(TermApplication {
                head: record.path.clone(),
                arguments: TermArguments::Named(arguments),
            }))
        }
        Pat::Paren(paren) => validate_native_pattern(
            &paren.pat,
            is_root,
            allow_record_rest,
            paths,
            bindings,
            nodes,
        ),
        Pat::Wild(wildcard) if !is_root => {
            if wildcard.attrs.is_empty() {
                Ok(TermTree::Wildcard(TokenRange::for_tokens(wildcard)?))
            } else {
                Err(unsupported_pattern(
                    "pattern attributes are not supported",
                    wildcard.span(),
                ))
            }
        }
        Pat::Lit(literal) => {
            let literal = validate_pattern_literal(literal, nodes)?;
            Ok(TermTree::Literal(literal))
        }
        Pat::Macro(macro_pattern) => Err(unsupported_pattern(
            "nested pattern macros are not supported",
            macro_pattern.span(),
        )),
        _ => Err(unsupported_pattern(
            "expected a named constructor with plain bindings, literals, or `_` arguments",
            pattern.span(),
        )),
    }
}

fn validate_root_identifier(
    identifier: &PatIdent,
    paths: &mut Vec<Path>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    if !identifier.attrs.is_empty()
        || identifier.by_ref.is_some()
        || identifier.mutability.is_some()
        || identifier.subpat.is_some()
    {
        return Err(unsupported_pattern(
            "a unit constructor subject must be one unadorned Rust identifier",
            identifier.span(),
        ));
    }
    let path = Path::from(identifier.ident.clone());
    paths.push(path.clone());
    nodes.push(TermNode::Reference(path.clone()));
    Ok(TermTree::Reference(path))
}

fn validate_native_binding(
    identifier: &PatIdent,
    paths: &mut Vec<Path>,
    bindings: &mut Vec<Ident>,
    nodes: &mut Vec<TermNode>,
) -> Result<TermTree, SyntaxError> {
    validate_binding(identifier, bindings)?;
    let path = Path::from(identifier.ident.clone());
    paths.push(path.clone());
    nodes.push(TermNode::Reference(path.clone()));
    Ok(TermTree::Reference(path))
}

fn validate_pattern_literal(
    literal: &syn::ExprLit,
    nodes: &mut Vec<TermNode>,
) -> Result<TermLiteral, SyntaxError> {
    if !literal.attrs.is_empty() {
        return Err(unsupported_pattern(
            "pattern attributes are not supported",
            literal.span(),
        ));
    }
    let literal = match &literal.lit {
        syn::Lit::Int(integer)
            if integer.suffix().is_empty()
                && integer
                    .to_string()
                    .chars()
                    .all(|character| character.is_ascii_digit() || character == '_') =>
        {
            TermLiteral::Integer(integer.clone())
        }
        syn::Lit::Bool(boolean) => TermLiteral::Boolean(boolean.clone()),
        _ => {
            return Err(unsupported_pattern(
                "only unsuffixed decimal Int and Bool literals are term patterns",
                literal.span(),
            ));
        }
    };
    nodes.push(TermNode::Literal(literal.clone()));
    Ok(literal)
}

fn validate_binding(identifier: &PatIdent, bindings: &mut Vec<Ident>) -> Result<(), SyntaxError> {
    if identifier.attrs.is_empty()
        && identifier.by_ref.is_none()
        && identifier.mutability.is_none()
        && identifier.subpat.is_none()
    {
        push_unique_binding(bindings, identifier.ident.clone());
        Ok(())
    } else {
        Err(unsupported_pattern(
            "constructor arguments allow only plain identifier bindings",
            identifier.span(),
        ))
    }
}

fn term_pattern_bindings(term: &TermExpression) -> Vec<Ident> {
    let mut bindings = Vec::new();
    for binding in term
        .symbols()
        .iter()
        .skip(1)
        .filter(|symbol| symbol.kind() == crate::TermSymbolKind::Reference)
        .filter_map(|symbol| bare_path_ident(symbol.path()).cloned())
    {
        push_unique_binding(&mut bindings, binding);
    }
    bindings
}

fn push_unique_binding(bindings: &mut Vec<Ident>, binding: Ident) {
    let spelling = binding.to_string();
    if !bindings.iter().any(|existing| existing == &spelling) {
        bindings.push(binding);
    }
}

fn bare_path_ident(path: &Path) -> Option<&Ident> {
    if path.leading_colon.is_none() && path.segments.len() == 1 {
        path.segments.first().map(|segment| &segment.ident)
    } else {
        None
    }
}

pub(super) fn is_bound_reference(symbol: &crate::TermSymbol, bindings: &[Ident]) -> bool {
    symbol.kind() == crate::TermSymbolKind::Reference && is_bound_path(symbol.path(), bindings)
}

pub(super) fn is_bound_path(path: &Path, bindings: &[Ident]) -> bool {
    bare_path_ident(path).is_some_and(|ident| {
        let spelling = ident.to_string();
        bindings.iter().any(|binding| binding == &spelling)
    })
}

pub(super) fn push_term_node_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    nodes: &[TermNode],
    application_role: ProvenanceRole,
    reference_role: ProvenanceRole,
    literal_role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut application_ordinal = 0_usize;
    let mut reference_ordinal = 0_usize;
    let mut literal_ordinal = 0_usize;
    for node in nodes {
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
            | TermNode::OrBool(_) => continue,
        };
        let range = term_node_range(node)?;
        anchors.push(ProvenanceAnchor::new(
            role,
            checked_ordinal(ordinal, role, range.first())?,
            range,
        ));
    }
    Ok(())
}

pub(super) fn push_wildcard_anchors(
    anchors: &mut Vec<ProvenanceAnchor>,
    tree: &TermTree,
) -> Result<(), SyntaxError> {
    let mut ranges = Vec::new();
    tree.wildcard_ranges_preorder(&mut ranges);
    for (ordinal, range) in ranges.into_iter().enumerate() {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::RuleLeftWildcard,
            checked_ordinal(ordinal, ProvenanceRole::RuleLeftWildcard, range.first())?,
            range,
        ));
    }
    Ok(())
}

pub(super) fn push_term_reference_candidates(
    candidates: &mut Vec<ReferenceCandidate<TermSymbolKind>>,
    nodes: &[TermNode],
    bindings: &[Ident],
    application_role: ProvenanceRole,
    reference_role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut application_ordinal = 0_usize;
    let mut reference_ordinal = 0_usize;
    for node in nodes {
        let (path, kind, role, ordinal) = match node {
            TermNode::ApplicationHead(path) => {
                let ordinal = application_ordinal;
                application_ordinal += 1;
                (
                    path,
                    TermSymbolKind::ApplicationHead,
                    application_role,
                    ordinal,
                )
            }
            TermNode::Reference(path) => {
                let ordinal = reference_ordinal;
                reference_ordinal += 1;
                if is_bound_path(path, bindings) {
                    continue;
                }
                (path, TermSymbolKind::Reference, reference_role, ordinal)
            }
            TermNode::Literal(_)
            | TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => continue,
        };
        let ordinal = checked_ordinal(ordinal, role, path.span())?;
        candidates.push(ReferenceCandidate {
            key: canonical_key(role, ordinal),
            path: path.clone(),
            kind,
        });
    }
    Ok(())
}

fn term_node_range(node: &TermNode) -> Result<TokenRange, SyntaxError> {
    match node {
        TermNode::ApplicationHead(path) | TermNode::Reference(path) => TokenRange::for_tokens(path),
        TermNode::Literal(TermLiteral::Integer(literal)) => TokenRange::for_tokens(literal),
        TermNode::Literal(TermLiteral::Boolean(literal)) => TokenRange::for_tokens(literal),
        TermNode::IdToken(literal) => TokenRange::for_tokens(literal),
        TermNode::BytesToken(literal) => TokenRange::for_tokens(literal),
        TermNode::Anonymous { spelling, .. } => TokenRange::for_tokens(spelling),
        TermNode::OrBool(range) => Ok(*range),
    }
}

pub(super) fn push_candidate(
    candidates: &mut Vec<ReferenceCandidate>,
    role: ProvenanceRole,
    ordinal: usize,
    path: &Path,
) -> Result<(), SyntaxError> {
    let ordinal = checked_ordinal(ordinal, role, path.span())?;
    candidates.push(ReferenceCandidate {
        key: canonical_key(role, ordinal),
        path: path.clone(),
        kind: (),
    });
    Ok(())
}

pub(super) fn canonical_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
}
