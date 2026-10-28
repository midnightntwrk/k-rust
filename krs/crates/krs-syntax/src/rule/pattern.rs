use krs_ir::ProvenanceKey;
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::{Ident, Pat, PatMacro, Path};

use crate::parse::{
    KeyAllocator, checked_ordinal, unsupported_rule_pattern as unsupported_pattern,
};
use crate::term::{TermKeys, allocate_record_field_keys, is_term_macro};
use crate::{
    IntegerLiteral, ProvenanceRole, ReferenceCandidate, SyntaxError, TermExpression, TermLiteral,
    TermNode, TermSymbolKind, TermTree, TokenRange,
};

/// The `-` and digits spans of each negative literal in a pattern's source
/// tokens, in source order.
///
/// syn reads `-1` in a pattern as one literal token whose span covers the
/// digits only where spans can be joined, which a compiler-hosted macro cannot
/// do; a negative pattern literal takes its range from these source spans so
/// that it is the same in every host.
#[derive(Clone, Debug, Default)]
pub(crate) struct NegativeLiteralSpans(std::collections::VecDeque<(Span, Span)>);

impl NegativeLiteralSpans {
    /// Collects every `-` immediately followed by a numeric literal, in token order.
    pub(crate) fn scan(tokens: TokenStream) -> Self {
        let mut spans = std::collections::VecDeque::new();
        collect_negative_literals(tokens, &mut spans);
        Self(spans)
    }

    /// Scans the parameter list of the `fn` item in `tokens`.
    pub(crate) fn of_fn_parameters(tokens: TokenStream) -> Self {
        let mut after_fn = false;
        for token in tokens {
            match token {
                TokenTree::Ident(ident) if ident == "fn" => after_fn = true,
                TokenTree::Group(group)
                    if after_fn && group.delimiter() == Delimiter::Parenthesis =>
                {
                    return Self::scan(group.stream());
                }
                _ => {}
            }
        }
        Self::default()
    }

    /// The next negative literal's `-` and digit spans, in token order.
    pub(crate) fn next(&mut self) -> Option<(Span, Span)> {
        self.0.pop_front()
    }

    /// The number of negative literals left.
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    /// Drops the next `count` negative literals, which a nested island
    /// parses from its own tokens.
    pub(crate) fn skip(&mut self, count: usize) {
        for _ in 0..count {
            self.0.pop_front();
        }
    }
}

/// Parses one term at a position that matches terms, with the spans of its
/// negative literals: a Rust pattern, or the term expression its tokens are
/// ([`crate::term::parse_term_pattern`]).
pub(crate) fn parse_pattern_with_signs(
    input: syn::parse::ParseStream<'_>,
) -> syn::Result<(Pat, NegativeLiteralSpans)> {
    parse_with_signs(input, crate::term::parse_term_pattern)
}

/// Parses one Rust pattern with the spans of its negative literals: a
/// position rustc parses as Rust, such as a match arm in a fn body.
pub(crate) fn parse_rust_pattern_with_signs(
    input: syn::parse::ParseStream<'_>,
) -> syn::Result<(Pat, NegativeLiteralSpans)> {
    parse_with_signs(input, Pat::parse_multi)
}

fn parse_with_signs(
    input: syn::parse::ParseStream<'_>,
    parse: fn(syn::parse::ParseStream<'_>) -> syn::Result<Pat>,
) -> syn::Result<(Pat, NegativeLiteralSpans)> {
    let start = input.cursor();
    // `A | B` alternatives (K's #Or, KF-030) may join whole subjects.
    let pattern = input.call(parse)?;
    let tokens = crate::term::tokens_between(start, input.cursor());
    Ok((pattern, NegativeLiteralSpans::scan(tokens)))
}

fn collect_negative_literals(
    tokens: TokenStream,
    spans: &mut std::collections::VecDeque<(Span, Span)>,
) {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    for (index, token) in tokens.iter().enumerate() {
        match token {
            TokenTree::Group(group) => collect_negative_literals(group.stream(), spans),
            TokenTree::Punct(punct) if punct.as_char() == '-' => {
                if let Some(TokenTree::Literal(literal)) = tokens.get(index + 1)
                    && literal
                        .to_string()
                        .starts_with(|character: char| character.is_ascii_digit())
                {
                    spans.push_back((punct.span(), literal.span()));
                }
            }
            _ => {}
        }
    }
}

/// Supported subject-pattern shell.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Public variant field types are a compatibility contract."
)]
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
        /// The keys the enclosing sentence's pass gave the pattern, indexed
        /// as `paths` (symbols), `nodes`, and the subject tree's record field
        /// names and wildcards; read them through [`RulePattern::keys`].
        keys: TermKeys,
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

    /// Returns the keys the enclosing sentence gave the pattern: its symbols
    /// are indexed as its paths ([`TermExpression::symbols`] for a `term!`
    /// pattern), its nodes as [`Self::nodes`], and its record field names and
    /// wildcards as the subject tree's.
    #[must_use]
    pub const fn keys(&self) -> &TermKeys {
        match self {
            Self::Native { keys, .. } => keys,
            Self::TermMacro { term, .. } => term.keys(),
        }
    }

    /// The pattern's nodes with its keys, for a pass that keys them.
    pub(crate) fn keying(&mut self) -> (&[TermNode], &mut TermKeys) {
        match self {
            Self::Native { nodes, keys, .. } => (nodes, keys),
            Self::TermMacro { term, .. } => {
                let (nodes, _, keys) = term.keying();
                (nodes, keys)
            }
        }
    }

    /// Forgets the pattern's keys, before a sentence's pass keys it.
    pub(crate) fn clear_keys(&mut self) {
        match self {
            Self::Native { keys, .. } => keys.clear(),
            Self::TermMacro { term, .. } => term.clear_keys(),
        }
    }

    /// Keys each constructor and binding path in preorder (the term's symbol
    /// paths for a `term!` pattern), as the next of `role`.
    pub(super) fn allocate_path_keys(
        &mut self,
        keys: &mut KeyAllocator,
        role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        let ranges = self.path_ranges()?;
        let (_, term_keys) = self.keying();
        for (index, range) in ranges.into_iter().enumerate() {
            term_keys.set_symbol(index, keys.key(role, range)?);
        }
        Ok(())
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

/// Keys a left-hand pattern's paths, then its application head, reference,
/// and literal nodes, then its record field names (those of `tree`, the
/// subject tree), each as the next of its left-hand role.
pub(super) fn allocate_rule_pattern_keys(
    keys: &mut KeyAllocator,
    pattern: &mut RulePattern,
    tree: &TermTree,
) -> Result<(), SyntaxError> {
    pattern.allocate_path_keys(keys, ProvenanceRole::RuleLeftPath)?;
    let (nodes, term_keys) = pattern.keying();
    for (index, node) in nodes.iter().enumerate() {
        let role = match node {
            TermNode::ApplicationHead(_) => ProvenanceRole::RuleLeftApplicationHead,
            TermNode::Reference(_) => ProvenanceRole::RuleLeftReference,
            TermNode::Literal(_) => ProvenanceRole::RuleLeftLiteral,
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_)
            | TermNode::Lexeme { .. }
            | TermNode::SortTest { .. }
            | TermNode::As { .. }
            | TermNode::Or(_)
            | TermNode::Matches(_)
            | TermNode::MatchesWildcard(_)
            | TermNode::Let { .. }
            | TermNode::Closure { .. }
            | TermNode::LetWildcard(_)
            | TermNode::Rewrite { .. } => continue,
        };
        term_keys.push_node(index, keys.key(role, node.range()?)?);
    }
    allocate_record_field_keys(
        keys,
        tree,
        term_keys,
        ProvenanceRole::RuleLeftRecordFieldName,
    )
}

#[derive(Clone, Copy)]
pub(super) enum RuleTermSide {
    Left,
    Right,
}

/// Keys a term's symbol paths, then its application head, reference, and
/// literal nodes, then its record field names, each as the next of its role
/// on `side`.
pub(super) fn allocate_rule_term_keys(
    keys: &mut KeyAllocator,
    term: &mut TermExpression,
    side: RuleTermSide,
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
    term.allocate_symbol_keys(keys, path_role)?;
    let (nodes, tree, term_keys) = term.keying();
    allocate_term_node_keys(
        keys,
        nodes,
        term_keys,
        application_role,
        reference_role,
        literal_role,
    )?;
    allocate_record_field_keys(keys, tree, term_keys, field_role)
}

pub(super) use crate::positions::PatternRoot;

/// Parses a rule pattern whose root reads as `root` says. The native
/// grammar is the one pattern reader a `k::term!` payload is read with
/// ([`crate::term::read_pattern`]), compiler-owned islands included, so the
/// wrapper is never needed around a pattern; the position table judges each
/// construct where it stands.
pub(super) fn parse_rule_pattern(
    pattern: Pat,
    root: PatternRoot,
    mut signs: NegativeLiteralSpans,
) -> Result<(RulePattern, TermTree), SyntaxError> {
    match pattern {
        Pat::Macro(macro_pattern) if is_term_macro(&macro_pattern.mac.path) => {
            let tokens = crate::parse::strip_trailing_comma(macro_pattern.mac.tokens.clone());
            // The wrapper is optional around a pattern, so its payload reads
            // at the pattern's root as a native pattern does: `_` and an
            // island stand below a subject's root, and a readable value
            // stands below the rule's subject, so `|` and an alias at its
            // root read as they do below a constructor.
            let term = TermExpression::parse_pattern_tokens_at(tokens, root)?;
            // A wrapped clause root names a unit constructor with a bare
            // name, as a subject's does, so an alias there would stand for
            // the whole subject.
            if root == PatternRoot::Clause {
                reject_subject_root_alias(term.tree())?;
            }
            let bindings = term_pattern_bindings(&term, root != PatternRoot::Value)?;
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
            let mut symbols = Vec::new();
            let mut nodes = Vec::new();
            let tree =
                crate::term::read_pattern(&pattern, root, &mut signs, &mut symbols, &mut nodes)?;
            let paths = symbols
                .into_iter()
                .map(|symbol| symbol.path().clone())
                .collect();
            // A subject's root names the matched constructor, but where a
            // clause's root is a bare name, which binds the whole subject.
            let root = root.at(matches!(pattern, Pat::Ident(_) | Pat::Macro(_)));
            let mut bindings = Vec::new();
            for binding in crate::term::pattern_tree_binders(&tree, root.names_constructor()) {
                crate::parse::validate_authored_binder(&binding.to_string(), binding.span())?;
                push_unique_binding(&mut bindings, binding);
            }
            Ok((
                RulePattern::Native {
                    pattern,
                    paths,
                    bindings,
                    nodes,
                    keys: TermKeys::default(),
                },
                tree,
            ))
        }
    }
}

pub(crate) fn validate_pattern_literal(
    literal: &syn::ExprLit,
    nodes: &mut Vec<TermNode>,
    signs: &mut NegativeLiteralSpans,
) -> Result<TermLiteral, SyntaxError> {
    if !literal.attrs.is_empty() {
        return Err(unsupported_pattern(
            "pattern attributes are not supported",
            literal.span(),
        ));
    }
    let literal = match &literal.lit {
        syn::Lit::Int(integer)
            if crate::term::is_unsuffixed_integer(integer)
                && integer.base10_digits().starts_with('-')
                && crate::term::is_zero(integer) =>
        {
            return Err(unsupported_pattern(
                crate::term::NEGATIVE_ZERO,
                literal.span(),
            ));
        }
        // syn reads a negative literal pattern such as `-1` as one signed token.
        syn::Lit::Int(integer)
            if crate::term::is_unsuffixed_integer(integer)
                && integer.base10_digits().starts_with('-') =>
        {
            let (minus, digits) = signs
                .next()
                .unwrap_or_else(|| (integer.span(), integer.span()));
            TermLiteral::Integer(IntegerLiteral::negative(integer.clone(), minus, digits))
        }
        syn::Lit::Int(integer) if crate::term::is_unsuffixed_integer(integer) => {
            TermLiteral::Integer(IntegerLiteral::unsigned(integer.clone())?)
        }
        syn::Lit::Bool(boolean) => TermLiteral::Boolean(boolean.clone()),
        syn::Lit::Str(string) => TermLiteral::String(crate::term::string_literal(string)?),
        float
            if matches!(float, syn::Lit::Float(_)) || crate::term::is_float_suffixed_int(float) =>
        {
            // syn reads a negative literal pattern such as `-1.5` as one signed token;
            // its `-` span comes from the scan, in token order.
            let negative = match float {
                syn::Lit::Float(value) => value.base10_digits().starts_with('-'),
                syn::Lit::Int(value) => value.base10_digits().starts_with('-'),
                _ => false,
            };
            let sign = if negative { signs.next() } else { None };
            TermLiteral::Float(
                crate::term::float_literal_spanning(
                    float,
                    sign.map(|(minus, _)| minus),
                    sign.map(|(_, digits)| digits),
                )?
                .expect("a float literal pattern"),
            )
        }
        syn::Lit::Int(_) => {
            return Err(unsupported_pattern(
                "only unsuffixed Int (decimal, 0x hex, 0o octal, or 0b binary; optionally negative), Bool, String, and Float literals are term patterns",
                literal.span(),
            ));
        }
        other => return Err(crate::term::unsupported_literal(other)),
    };
    nodes.push(TermNode::Literal(literal.clone()));
    Ok(literal)
}

/// Refuses an alias that stands for a whole wrapped clause subject, which
/// reads its root as a subject's: the root is the matched constructor or
/// function, and each alternative of a root `A | B` is a whole subject.
fn reject_subject_root_alias(tree: &TermTree) -> Result<(), SyntaxError> {
    match tree {
        TermTree::As { binding, .. } => Err(SyntaxError::new(
            crate::SyntaxErrorKind::InvalidPatternAs {
                reason: format!(
                    "`{binding} @ pattern` cannot alias a whole rule subject: its root is the matched constructor or function; alias a subterm instead"
                ),
            },
            binding.span(),
        )),
        TermTree::Or { alternatives, .. } => {
            alternatives.iter().try_for_each(reject_subject_root_alias)
        }
        _ => Ok(()),
    }
}

fn term_pattern_bindings(
    term: &TermExpression,
    subject_root: bool,
) -> Result<Vec<Ident>, SyntaxError> {
    let mut bindings = Vec::new();
    // A subject's root path names the matched constructor or function; every
    // other bare reference and every `name @ pattern` alias binds, in
    // preorder. A readable value has no such root.
    for binding in crate::term::pattern_tree_binders(term.tree(), subject_root) {
        crate::parse::validate_authored_binder(&binding.to_string(), binding.span())?;
        push_unique_binding(&mut bindings, binding);
    }
    Ok(bindings)
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

/// Keys each application head, reference, and literal node of `nodes`, as
/// the next of its role, into `term_keys`.
pub(crate) fn allocate_term_node_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
    application_role: ProvenanceRole,
    reference_role: ProvenanceRole,
    literal_role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    for (index, node) in nodes.iter().enumerate() {
        let role = match node {
            TermNode::ApplicationHead(_) => application_role,
            TermNode::Reference(_) => reference_role,
            TermNode::Literal(_) => literal_role,
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_)
            | TermNode::Lexeme { .. }
            | TermNode::SortTest { .. }
            | TermNode::As { .. }
            | TermNode::Or(_)
            | TermNode::Matches(_)
            | TermNode::MatchesWildcard(_)
            | TermNode::Let { .. }
            | TermNode::Closure { .. }
            | TermNode::LetWildcard(_)
            | TermNode::Rewrite { .. } => continue,
        };
        term_keys.push_node(index, keys.key(role, node.range()?)?);
    }
    Ok(())
}

/// Keys each `_` of `tree` in preorder, into `term_keys`.
pub(crate) fn allocate_wildcard_keys(
    keys: &mut KeyAllocator,
    tree: &TermTree,
    term_keys: &mut TermKeys,
    role: ProvenanceRole,
) -> Result<(), SyntaxError> {
    let mut ranges = Vec::new();
    tree.wildcard_ranges_preorder(&mut ranges);
    for (index, range) in ranges.into_iter().enumerate() {
        term_keys.set_wildcard(index, keys.key(role, range)?);
    }
    Ok(())
}

/// Pushes a candidate for each application head and each reference of
/// `nodes` that is not one of `bindings`, keyed as its sentence keyed the
/// node: the first key of the node in `term_keys`.
pub(super) fn push_term_reference_candidates(
    candidates: &mut Vec<ReferenceCandidate<TermSymbolKind>>,
    nodes: &[TermNode],
    term_keys: &TermKeys,
    bindings: &[Ident],
) {
    for (index, node) in nodes.iter().enumerate() {
        let (path, kind) = match node {
            TermNode::ApplicationHead(path) => (path, TermSymbolKind::ApplicationHead),
            TermNode::Reference(path) => {
                if is_bound_path(path, bindings) {
                    continue;
                }
                (path, TermSymbolKind::Reference)
            }
            TermNode::Literal(_)
            | TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_)
            | TermNode::Lexeme { .. }
            | TermNode::SortTest { .. }
            | TermNode::As { .. }
            | TermNode::Or(_)
            | TermNode::Matches(_)
            | TermNode::MatchesWildcard(_)
            | TermNode::Let { .. }
            | TermNode::Closure { .. }
            | TermNode::LetWildcard(_)
            | TermNode::Rewrite { .. } => continue,
        };
        let key = term_keys
            .node(index)
            .first()
            .expect("a keyed sentence keys every application head and reference");
        candidates.push(ReferenceCandidate {
            key: key.clone(),
            path: path.clone(),
            kind,
        });
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

#[cfg(test)]
impl RulePattern {
    /// Records the keys of the pattern's paths and nodes, and of the record
    /// field names and wildcards of `tree`, the subject tree they index.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
        tree: &TermTree,
    ) -> Result<(), SyntaxError> {
        if let Self::TermMacro { term, .. } = self {
            // The whole pattern is keyed on the parameter, never on its term.
            assert!(term.keys().payload().is_none() && term.keys().term().is_none());
        }
        self.keys()
            .keyed_nodes(nodes, &self.path_ranges()?, self.nodes(), tree)
    }
}
