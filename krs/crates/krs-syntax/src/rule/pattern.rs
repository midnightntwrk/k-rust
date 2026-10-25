use krs_ir::ProvenanceKey;
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{Ident, Member, Pat, PatIdent, PatMacro, Path};

use crate::parse::{
    KeyAllocator, checked_ordinal, unsupported_rule_pattern as unsupported_pattern,
};
use crate::path::is_plain_path;
use crate::term::{TermKeys, allocate_record_field_keys, is_term_macro, unexpected_macro};
use crate::{
    CellTerm, IntegerLiteral, ProvenanceRole, ReferenceCandidate, SyntaxError, TermApplication,
    TermArguments, TermExpression, TermLiteral, TermNamedArgument, TermNode, TermSymbolKind,
    TermTree, TokenRange,
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

/// Parses one pattern with the spans of its negative literals.
pub(crate) fn parse_pattern_with_signs(
    input: syn::parse::ParseStream<'_>,
) -> syn::Result<(Pat, NegativeLiteralSpans)> {
    let start = input.cursor();
    // `A | B` alternatives (K's #Or, KF-030) may join whole subjects.
    let pattern = input.call(Pat::parse_multi)?;
    let end = input.cursor();
    let mut tokens = TokenStream::new();
    let mut cursor = start;
    while cursor != end {
        let Some((token, next)) = cursor.token_tree() else {
            break;
        };
        tokens.extend([token]);
        cursor = next;
    }
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

/// What a rule pattern's root is, which decides how the root reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PatternRoot {
    /// A fn's subject parameter: the root is the matched constructor or
    /// function.
    Subject,
    /// A readable `for Sort` clause's subject: the root is the matched
    /// constructor, a bare root identifier binds the subject, and an alias
    /// or island at the root stands as it does below a constructor.
    Clause,
    /// A readable record's value (a cell value, a list element, a
    /// computation item): not a rule subject, so the whole pattern, `|` and
    /// parentheses at its root included, reads as below a constructor.
    Value,
}

/// Parses a rule pattern whose root reads as `root` says. The native
/// grammar reads every pattern a `k::term!` payload reads, compiler-owned
/// islands included, so the wrapper is never needed around a pattern;
/// `k::rewrite!` stands only in a fn's subject, whose item decides whether
/// it is a single-body rule.
pub(super) fn parse_rule_pattern(
    pattern: Pat,
    root: PatternRoot,
    mut signs: NegativeLiteralSpans,
) -> Result<(RulePattern, TermTree), SyntaxError> {
    let root_identifier_is_binding = root != PatternRoot::Subject;
    let allow_rewrite = !root_identifier_is_binding;
    match pattern {
        Pat::Macro(macro_pattern)
            if !root_identifier_is_binding || is_term_macro(&macro_pattern.mac.path) =>
        {
            if crate::term::is_sort_test_macro(&macro_pattern.mac.path) {
                return Err(crate::term::matched_sort_test(&macro_pattern.mac.path));
            }
            if crate::term::is_matches_macro(&macro_pattern.mac.path)
                || crate::term::is_std_matches(&macro_pattern.mac.path)
            {
                return Err(crate::term::matched_matches(&macro_pattern.mac.path));
            }
            if !is_term_macro(&macro_pattern.mac.path) {
                return Err(subject_root_macro(&macro_pattern.mac.path));
            }
            let term = TermExpression::parse_pattern_tokens(crate::parse::strip_trailing_comma(
                macro_pattern.mac.tokens.clone(),
            ))?;
            // A readable value stands below the rule's subject, so `|` and
            // an alias at its root read as they do below a constructor.
            if let TermTree::As { binding, .. } = term.tree()
                && root != PatternRoot::Value
            {
                return Err(SyntaxError::new(
                    crate::SyntaxErrorKind::InvalidPatternAs {
                        reason: format!(
                            "`{binding} @ pattern` cannot alias a whole rule subject: its root is the matched constructor or function; alias a subterm instead"
                        ),
                    },
                    binding.span(),
                ));
            }
            if let TermTree::Or { range, .. } = term.tree()
                && root != PatternRoot::Value
            {
                return Err(SyntaxError::new(
                    crate::SyntaxErrorKind::InvalidPatternOr {
                        reason: "`|` cannot join whole `k::term!` subjects: the root is the matched constructor or function; put the alternatives inside its arguments".to_owned(),
                    },
                    range.first(),
                ));
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
            let mut paths = Vec::new();
            let mut bindings = Vec::new();
            let mut nodes = Vec::new();
            let mut validate = |is_root| {
                validate_native_pattern(
                    &pattern,
                    is_root,
                    allow_rewrite,
                    &mut paths,
                    &mut bindings,
                    &mut nodes,
                    &mut signs,
                )
            };
            let tree = match (root, &pattern) {
                (PatternRoot::Clause, Pat::Ident(identifier)) if identifier.subpat.is_none() => {
                    validate_native_binding(identifier, &mut paths, &mut bindings, &mut nodes)?
                }
                // A readable value is not a rule subject, so its root,
                // alternatives and parentheses included, reads as a pattern
                // below a constructor: a bare name binds, and
                // `name @ pattern`, `_`, or an island stands as it does there.
                // At a clause's root, `name @ pattern` or an island stands as
                // it does below a constructor too.
                (PatternRoot::Value, _) | (PatternRoot::Clause, Pat::Ident(_) | Pat::Macro(_)) => {
                    validate(false)?
                }
                _ => validate(true)?,
            };
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

#[expect(
    clippy::too_many_lines,
    reason = "Exhaustive validation over syn's closed pattern variants."
)]
fn validate_native_pattern(
    pattern: &Pat,
    is_root: bool,
    allow_rewrite: bool,
    paths: &mut Vec<Path>,
    bindings: &mut Vec<Ident>,
    nodes: &mut Vec<TermNode>,
    signs: &mut NegativeLiteralSpans,
) -> Result<TermTree, SyntaxError> {
    match pattern {
        Pat::Ident(PatIdent {
            ident,
            subpat: Some(_),
            ..
        }) if is_root => Err(SyntaxError::new(
            crate::SyntaxErrorKind::InvalidPatternAs {
                reason: format!(
                    "`{ident} @ pattern` cannot alias a whole rule subject: its root is the matched constructor or function; alias a subterm instead"
                ),
            },
            ident.span(),
        )),
        Pat::Ident(
            identifier @ PatIdent {
                subpat: Some((_, subpattern)),
                ..
            },
        ) => {
            if identifier.by_ref.is_none() && identifier.mutability.is_none() {
                crate::parse::validate_authored_binder(
                    &identifier.ident.to_string(),
                    identifier.ident.span(),
                )?;
                push_unique_binding(bindings, identifier.ident.clone());
            }
            crate::term::validate_pattern_as(identifier, subpattern, nodes, |subpattern, nodes| {
                validate_native_pattern(
                    subpattern,
                    false,
                    allow_rewrite,
                    paths,
                    bindings,
                    nodes,
                    signs,
                )
            })
        }
        // `A | B | ..` is K's #Or (KF-030). At a subject's root each
        // alternative is a whole subject, so a bare identifier names a unit
        // constructor there.
        Pat::Or(or) => {
            let (tree, names) =
                crate::term::validate_pattern_or(or, nodes, |alternative, nodes| {
                    let mut alternative_bindings = Vec::new();
                    let tree = validate_native_pattern(
                        alternative,
                        is_root,
                        allow_rewrite,
                        paths,
                        &mut alternative_bindings,
                        nodes,
                        signs,
                    )?;
                    Ok((tree, alternative_bindings))
                })?;
            for name in names {
                push_unique_binding(bindings, name);
            }
            Ok(tree)
        }
        Pat::Ident(identifier) if is_root => validate_root_identifier(identifier, paths, nodes),
        Pat::Ident(identifier) => validate_native_binding(identifier, paths, bindings, nodes),
        Pat::Path(path) => {
            if path.qself.is_some() || !path.attrs.is_empty() || !is_plain_path(&path.path) {
                return Err(unsupported_pattern(
                    "expected a plain constructor path",
                    path.span(),
                ));
            }
            if path.path.leading_colon.is_none()
                && let Some(constant) = crate::term::float_constant_path(&path.path)
            {
                let literal =
                    TermLiteral::Float(crate::term::float_constant(&path.path, constant?, None)?);
                nodes.push(TermNode::Literal(literal.clone()));
                return Ok(TermTree::Literal(literal));
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
                    allow_rewrite,
                    paths,
                    bindings,
                    nodes,
                    signs,
                )?);
            }
            Ok(TermTree::Application(TermApplication {
                head: tuple.path.clone(),
                arguments: TermArguments::Positional(arguments),
                instance: Vec::new(),
                notation: false,
                update: None,
                open: false,
            }))
        }
        // `[p1, .., pn, rest @ ..]` is one level of list notation.
        Pat::Slice(slice) => {
            let (head, elements) = crate::list_notation::pattern_level(slice)?;
            paths.push(head.clone());
            nodes.push(TermNode::ApplicationHead(head.clone()));
            let mut arguments = Vec::with_capacity(elements.len());
            for element in &elements {
                arguments.push(validate_native_pattern(
                    element,
                    false,
                    allow_rewrite,
                    paths,
                    bindings,
                    nodes,
                    signs,
                )?);
            }
            Ok(TermTree::Application(TermApplication {
                head,
                arguments: TermArguments::Positional(arguments),
                instance: Vec::new(),
                notation: true,
                update: None,
                open: false,
            }))
        }
        Pat::Struct(record) => {
            if record.qself.is_some() || !record.attrs.is_empty() || !is_plain_path(&record.path) {
                return Err(unsupported_pattern(
                    "expected a plain record constructor path",
                    record.span(),
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
                        allow_rewrite,
                        paths,
                        bindings,
                        nodes,
                        signs,
                    )?,
                });
            }
            Ok(TermTree::Application(TermApplication {
                head: record.path.clone(),
                arguments: TermArguments::Named(arguments),
                instance: Vec::new(),
                notation: false,
                update: None,
                open: record.rest.is_some(),
            }))
        }
        Pat::Paren(paren) => validate_native_pattern(
            &paren.pat,
            is_root,
            allow_rewrite,
            paths,
            bindings,
            nodes,
            signs,
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
            let literal = validate_pattern_literal(literal, nodes, signs)?;
            Ok(TermTree::Literal(literal))
        }
        Pat::Macro(macro_pattern) if crate::term::is_sort_test_macro(&macro_pattern.mac.path) => {
            Err(crate::term::matched_sort_test(&macro_pattern.mac.path))
        }
        Pat::Macro(macro_pattern)
            if crate::term::is_matches_macro(&macro_pattern.mac.path)
                || crate::term::is_std_matches(&macro_pattern.mac.path) =>
        {
            Err(crate::term::matched_matches(&macro_pattern.mac.path))
        }
        Pat::Macro(macro_pattern)
            if crate::term::is_rewrite_macro(&macro_pattern.mac.path) && !allow_rewrite =>
        {
            Err(crate::term::local_rewrite_error(
                crate::term::REWRITE_IN_READABLE.to_owned(),
                macro_pattern.mac.path.span(),
            ))
        }
        Pat::Macro(macro_pattern) if crate::rule::is_bits_macro(&macro_pattern.mac.path) => Err(
            crate::rule::misplaced_bit_template(macro_pattern.mac.path.span()),
        ),
        // A rule subject's root is the matched constructor or function.
        Pat::Macro(macro_pattern) if is_root => Err(subject_root_macro(&macro_pattern.mac.path)),
        // `k::fragment![Group { .. }]` is the group's cell term: its children
        // are patterns of this grammar.
        Pat::Macro(macro_pattern) if crate::term::is_fragment_macro(&macro_pattern.mac.path) => {
            validate_native_cell_pattern(
                macro_pattern,
                allow_rewrite,
                paths,
                bindings,
                nodes,
                signs,
            )
        }
        // Every other island builds the tree `k::term!` builds for it.
        Pat::Macro(macro_pattern) => {
            let start = nodes.len();
            let mut symbols = Vec::new();
            let tree =
                crate::term::validate_pattern_island(macro_pattern, signs, &mut symbols, nodes)?;
            paths.extend(symbols.iter().map(|symbol| symbol.path().clone()));
            // Its bare names bind as in a `k::term!` subject; a rewrite's
            // right side only uses them.
            let (left, _) = crate::term::split_rewrite_images(&nodes[start..]);
            for binding in left.into_iter().filter_map(|node| match node {
                TermNode::Reference(path) => crate::path::pattern_binder(path).cloned(),
                TermNode::As { binding, .. } => Some(binding.clone()),
                _ => None,
            }) {
                crate::parse::validate_authored_binder(&binding.to_string(), binding.span())?;
                push_unique_binding(bindings, binding);
            }
            Ok(tree)
        }
        _ => Err(unsupported_pattern(
            "expected a named constructor with plain bindings, literals, or `_` arguments",
            pattern.span(),
        )),
    }
}

/// `k::fragment![Group { f: p, .. }]` in a native pattern: the twin of the
/// term grammar's cell pattern, whose child values are native patterns. `..`
/// leaves the children it does not name unconstrained; without it every
/// child must be named, which semantic lowering checks.
fn validate_native_cell_pattern(
    value: &syn::ExprMacro,
    allow_rewrite: bool,
    paths: &mut Vec<Path>,
    bindings: &mut Vec<Ident>,
    nodes: &mut Vec<TermNode>,
    signs: &mut NegativeLiteralSpans,
) -> Result<TermTree, SyntaxError> {
    let complete = || "complete cell terms require unadorned named fields";
    if !value.attrs.is_empty() {
        return Err(unsupported_pattern(
            "pattern attributes are not supported",
            value.span(),
        ));
    }
    let Pat::Struct(record) =
        Pat::parse_multi.parse2(crate::parse::strip_trailing_comma(value.mac.tokens.clone()))?
    else {
        return Err(unsupported_pattern(
            "fragment! requires one nominal cell record",
            value.mac.tokens.span(),
        ));
    };
    if record.qself.is_some() || !record.attrs.is_empty() || !is_plain_path(&record.path) {
        return Err(unsupported_pattern(
            "expected a plain cell record path",
            record.span(),
        ));
    }
    if let Some(rest) = &record.rest
        && !rest.attrs.is_empty()
    {
        return Err(unsupported_pattern(
            "pattern attributes are not supported",
            rest.span(),
        ));
    }
    let open = record.rest.is_some();
    paths.push(record.path.clone());
    nodes.push(TermNode::ApplicationHead(record.path.clone()));
    let mut fields = Vec::with_capacity(record.fields.len());
    for field in &record.fields {
        let Member::Named(name) = &field.member else {
            return Err(unsupported_pattern(complete(), field.span()));
        };
        if !field.attrs.is_empty() {
            return Err(unsupported_pattern(complete(), field.span()));
        }
        fields.push(TermNamedArgument {
            name: name.clone(),
            value: validate_native_pattern(
                &field.pat,
                false,
                allow_rewrite,
                paths,
                bindings,
                nodes,
                signs,
            )?,
        });
    }
    if fields.is_empty() && !open {
        return Err(unsupported_pattern(
            "complete cell terms require at least one child field",
            record.span(),
        ));
    }
    Ok(TermTree::Cell(CellTerm {
        range: TokenRange::for_tokens(value)?,
        owner: record.path,
        fields,
        open,
        update: None,
    }))
}

/// The error for a macro at the root of a fn's subject. A compiler-owned
/// island stands below the root, which is the constructor or function the
/// rule matches; any other macro is not a pattern.
fn subject_root_macro(path: &Path) -> SyntaxError {
    if crate::term::is_rewrite_macro(path) {
        return unsupported_pattern(
            "a whole-subject `k::rewrite!(from => to)` is an ordinary rule: write `from` as the subject and `to` as the result, or mark the change below the subject's root",
            path.span(),
        );
    }
    if crate::term::is_island_macro(path) {
        return unsupported_pattern(
            "a rule subject's root is the constructor or function the rule matches, so a compiler-owned island stands below it, as in `F(k::fragment![Group { .. }])` or `F(k::bytes!(b\"..\"))`",
            path.span(),
        );
    }
    unexpected_macro(path)
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

fn validate_binding(identifier: &PatIdent, bindings: &mut Vec<Ident>) -> Result<(), SyntaxError> {
    if identifier.attrs.is_empty()
        && identifier.by_ref.is_none()
        && identifier.mutability.is_none()
        && identifier.subpat.is_none()
    {
        // A name spelled as a constant refers to one and binds nothing.
        if crate::path::is_constant_name(&identifier.ident) {
            return Ok(());
        }
        crate::parse::validate_authored_binder(
            &identifier.ident.to_string(),
            identifier.ident.span(),
        )?;
        push_unique_binding(bindings, identifier.ident.clone());
        Ok(())
    } else {
        Err(unsupported_pattern(
            "constructor arguments allow only plain identifier bindings",
            identifier.span(),
        ))
    }
}

fn term_pattern_bindings(
    term: &TermExpression,
    subject_root: bool,
) -> Result<Vec<Ident>, SyntaxError> {
    let mut bindings = Vec::new();
    // A subject's root path names the matched constructor or function; every
    // later bare reference and every `name @ pattern` alias binds, in
    // preorder. A readable value has no such root.
    let mut root = subject_root;
    // Only the left image binds (KF-011): the right side of a `k::rewrite!`
    // uses the subject's bindings.
    let (left, _) = crate::term::split_rewrite_images(term.nodes());
    for binding in left.into_iter().filter_map(|node| match node {
        TermNode::ApplicationHead(_) | TermNode::Reference(_) if std::mem::take(&mut root) => None,
        TermNode::Reference(path) => crate::path::pattern_binder(path).cloned(),
        TermNode::As { binding, .. } => Some(binding.clone()),
        _ => None,
    }) {
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
