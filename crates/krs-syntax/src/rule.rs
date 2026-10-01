use proc_macro2::TokenStream;
use proc_macro2::TokenTree;
use quote::{ToTokens, quote};
use syn::ext::IdentExt;
use syn::parse::discouraged::Speculative;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, ExprCall, FnArg, GenericArgument, Ident, ItemFn, ItemUse, Member, Meta, Pat,
    PatIdent, PatMacro, Path, PathArguments, ReturnType, Stmt, Token, TraitBoundModifier, Type,
    TypeParamBound, UseTree, braced, bracketed,
};

use krs_ir::ProvenanceKey;

use crate::ReferenceCandidate;
use crate::attribute::is_plain_path;
use crate::parse::{
    KrsSyntax, checked_ordinal, unsupported_rule_pattern as unsupported_pattern,
    unsupported_rule_signature as unsupported_signature,
};
use crate::term::{is_term_macro, push_record_field_anchors, unexpected_macro};
use crate::{
    ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TermApplication, TermArguments,
    TermExpression, TermLiteral, TermNamedArgument, TermNode, TermSymbolKind, TermTree, TokenRange,
};

/// A validated `Term<SortPath>` or `Term<dyn SortPath>` type reference.
#[derive(Clone, Debug)]
pub struct TermSort {
    ty: Type,
    sort: Path,
    dynamic: bool,
}

impl TermSort {
    /// Returns the complete authored `Term<...>` type.
    #[must_use]
    pub const fn ty(&self) -> &Type {
        &self.ty
    }

    /// Returns the Rust-resolved sort path inside `Term`.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// Returns whether the sort was written as a `dyn` trait object.
    #[must_use]
    pub const fn is_dynamic(&self) -> bool {
        self.dynamic
    }

    /// Returns the token-stream text of the sort path, such as `model :: Expr`,
    /// which descriptors carry as the sort's `authored_path`.
    #[must_use]
    pub fn sort_token_text(&self) -> String {
        self.sort.to_token_stream().to_string()
    }
}

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

    fn path_ranges(&self) -> Result<Vec<TokenRange>, SyntaxError> {
        match self {
            Self::Native { paths, .. } => paths.iter().map(TokenRange::for_tokens).collect(),
            Self::TermMacro { term, .. } => term
                .symbols()
                .iter()
                .map(|symbol| TokenRange::for_tokens(symbol.path()))
                .collect(),
        }
    }

    fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Native { pattern, .. } => TokenRange::for_tokens(pattern),
            Self::TermMacro { pattern, .. } => TokenRange::for_tokens(pattern),
        }
    }
}

/// The one typed subject parameter of a rule clause.
#[derive(Clone, Debug)]
pub struct RuleParameter {
    /// Validated named-constructor subject pattern.
    pub pattern: RulePattern,
    /// Rust-resolved term sort.
    pub term_sort: TermSort,
}

/// One parsed object-language Boolean condition from `#[k::requires(...)]`.
#[derive(Clone, Debug)]
pub struct RuleCondition {
    term: TermExpression,
}

impl RuleCondition {
    /// Returns the complete structured condition term.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Returns complete and nested parser-owned condition anchors.
    ///
    /// # Errors
    ///
    /// Returns endpoint or occurrence-overflow errors only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::RuleRequires,
            0,
            TokenRange::for_tokens(self.term.expression())?,
        )];
        for (ordinal, symbol) in self.term.symbols().iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleRequiresPath,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::RuleRequiresPath,
                    symbol.path().span(),
                )?,
                TokenRange::for_tokens(symbol.path())?,
            ));
        }
        push_term_node_anchors(
            &mut anchors,
            self.term.nodes(),
            ProvenanceRole::RuleRequiresApplicationHead,
            ProvenanceRole::RuleRequiresReference,
            ProvenanceRole::RuleRequiresLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            self.term.tree(),
            ProvenanceRole::RuleRequiresRecordFieldName,
        )?;
        Ok(anchors)
    }

    /// Returns rustc-resolvable condition references, excluding pre-bindings.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error for pathological inputs.
    pub fn reference_candidates(
        &self,
        bindings: &[Ident],
    ) -> Result<Vec<ReferenceCandidate<TermSymbolKind>>, SyntaxError> {
        let mut candidates = Vec::new();
        push_term_reference_candidates(
            &mut candidates,
            self.term.nodes(),
            bindings,
            ProvenanceRole::RuleRequiresApplicationHead,
            ProvenanceRole::RuleRequiresReference,
        )?;
        Ok(candidates)
    }
}

/// Validated one-clause rule function.
#[derive(Clone, Debug)]
pub struct RuleItem {
    item: ItemFn,
    parameter: RuleParameter,
    result_sort: TermSort,
    result: TermExpression,
    subject_tree: TermTree,
    requires: Option<RuleCondition>,
}

/// One explicit binding-sort refinement after a readable rule clause.
#[derive(Clone, Debug)]
pub struct RuleNarrowing {
    binding: Ident,
    sort: Path,
}

/// Right-hand shape of one computation-head clause.
#[derive(Clone, Debug)]
pub enum RuleHeadResult {
    /// One ordinary replacement term.
    Replace(Box<TermExpression>),
    /// Ordered items from `k![...]`, spliced before the preserved tail.
    Splice {
        /// Complete `k![...]` expression range.
        range: TokenRange,
        /// Authored splice items.
        items: Vec<TermExpression>,
    },
    /// Empty tuple `()`, erasing the matched head.
    Erase(TokenRange),
}

impl RuleHeadResult {
    /// Returns ordinary replacement, splice, or erasure meaning.
    #[must_use]
    pub const fn replacement(&self) -> Option<&TermExpression> {
        match self {
            Self::Replace(term) => Some(term),
            Self::Splice { .. } | Self::Erase(_) => None,
        }
    }

    /// Returns a deterministic source-like spelling.
    #[must_use]
    pub fn spelling(&self) -> String {
        match self {
            Self::Replace(term) => term.spelling(),
            Self::Splice { items, .. } => format!(
                "k![{}]",
                items
                    .iter()
                    .map(TermExpression::spelling)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Erase(_) => "()".to_owned(),
        }
    }

    fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Replace(term) => TokenRange::for_tokens(term.expression()),
            Self::Splice { range, .. } | Self::Erase(range) => Ok(*range),
        }
    }
}

/// One explicit gradual extra-cell clause in a readable rule.
#[derive(Clone, Debug)]
pub enum RuleExtra {
    /// Failable preserved map binding read.
    HaveMap {
        /// Named fixed cell.
        cell: Ident,
        /// Required key term.
        key: Box<TermExpression>,
        /// Value binder introduced only when the map item is present.
        value: Ident,
    },
    /// Simultaneous map update.
    UpdateMap {
        /// Named fixed cell and implicit pre-state map binder.
        cell: Ident,
        /// Authored whole-map binding from the subject record.
        base: Ident,
        /// Complete ordinary three-argument update term.
        update: Box<TermExpression>,
    },
    /// Simultaneous exact rewrite of one ordinary fixed leaf cell.
    RewriteCell {
        /// Named fixed cell.
        cell: Ident,
        /// Complete constructor or binding pattern before the rewrite.
        before: Box<RulePattern>,
        /// Parser-owned subject tree for descriptor expansion and provenance.
        before_tree: Box<TermTree>,
        /// Complete replacement term after the rewrite.
        after: Box<TermExpression>,
    },
}

impl RuleExtra {
    /// Returns the named fixed cell.
    #[must_use]
    pub const fn cell(&self) -> &Ident {
        match self {
            Self::HaveMap { cell, .. }
            | Self::UpdateMap { cell, .. }
            | Self::RewriteCell { cell, .. } => cell,
        }
    }
}

impl RuleNarrowing {
    /// Returns the subject binding being refined.
    #[must_use]
    pub const fn binding(&self) -> &Ident {
        &self.binding
    }

    /// Returns the exact authored sort path.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }
}

/// Authored component ranges of one readable rule clause.
#[derive(Clone, Copy, Debug)]
pub struct RuleClauseLayout {
    /// The clause name identifier, excluding the following colon.
    pub label: TokenRange,
    /// The term pattern or complete brace-delimited subject record.
    pub pattern: TokenRange,
    /// The result expression or complete brace-delimited result record.
    pub result: TokenRange,
    /// The tokens after `where`, excluding the terminating semicolon.
    pub conditions: Option<TokenRange>,
}

/// One named `pattern => result` clause in a readable rule block.
#[derive(Clone, Debug)]
pub struct RuleClause {
    rule: RuleItem,
    attribute: crate::RuleAttribute,
    narrowings: Vec<RuleNarrowing>,
    head_result: RuleHeadResult,
    extras: Vec<RuleExtra>,
    bindings: Vec<Ident>,
    computation_cell: Option<Ident>,
    source_range: TokenRange,
    layout: RuleClauseLayout,
}

impl RuleClause {
    /// Returns the ordinary structured-rule view shared with `#[k::rule]`.
    #[must_use]
    pub const fn rule(&self) -> &RuleItem {
        &self.rule
    }

    /// Returns the optional explicit rule-label metadata.
    #[must_use]
    pub const fn attribute(&self) -> &crate::RuleAttribute {
        &self.attribute
    }

    /// Returns binding refinements in authored order.
    #[must_use]
    pub fn narrowings(&self) -> &[RuleNarrowing] {
        &self.narrowings
    }

    /// Returns replacement, splice, or erasure head meaning.
    #[must_use]
    pub const fn head_result(&self) -> &RuleHeadResult {
        &self.head_result
    }

    /// Returns explicit non-computation-cell clauses.
    #[must_use]
    pub fn extras(&self) -> &[RuleExtra] {
        &self.extras
    }

    /// Returns all head, map-read, and implicit update bindings in introduction order.
    #[must_use]
    pub fn bindings(&self) -> &[Ident] {
        &self.bindings
    }

    /// Returns the authored computation-cell field for a cell-record clause.
    #[must_use]
    pub const fn computation_cell(&self) -> Option<&Ident> {
        self.computation_cell.as_ref()
    }

    /// Returns the complete authored clause range, including attributes and
    /// the terminating semicolon.
    #[must_use]
    pub const fn source_range(&self) -> TokenRange {
        self.source_range
    }

    /// Returns the authored label, pattern, result, and optional condition ranges.
    ///
    /// Record ranges include their braces.
    /// Condition ranges exclude `where` and the terminating semicolon.
    #[must_use]
    pub const fn layout(&self) -> RuleClauseLayout {
        self.layout
    }

    /// Returns the exact descriptor provenance for the completed head rule.
    ///
    /// # Errors
    ///
    /// Returns endpoint or provenance-ordinal overflow errors.
    #[allow(clippy::too_many_lines)] // One ordered pass retains exact aggregate term ordinals.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.rule.full_provenance()?;
        if self.attribute.label().is_none() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleLabel,
                0,
                TokenRange::for_tokens(&self.rule.item.sig.ident)?,
            ));
        }
        anchors.retain(|anchor| {
            !matches!(
                anchor.role(),
                ProvenanceRole::RuleResult
                    | ProvenanceRole::RuleRightPath
                    | ProvenanceRole::RuleRightApplicationHead
                    | ProvenanceRole::RuleRightReference
                    | ProvenanceRole::RuleRightLiteral
                    | ProvenanceRole::RuleRightRecordFieldName
            )
        });
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::RuleResult,
            0,
            self.head_result.range()?,
        ));
        let mut right = RuleTermCounters::default();
        match &self.head_result {
            RuleHeadResult::Replace(term) => {
                append_rule_term_anchors(&mut anchors, term, RuleTermSide::Right, &mut right)?;
            }
            RuleHeadResult::Splice { range, items } => {
                anchors.push(ProvenanceAnchor::new(
                    ProvenanceRole::RuleRightKSequencePayload,
                    0,
                    *range,
                ));
                for (ordinal, item) in items.iter().enumerate() {
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightKSequenceItem,
                        checked_ordinal(
                            ordinal,
                            ProvenanceRole::RuleRightKSequenceItem,
                            item.expression().span(),
                        )?,
                        TokenRange::for_tokens(item.expression())?,
                    ));
                    append_rule_term_anchors(&mut anchors, item, RuleTermSide::Right, &mut right)?;
                }
            }
            RuleHeadResult::Erase(_) => {}
        }

        let mut left = RuleTermCounters::from_rule_pattern(self.rule.parameter().pattern.nodes());
        let mut subject_fields = Vec::new();
        self.rule
            .subject_tree()
            .record_field_names_preorder(&mut subject_fields);
        left.field = subject_fields.len();
        let mut have_cell = 0_usize;
        let mut update_cell = 0_usize;
        for extra in &self.extras {
            match extra {
                RuleExtra::HaveMap { cell, key, value } => {
                    let ordinal = checked_ordinal(
                        have_cell,
                        ProvenanceRole::RuleLeftCellsField,
                        cell.span(),
                    )?;
                    have_cell += 1;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleLeftCellsField,
                        ordinal,
                        TokenRange::for_tokens(cell)?,
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleLeftMapKey,
                        ordinal,
                        TokenRange::for_tokens(key.expression())?,
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleLeftMapValue,
                        ordinal,
                        TokenRange::for_tokens(value)?,
                    ));
                    append_rule_term_anchors(&mut anchors, key, RuleTermSide::Left, &mut left)?;
                }
                RuleExtra::UpdateMap { cell, update, .. } => {
                    let [base, key, value] = map_update_arguments(update);
                    let ordinal = checked_ordinal(
                        update_cell,
                        ProvenanceRole::RuleRightCellsField,
                        cell.span(),
                    )?;
                    update_cell += 1;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightCellsField,
                        ordinal,
                        TokenRange::for_tokens(cell)?,
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightMapUpdateBase,
                        ordinal,
                        TokenRange::for_tokens(base)?,
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightMapKey,
                        ordinal,
                        TokenRange::for_tokens(key)?,
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightMapValue,
                        ordinal,
                        TokenRange::for_tokens(value)?,
                    ));
                    append_rule_term_anchors(
                        &mut anchors,
                        update,
                        RuleTermSide::Right,
                        &mut right,
                    )?;
                }
                RuleExtra::RewriteCell {
                    cell,
                    before,
                    before_tree,
                    after,
                } => {
                    let left_ordinal = checked_ordinal(
                        have_cell,
                        ProvenanceRole::RuleLeftCellsField,
                        cell.span(),
                    )?;
                    have_cell += 1;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleLeftCellsField,
                        left_ordinal,
                        TokenRange::for_tokens(cell)?,
                    ));
                    append_rule_pattern_anchors(&mut anchors, before, before_tree, &mut left)?;

                    let right_ordinal = checked_ordinal(
                        update_cell,
                        ProvenanceRole::RuleRightCellsField,
                        cell.span(),
                    )?;
                    update_cell += 1;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::RuleRightCellsField,
                        right_ordinal,
                        TokenRange::for_tokens(cell)?,
                    ));
                    append_rule_term_anchors(&mut anchors, after, RuleTermSide::Right, &mut right)?;
                }
            }
        }
        for (ordinal, narrowing) in self.narrowings.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleBindingType,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::RuleBindingType,
                    narrowing.sort.span(),
                )?,
                TokenRange::for_tokens(&narrowing.sort)?,
            ));
        }
        Ok(anchors)
    }
}

fn append_rule_pattern_anchors(
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
enum RuleTermSide {
    Left,
    Right,
}

#[derive(Default)]
struct RuleTermCounters {
    path: usize,
    application: usize,
    reference: usize,
    literal: usize,
    field: usize,
}

impl RuleTermCounters {
    fn from_rule_pattern(nodes: &[TermNode]) -> Self {
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

fn append_rule_term_anchors(
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

/// One block-local enum glob import consumed by `rules!` resolution.
#[derive(Clone, Debug)]
pub struct RuleImport {
    item: ItemUse,
    owner: Path,
    variant: Option<Ident>,
}

impl RuleImport {
    /// Returns the complete Rust `use Enum::*;` item.
    #[must_use]
    pub const fn item(&self) -> &ItemUse {
        &self.item
    }

    /// Returns the enum owner used to qualify unqualified clause heads.
    #[must_use]
    pub const fn owner(&self) -> &Path {
        &self.owner
    }

    /// Returns the one imported variant, or `None` for an enum glob.
    #[must_use]
    pub const fn variant(&self) -> Option<&Ident> {
        self.variant.as_ref()
    }
}

/// A readable family of independently named ordinary term rules.
#[derive(Clone, Debug)]
pub struct RuleBlock {
    sort: TermSort,
    configuration: bool,
    imports: Vec<RuleImport>,
    clauses: Vec<RuleClause>,
}

impl RuleBlock {
    /// Returns the alias-typed subject and result sort shared by every clause.
    #[must_use]
    pub const fn sort(&self) -> &TermSort {
        &self.sort
    }

    /// Returns whether the header names a fixed configuration rather than a k-head sort.
    #[must_use]
    pub const fn is_configuration(&self) -> bool {
        self.configuration
    }

    /// Returns block-local enum imports in authored order.
    #[must_use]
    pub fn imports(&self) -> &[RuleImport] {
        &self.imports
    }

    /// Returns independent clauses in authored order. Their order has no
    /// semantic priority.
    #[must_use]
    pub fn clauses(&self) -> &[RuleClause] {
        &self.clauses
    }

    #[allow(clippy::too_many_lines)] // One linear parser keeps clause diagnostics at authored tokens.
    fn from_stream(input: ParseStream<'_>) -> syn::Result<Self> {
        input.parse::<Token![for]>()?;
        let sort_type: Type = input.parse()?;
        let sort = parse_readable_sort(sort_type.clone())?;
        if input.peek(Token![in]) {
            return Err(input.error(
                "`for Sort in cell` is a control-flow rule surface and is not implemented yet",
            ));
        }
        input.parse::<Token![;]>()?;

        let mut imports = Vec::new();
        while input.peek(Token![use]) {
            let item: ItemUse = input.parse()?;
            let (owner, variant) = enum_glob_owner(&item)?;
            if !imports.is_empty() {
                return Err(syn::Error::new(
                    item.span(),
                    "a readable term-rule block accepts exactly one enum glob import",
                ));
            }
            imports.push(RuleImport {
                item,
                owner,
                variant,
            });
        }

        let mut clauses = Vec::new();
        let mut configuration = None;
        while !input.is_empty() {
            let clause_start = input.cursor().span();
            let attributes = input.call(Attribute::parse_outer)?;
            let name = input.call(Ident::parse_any)?;
            if clauses
                .iter()
                .any(|clause: &RuleClause| clause.rule.item.sig.ident.unraw() == name.unraw())
            {
                return Err(syn::Error::new(
                    name.span(),
                    format!("duplicate readable rule clause `{}`", name.unraw()),
                ));
            }
            input.parse::<Token![:]>()?;
            let machine_clause = input.peek(syn::token::Brace);
            if let Some(expected) = configuration {
                if expected != machine_clause {
                    return Err(syn::Error::new(
                        name.span(),
                        "a readable rule block cannot mix term clauses and cell-record clauses",
                    ));
                }
            } else {
                configuration = Some(machine_clause);
            }
            if machine_clause {
                clauses.push(parse_machine_clause(
                    input,
                    attributes,
                    &name,
                    &sort_type,
                    clause_start,
                )?);
                continue;
            }
            let pattern = input.call(Pat::parse_single)?;
            input.parse::<Token![=>]>()?;
            let result: Expr = input.parse()?;
            let head_result = parse_head_result(result.clone())?;
            let mut layout = RuleClauseLayout {
                label: TokenRange::for_tokens(&name)?,
                pattern: TokenRange::for_tokens(&pattern)?,
                result: TokenRange::for_tokens(&result)?,
                conditions: None,
            };

            let mut narrowings = Vec::new();
            let mut extras = Vec::new();
            if input.peek(Token![where]) {
                input.parse::<Token![where]>()?;
                layout.conditions = Some(condition_token_range(input)?);
                loop {
                    let first = input.call(Ident::parse_any)?;
                    match first.unraw().to_string().as_str() {
                        "have" => extras.push(parse_have_extra(input)?),
                        "update" => extras.push(parse_update_extra(input)?),
                        _ => {
                            let binding = first;
                            input.parse::<Token![:]>()?;
                            let sort: Path = input.parse()?;
                            if !is_plain_path(&sort) {
                                return Err(syn::Error::new(
                                    sort.span(),
                                    "a rule narrowing requires a plain object-sort path",
                                ));
                            }
                            if narrowings.iter().any(|existing: &RuleNarrowing| {
                                existing.binding.unraw() == binding.unraw()
                            }) {
                                return Err(syn::Error::new(
                                    binding.span(),
                                    format!(
                                        "duplicate narrowing for binding `{}`",
                                        binding.unraw()
                                    ),
                                ));
                            }
                            narrowings.push(RuleNarrowing { binding, sort });
                        }
                    }
                    if !input.peek(Token![,]) {
                        break;
                    }
                    input.parse::<Token![,]>()?;
                    if input.peek(Token![;]) {
                        return Err(input.error("expected a binding refinement after `,`"));
                    }
                }
            }
            let semicolon = input.parse::<Token![;]>()?;

            let (attribute, retained) = take_rule_clause_attribute(attributes)?;
            let placeholder = match &head_result {
                RuleHeadResult::Replace(_) => result,
                RuleHeadResult::Splice { .. } | RuleHeadResult::Erase(_) => syn::parse_quote!(true),
            };
            let item: ItemFn = syn::parse2(quote! {
                #(#retained)*
                pub fn #name(#pattern: #sort_type) -> #sort_type { #placeholder }
            })?;
            let rule = RuleItem::from_readable_item(item)?;
            let mut bindings = rule.parameter.pattern.bindings().to_vec();
            for extra in &extras {
                let introduced = match extra {
                    RuleExtra::HaveMap { value, .. } => value,
                    RuleExtra::UpdateMap { cell, .. } => cell,
                    RuleExtra::RewriteCell { .. } => {
                        unreachable!("term-table extras cannot rewrite ordinary cells")
                    }
                };
                if bindings
                    .iter()
                    .any(|binding| binding.unraw() == introduced.unraw())
                {
                    return Err(syn::Error::new(
                        introduced.span(),
                        format!("duplicate readable rule binding `{}`", introduced.unraw()),
                    ));
                }
                bindings.push(introduced.clone());
            }
            let mut mentioned_cells = Vec::<Ident>::new();
            for extra in &extras {
                let cell = extra.cell();
                if mentioned_cells
                    .iter()
                    .any(|existing| existing.unraw() == cell.unraw())
                {
                    return Err(syn::Error::new(
                        cell.span(),
                        format!("duplicate extra-cell mention `{}`", cell.unraw()),
                    ));
                }
                mentioned_cells.push(cell.clone());
            }
            for narrowing in &narrowings {
                if !bindings
                    .iter()
                    .any(|binding| binding.unraw() == narrowing.binding.unraw())
                {
                    return Err(syn::Error::new(
                        narrowing.binding.span(),
                        format!(
                            "rule narrowing names unbound subject binding `{}`",
                            narrowing.binding.unraw()
                        ),
                    ));
                }
            }
            clauses.push(RuleClause {
                rule,
                attribute,
                narrowings,
                head_result,
                extras,
                bindings,
                computation_cell: None,
                source_range: TokenRange::new(clause_start, semicolon.span),
                layout,
            });
        }
        if clauses.is_empty() {
            return Err(input.error("a readable rule block requires at least one clause"));
        }
        if !configuration.unwrap_or(false)
            && imports.iter().any(|import| import.variant().is_some())
        {
            return Err(syn::Error::new(
                imports[0].item().span(),
                "a `for Sort` rule table accepts only `use Enum::*;` imports",
            ));
        }
        Ok(Self {
            sort,
            configuration: configuration.unwrap_or(false),
            imports,
            clauses,
        })
    }
}

#[derive(Clone)]
enum MachinePatternCell {
    KHead(Pat),
    MapItem {
        key: Expr,
        value: Ident,
    },
    Term {
        pattern: Box<RulePattern>,
        tree: Box<TermTree>,
    },
}

#[derive(Clone)]
enum MachineResultCell {
    KItems(Vec<Expr>),
    Term(Box<Expr>),
}

fn parse_machine_pattern_record(
    input: ParseStream<'_>,
) -> syn::Result<Vec<(Ident, MachinePatternCell)>> {
    let content;
    braced!(content in input);
    let mut cells = Vec::new();
    while !content.is_empty() {
        let cell = content.call(Ident::parse_any)?;
        if cells
            .iter()
            .any(|(existing, _): &(Ident, MachinePatternCell)| existing.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                format!("duplicate machine-rule cell `{}`", cell.unraw()),
            ));
        }
        content.parse::<Token![:]>()?;
        let value = if content.peek(syn::token::Bracket) {
            let sequence;
            bracketed!(sequence in content);
            if sequence.peek(Token![..]) {
                return Err(
                    sequence.error("a machine-rule pattern must match one k head before `..`")
                );
            }
            let head = sequence.call(Pat::parse_single)?;
            sequence.parse::<Token![,]>()?;
            sequence.parse::<Token![..]>()?;
            if sequence.peek(Token![,]) {
                sequence.parse::<Token![,]>()?;
            }
            if !sequence.is_empty() {
                return Err(sequence.error("a machine-rule k pattern is `[head, ..]`"));
            }
            MachinePatternCell::KHead(head)
        } else if content.peek(syn::token::Brace) {
            let map;
            braced!(map in content);
            let key = parse_expression_before_arrow(&map)?;
            map.parse::<Token![->]>()?;
            let value = map.call(Ident::parse_any)?;
            map.parse::<Token![,]>()?;
            map.parse::<Token![..]>()?;
            if map.peek(Token![,]) {
                map.parse::<Token![,]>()?;
            }
            if !map.is_empty() {
                return Err(map.error("a machine-rule map pattern is `{ key -> value, .. }`"));
            }
            MachinePatternCell::MapItem { key, value }
        } else {
            let pattern = content.call(Pat::parse_single)?;
            let (pattern, tree) = parse_rule_pattern(pattern, true, true)?;
            MachinePatternCell::Term {
                pattern: Box::new(pattern),
                tree: Box::new(tree),
            }
        };
        cells.push((cell, value));
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        } else if !content.is_empty() {
            return Err(content.error("expected `,` between machine-rule cells"));
        }
    }
    Ok(cells)
}

fn parse_expression_before_arrow(input: ParseStream<'_>) -> syn::Result<Expr> {
    let fork = input.fork();
    let mut tokens = TokenStream::new();
    while !fork.peek(Token![->]) {
        if fork.peek(Token![=>]) {
            return Err(fork.error("`=>` is reserved for rewrites; map entries use `->`"));
        }
        if fork.is_empty() {
            return Err(fork.error("a map item requires `key -> value`"));
        }
        tokens.extend([fork.parse::<TokenTree>()?]);
    }
    if tokens.is_empty() {
        return Err(fork.error("a map item requires a key before `->`"));
    }
    input.advance_to(&fork);
    syn::parse2(tokens)
}

fn parse_machine_result_record(
    input: ParseStream<'_>,
) -> syn::Result<Vec<(Ident, MachineResultCell)>> {
    let content;
    braced!(content in input);
    let mut cells = Vec::new();
    while !content.is_empty() {
        let cell = content.call(Ident::parse_any)?;
        if cells
            .iter()
            .any(|(existing, _): &(Ident, MachineResultCell)| existing.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                format!("duplicate machine-rule result cell `{}`", cell.unraw()),
            ));
        }
        content.parse::<Token![:]>()?;
        let value = if content.peek(syn::token::Bracket) {
            let sequence;
            bracketed!(sequence in content);
            let mut items = Vec::new();
            while !sequence.peek(Token![..]) {
                items.push(sequence.parse::<Expr>()?);
                sequence.parse::<Token![,]>()?;
            }
            sequence.parse::<Token![..]>()?;
            if sequence.peek(Token![,]) {
                sequence.parse::<Token![,]>()?;
            }
            if !sequence.is_empty() {
                return Err(sequence.error("a machine-rule k result ends in `..`"));
            }
            MachineResultCell::KItems(items)
        } else {
            MachineResultCell::Term(Box::new(content.parse::<Expr>()?))
        };
        cells.push((cell, value));
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        } else if !content.is_empty() {
            return Err(content.error("expected `,` between machine-rule result cells"));
        }
    }
    Ok(cells)
}

#[allow(clippy::too_many_lines)]
fn parse_machine_clause(
    input: ParseStream<'_>,
    attributes: Vec<Attribute>,
    name: &Ident,
    configuration_type: &Type,
    clause_start: proc_macro2::Span,
) -> syn::Result<RuleClause> {
    let pattern_record: TokenTree = input.fork().parse()?;
    let subject_cells = parse_machine_pattern_record(input)?;
    input.parse::<Token![=>]>()?;
    let result_record: TokenTree = input.fork().parse()?;
    let result_cells = parse_machine_result_record(input)?;
    let mut layout = RuleClauseLayout {
        label: TokenRange::for_tokens(name)?,
        pattern: TokenRange::for_tokens(&pattern_record)?,
        result: TokenRange::for_tokens(&result_record)?,
        conditions: None,
    };

    let mut narrowings = Vec::new();
    if input.peek(Token![where]) {
        input.parse::<Token![where]>()?;
        layout.conditions = Some(condition_token_range(input)?);
        loop {
            let binding = input.call(Ident::parse_any)?;
            input.parse::<Token![:]>()?;
            let sort: Path = input.parse()?;
            if !is_plain_path(&sort) {
                return Err(syn::Error::new(
                    sort.span(),
                    "a rule narrowing requires a plain object-sort path",
                ));
            }
            if narrowings
                .iter()
                .any(|existing: &RuleNarrowing| existing.binding.unraw() == binding.unraw())
            {
                return Err(syn::Error::new(
                    binding.span(),
                    format!("duplicate narrowing for binding `{}`", binding.unraw()),
                ));
            }
            narrowings.push(RuleNarrowing { binding, sort });
            if !input.peek(Token![,]) {
                break;
            }
            input.parse::<Token![,]>()?;
        }
    }
    let semicolon = input.parse::<Token![;]>()?;

    let mut subject_k = None;
    let mut extras = Vec::new();
    let mut extra_bindings = Vec::new();
    for (cell, pattern) in &subject_cells {
        match pattern {
            MachinePatternCell::KHead(head) => {
                if subject_k.replace((cell.clone(), head.clone())).is_some() {
                    return Err(syn::Error::new(
                        cell.span(),
                        "a machine rule has exactly one sequence-pattern cell",
                    ));
                }
            }
            MachinePatternCell::MapItem { key, value } => {
                if result_cells
                    .iter()
                    .any(|(result_cell, _)| result_cell.unraw() == cell.unraw())
                {
                    return Err(syn::Error::new(
                        cell.span(),
                        "a preserved map-item cell is omitted from the machine-rule result",
                    ));
                }
                extras.push(RuleExtra::HaveMap {
                    cell: cell.clone(),
                    key: Box::new(TermExpression::from_expression(key.clone())?),
                    value: value.clone(),
                });
                extra_bindings.push(value.clone());
            }
            MachinePatternCell::Term {
                pattern,
                tree: before_tree,
            } => {
                let Some((_, MachineResultCell::Term(result))) = result_cells
                    .iter()
                    .find(|(result_cell, _)| result_cell.unraw() == cell.unraw())
                else {
                    return Err(syn::Error::new(
                        cell.span(),
                        "an ordinary fixed-cell pattern requires a corresponding result",
                    ));
                };
                let map_update = match pattern.native_pattern() {
                    Some(Pat::Ident(PatIdent { ident: base, .. })) => {
                        parse_machine_update(cell, base, result).ok()
                    }
                    _ => None,
                };
                if let Some(update) = map_update {
                    let RuleExtra::UpdateMap { base, .. } = &update else {
                        unreachable!("machine map-update parsing returns an update extra")
                    };
                    extra_bindings.push(base.clone());
                    extras.push(update);
                } else {
                    extra_bindings.extend(pattern.bindings().iter().cloned());
                    extras.push(RuleExtra::RewriteCell {
                        cell: cell.clone(),
                        before: pattern.clone(),
                        before_tree: before_tree.clone(),
                        after: Box::new(TermExpression::from_expression((**result).clone())?),
                    });
                }
            }
        }
    }
    for (cell, _) in &result_cells {
        if !subject_cells
            .iter()
            .any(|(subject_cell, _)| subject_cell.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                "a machine-rule result cannot introduce an unmatched cell",
            ));
        }
    }
    let (computation_cell, subject_k) = subject_k.ok_or_else(|| {
        syn::Error::new(
            name.span(),
            "a machine rule must match one computation-cell sequence",
        )
    })?;
    let Some((_, MachineResultCell::KItems(result_k))) = result_cells
        .iter()
        .find(|(cell, _)| cell.unraw() == computation_cell.unraw())
    else {
        return Err(syn::Error::new(
            name.span(),
            "a machine rule must write its framed computation-cell sequence",
        ));
    };
    let head_result = match result_k.as_slice() {
        [] => RuleHeadResult::Erase(TokenRange::for_tokens(&name)?),
        [term] => RuleHeadResult::Replace(Box::new(TermExpression::from_expression(term.clone())?)),
        items => RuleHeadResult::Splice {
            range: TokenRange::for_tokens(&name)?,
            items: items
                .iter()
                .cloned()
                .map(TermExpression::from_expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
    };

    let (attribute, retained) = take_rule_clause_attribute(attributes)?;
    let placeholder: Expr = match &head_result {
        RuleHeadResult::Replace(term) => term.expression().clone(),
        RuleHeadResult::Splice { .. } | RuleHeadResult::Erase(_) => syn::parse_quote!(true),
    };
    let item: ItemFn = syn::parse2(quote! {
        #(#retained)*
        pub fn #name(#subject_k: #configuration_type) -> #configuration_type { #placeholder }
    })?;
    let rule = RuleItem::from_readable_item(item)?;
    let mut bindings = rule.parameter.pattern.bindings().to_vec();
    for introduced in extra_bindings {
        if bindings
            .iter()
            .any(|binding| binding.unraw() == introduced.unraw())
        {
            return Err(syn::Error::new(
                introduced.span(),
                format!("duplicate readable rule binding `{}`", introduced.unraw()),
            ));
        }
        bindings.push(introduced);
    }
    for narrowing in &narrowings {
        if !bindings
            .iter()
            .any(|binding| binding.unraw() == narrowing.binding.unraw())
        {
            return Err(syn::Error::new(
                narrowing.binding.span(),
                format!(
                    "rule narrowing names unbound subject binding `{}`",
                    narrowing.binding.unraw()
                ),
            ));
        }
    }
    Ok(RuleClause {
        rule,
        attribute,
        narrowings,
        head_result,
        extras,
        bindings,
        computation_cell: Some(computation_cell),
        source_range: TokenRange::new(clause_start, semicolon.span),
        layout,
    })
}

fn condition_token_range(input: ParseStream<'_>) -> syn::Result<TokenRange> {
    let fork = input.fork();
    let mut tokens = TokenStream::new();
    while !fork.is_empty() && !fork.peek(Token![;]) {
        tokens.extend([fork.parse::<TokenTree>()?]);
    }
    if tokens.is_empty() {
        return Err(input.error("expected a rule condition after `where`"));
    }
    Ok(TokenRange::for_tokens(&tokens)?)
}

fn parse_machine_update(cell: &Ident, base: &Ident, expression: &Expr) -> syn::Result<RuleExtra> {
    parse_map_update(cell, base, expression, "the map update base must be")
}

fn parse_head_result(result: Expr) -> syn::Result<RuleHeadResult> {
    if let Expr::Tuple(tuple) = &result
        && tuple.elems.is_empty()
    {
        return Ok(RuleHeadResult::Erase(TokenRange::for_tokens(&result)?));
    }
    if let Expr::Macro(expression) = &result
        && expression
            .mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "k")
    {
        let sequence = crate::parse_k_sequence_expression(expression.mac.tokens.clone())?;
        if !matches!(sequence.tail(), crate::StateMacroRemainder::Exact) {
            return Err(syn::Error::new(
                expression.span(),
                "a readable rule splice has an implicit preserved tail; do not spell another tail",
            ));
        }
        return Ok(RuleHeadResult::Splice {
            range: TokenRange::for_tokens(&result)?,
            items: sequence.items().to_vec(),
        });
    }
    Ok(RuleHeadResult::Replace(Box::new(
        TermExpression::from_expression(result)?,
    )))
}

fn parse_have_extra(input: ParseStream<'_>) -> syn::Result<RuleExtra> {
    let cell = input.call(Ident::parse_any)?;
    let content;
    bracketed!(content in input);
    let key = parse_expression_before_arrow(&content)?;
    content.parse::<Token![->]>()?;
    content.parse::<Token![let]>()?;
    let value = content.call(Ident::parse_any)?;
    if !content.is_empty() {
        return Err(content.error("unexpected tokens after map binding value"));
    }
    Ok(RuleExtra::HaveMap {
        cell,
        key: Box::new(TermExpression::from_expression(key)?),
        value,
    })
}

fn parse_update_extra(input: ParseStream<'_>) -> syn::Result<RuleExtra> {
    let cell = input.call(Ident::parse_any)?;
    input.parse::<Token![=]>()?;
    let expression: Expr = input.parse()?;
    parse_map_update(
        &cell,
        &cell,
        &expression,
        "the update base must be the cell",
    )
}

fn parse_map_update(
    cell: &Ident,
    expected_base: &Ident,
    expression: &Expr,
    base_error: &str,
) -> syn::Result<RuleExtra> {
    let Expr::Call(ExprCall { func, args, .. }) = expression else {
        return Err(syn::Error::new(
            expression.span(),
            "a changed map cell requires one ordinary three-argument update term",
        ));
    };
    let Expr::Path(function) = func.as_ref() else {
        return Err(syn::Error::new(
            func.span(),
            "a changed map cell update must have a plain path head",
        ));
    };
    if function.qself.is_some() || !is_plain_path(&function.path) {
        return Err(syn::Error::new(
            function.path.span(),
            "a changed map cell update must have a plain path head",
        ));
    }
    let arguments = args.iter().collect::<Vec<_>>();
    let [base, _, _] = arguments.as_slice() else {
        return Err(syn::Error::new(
            args.span(),
            "a map update term requires exactly three arguments",
        ));
    };
    let Expr::Path(base) = base else {
        return Err(syn::Error::new(
            base.span(),
            "the first map update argument must be the matched whole-map binding",
        ));
    };
    if base.path.leading_colon.is_some()
        || base.path.segments.len() != 1
        || base.path.segments[0].ident.unraw() != expected_base.unraw()
    {
        return Err(syn::Error::new(
            base.path.span(),
            format!("{base_error} `{}`", expected_base.unraw()),
        ));
    }
    let update = TermExpression::from_expression(expression.clone())?;
    Ok(RuleExtra::UpdateMap {
        cell: cell.clone(),
        base: base.path.segments[0].ident.clone(),
        update: Box::new(update),
    })
}

fn map_update_arguments(update: &TermExpression) -> [&Expr; 3] {
    let Expr::Call(ExprCall { args, .. }) = update.expression() else {
        unreachable!("validated map update terms are calls")
    };
    let arguments = args.iter().collect::<Vec<_>>();
    let [base, key, value] = arguments.as_slice() else {
        unreachable!("validated map update terms have exactly three arguments")
    };
    [base, key, value]
}

impl RuleItem {
    /// Validates a previously parsed Rust function as a rule clause.
    ///
    /// # Errors
    ///
    /// Rejects signature modifiers, arity other than one, receivers, non-term
    /// types, unsupported patterns, and bodies other than one named term.
    pub fn from_item(mut item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_term_sort, false, false)
    }

    fn from_readable_item(mut item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_readable_sort, true, true)
    }

    fn from_item_with_sort_parser(
        item: &mut ItemFn,
        sort_parser: fn(Type) -> Result<TermSort, SyntaxError>,
        allow_record_rest: bool,
        root_identifier_is_binding: bool,
    ) -> Result<Self, SyntaxError> {
        validate_signature_features(item)?;
        let argument = item.sig.inputs.first().ok_or_else(|| {
            unsupported_signature(
                "a rule must have exactly one subject parameter",
                item.sig.span(),
            )
        })?;
        let FnArg::Typed(argument) = argument else {
            return Err(unsupported_signature(
                "rules cannot have a `self` receiver",
                argument.span(),
            ));
        };
        if !argument.attrs.is_empty() {
            return Err(unsupported_signature(
                "parameter attributes are outside the rule shape",
                argument.attrs[0].span(),
            ));
        }
        let (pattern, subject_tree) = parse_rule_pattern(
            (*argument.pat).clone(),
            allow_record_rest,
            root_identifier_is_binding,
        )?;
        let parameter_sort = sort_parser((*argument.ty).clone())?;

        let ReturnType::Type(_, result_type) = &item.sig.output else {
            return Err(unsupported_signature(
                "a rule must declare a `Term<SortPath>` result",
                item.sig.ident.span(),
            ));
        };
        let result_sort = sort_parser((**result_type).clone())?;
        let result = parse_rule_body(item)?;
        let requires = take_requires_helper(&mut item.attrs)?;

        Ok(Self {
            item: item.clone(),
            parameter: RuleParameter {
                pattern,
                term_sort: parameter_sort,
            },
            result_sort,
            result,
            subject_tree,
            requires,
        })
    }

    /// Returns the original Rust function with authored spans.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }

    /// Returns the single subject parameter.
    #[must_use]
    pub const fn parameter(&self) -> &RuleParameter {
        &self.parameter
    }

    /// Returns the rule's result sort.
    #[must_use]
    pub const fn result_sort(&self) -> &TermSort {
        &self.result_sort
    }

    /// Returns the validated right-hand term payload.
    #[must_use]
    pub const fn result(&self) -> &TermExpression {
        &self.result
    }

    /// Returns the structured argument-preserving rule-subject tree.
    #[must_use]
    pub const fn subject_tree(&self) -> &TermTree {
        &self.subject_tree
    }

    /// Returns the optional object-language Boolean applicability condition.
    #[must_use]
    pub const fn requires(&self) -> Option<&RuleCondition> {
        self.requires.as_ref()
    }

    /// Returns canonical rule node anchors and nested path anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::RuleDeclaration,
                0,
                TokenRange::for_tokens(&self.item.sig.ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RulePattern,
                0,
                self.parameter.pattern.range()?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleType,
                0,
                TokenRange::for_tokens(self.parameter.term_sort.ty())?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResultType,
                0,
                TokenRange::for_tokens(self.result_sort.ty())?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResult,
                0,
                TokenRange::for_tokens(self.result.expression())?,
            ),
        ];
        for (ordinal, range) in self
            .parameter
            .pattern
            .path_ranges()?
            .into_iter()
            .enumerate()
        {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleLeftPath,
                checked_ordinal(ordinal, ProvenanceRole::RuleLeftPath, range.first())?,
                range,
            ));
        }
        for (ordinal, symbol) in self.result.symbols().iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleRightPath,
                checked_ordinal(ordinal, ProvenanceRole::RuleRightPath, symbol.path().span())?,
                TokenRange::for_tokens(symbol.path())?,
            ));
        }
        Ok(anchors)
    }

    /// Returns the compact catalog plus typed subject/result term-node
    /// anchors required by protocol v6.
    ///
    /// # Errors
    ///
    /// Returns endpoint or occurrence-overflow errors.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.provenance()?;
        push_term_node_anchors(
            &mut anchors,
            self.parameter.pattern.nodes(),
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            &self.subject_tree,
            ProvenanceRole::RuleLeftRecordFieldName,
        )?;
        push_wildcard_anchors(&mut anchors, &self.subject_tree)?;
        push_term_node_anchors(
            &mut anchors,
            self.result.nodes(),
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            self.result.tree(),
            ProvenanceRole::RuleRightRecordFieldName,
        )?;
        if let Some(requires) = &self.requires {
            anchors.extend(requires.provenance()?);
        }
        Ok(anchors)
    }

    /// Returns rustc-resolvable type and constructor references in canonical order.
    ///
    /// The order is parameter type, result type, subject paths in preorder,
    /// then result paths in preorder. Each path retains the ordinal assigned by
    /// [`Self::provenance`]. Skipping a bare bound variable therefore leaves an
    /// ordinal gap rather than renumbering later references.
    ///
    /// # Errors
    ///
    /// Returns a structured overflow error if one path role has more than
    /// `u32::MAX` occurrences.
    pub fn reference_candidates(&self) -> Result<Vec<ReferenceCandidate>, SyntaxError> {
        let mut candidates = vec![
            ReferenceCandidate {
                key: canonical_key(ProvenanceRole::RuleType, 0),
                path: self.parameter.term_sort.sort().clone(),
                kind: (),
            },
            ReferenceCandidate {
                key: canonical_key(ProvenanceRole::RuleResultType, 0),
                path: self.result_sort.sort().clone(),
                kind: (),
            },
        ];

        match &self.parameter.pattern {
            RulePattern::Native {
                nodes, bindings, ..
            } => {
                let mut ordinal = 0_usize;
                for node in nodes {
                    let path = match node {
                        TermNode::ApplicationHead(path) => path,
                        TermNode::Reference(path) => {
                            let current = ordinal;
                            ordinal += 1;
                            if is_bound_path(path, bindings) {
                                continue;
                            }
                            push_candidate(
                                &mut candidates,
                                ProvenanceRole::RuleLeftPath,
                                current,
                                path,
                            )?;
                            continue;
                        }
                        TermNode::Literal(_)
                        | TermNode::IdToken(_)
                        | TermNode::BytesToken(_)
                        | TermNode::Anonymous { .. }
                        | TermNode::OrBool(_) => continue,
                    };
                    push_candidate(&mut candidates, ProvenanceRole::RuleLeftPath, ordinal, path)?;
                    ordinal += 1;
                }
            }
            RulePattern::TermMacro { term, bindings, .. } => {
                for (ordinal, symbol) in term.symbols().iter().enumerate() {
                    if is_bound_reference(symbol, bindings) {
                        continue;
                    }
                    push_candidate(
                        &mut candidates,
                        ProvenanceRole::RuleLeftPath,
                        ordinal,
                        symbol.path(),
                    )?;
                }
            }
        }

        let bindings = self.parameter.pattern.bindings();
        for (ordinal, symbol) in self.result.symbols().iter().enumerate() {
            if is_bound_reference(symbol, bindings) {
                continue;
            }
            push_candidate(
                &mut candidates,
                ProvenanceRole::RuleRightPath,
                ordinal,
                symbol.path(),
            )?;
        }
        Ok(candidates)
    }

    /// Returns only rule-term application/reference candidates under the
    /// typed protocol-v6 role catalog. Bound bare paths remain absent without
    /// renumbering later same-kind occurrences.
    ///
    /// Resolution to a declared production or a builtin operation remains a
    /// compiler responsibility based on the exact retained Rust path.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error for pathological input.
    pub fn term_reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<TermSymbolKind>>, SyntaxError> {
        let mut candidates = Vec::new();
        push_term_reference_candidates(
            &mut candidates,
            self.parameter.pattern.nodes(),
            self.parameter.pattern.bindings(),
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
        )?;
        push_term_reference_candidates(
            &mut candidates,
            self.result.nodes(),
            self.parameter.pattern.bindings(),
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
        )?;
        if let Some(requires) = &self.requires {
            candidates.extend(requires.reference_candidates(self.parameter.pattern.bindings())?);
        }
        Ok(candidates)
    }
}

pub(crate) fn take_requires_helper(
    attributes: &mut Vec<Attribute>,
) -> Result<Option<RuleCondition>, SyntaxError> {
    let mut condition = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        let is_requires = attribute.path().segments.len() >= 2
            && attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "requires");
        if !is_requires {
            retained.push(attribute);
            continue;
        }
        if condition.is_some() {
            return Err(unsupported_signature(
                "a rule may declare only one `#[k::requires(...)]` condition",
                attribute.span(),
            ));
        }
        let Meta::List(list) = attribute.meta else {
            return Err(unsupported_signature(
                "`#[k::requires]` requires one parenthesized object-Bool term",
                attribute.span(),
            ));
        };
        let term = TermExpression::parse_tokens(list.tokens)?;
        if term.root_kind() == crate::TermRootKind::Literal {
            return Err(unsupported_signature(
                "a rule condition must be an object-Bool term constructor, not a host literal",
                term.expression().span(),
            ));
        }
        condition = Some(RuleCondition { term });
    }
    *attributes = retained;
    Ok(condition)
}

impl KrsSyntax for RuleItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2::<ItemFn>(tokens)?)
    }
}

impl KrsSyntax for RuleBlock {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let parser = |input: ParseStream<'_>| Self::from_stream(input);
        parser.parse2(tokens).map_err(SyntaxError::from)
    }
}

/// Parses a readable term-rule family together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`RuleBlock::parse_tokens`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_rule_block_source_with_trivia(
    source: &str,
) -> Result<(RuleBlock, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("k::rules")?;
    Ok((RuleBlock::parse_tokens(tokens)?, trivia))
}

fn take_rule_clause_attribute(
    attributes: Vec<Attribute>,
) -> Result<(crate::RuleAttribute, Vec<Attribute>), SyntaxError> {
    let mut rule = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in attributes {
        if attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "rule")
        {
            if rule.is_some() {
                return Err(unsupported_signature(
                    "a readable clause may carry only one `#[k::rule(...)]` label attribute",
                    attribute.span(),
                ));
            }
            let Meta::List(list) = &attribute.meta else {
                return Err(unsupported_signature(
                    "`#[k::rule]` clause metadata must be empty or parenthesized",
                    attribute.span(),
                ));
            };
            rule = Some(crate::RuleAttribute::parse_tokens(list.tokens.clone())?);
        } else {
            retained.push(attribute);
        }
    }
    Ok((rule.unwrap_or_default(), retained))
}

fn enum_glob_owner(item: &ItemUse) -> syn::Result<(Path, Option<Ident>)> {
    fn visit(tree: &UseTree, segments: &mut Vec<Ident>) -> syn::Result<Option<Ident>> {
        match tree {
            UseTree::Path(path) => {
                segments.push(path.ident.clone());
                visit(&path.tree, segments)
            }
            UseTree::Glob(_) if !segments.is_empty() => Ok(None),
            UseTree::Name(name) if !segments.is_empty() => Ok(Some(name.ident.clone())),
            _ => Err(syn::Error::new(
                tree.span(),
                "readable rules accept only `use Enum::*;` or `use Enum::Variant;` imports",
            )),
        }
    }

    let mut segments = Vec::new();
    let variant = visit(&item.tree, &mut segments)?;
    let leading = item.leading_colon;
    let owner = syn::parse2(quote!(#leading #(#segments)::*))?;
    Ok((owner, variant))
}

fn validate_signature_features(item: &ItemFn) -> Result<(), SyntaxError> {
    let signature = &item.sig;
    if signature.inputs.len() != 1 {
        return Err(unsupported_signature(
            "a rule must have exactly one subject parameter",
            signature.inputs.span(),
        ));
    }
    if let Some(token) = signature.constness {
        return Err(unsupported_signature("rules cannot be `const`", token.span));
    }
    if let Some(token) = signature.asyncness {
        return Err(unsupported_signature("rules cannot be `async`", token.span));
    }
    if let Some(token) = signature.unsafety {
        return Err(unsupported_signature(
            "rules cannot be `unsafe`",
            token.span,
        ));
    }
    if let Some(abi) = &signature.abi {
        return Err(unsupported_signature(
            "rules cannot declare an extern ABI",
            abi.span(),
        ));
    }
    if !signature.generics.params.is_empty() {
        return Err(unsupported_signature(
            "rule generics are not supported",
            signature.generics.params.span(),
        ));
    }
    if let Some(where_clause) = &signature.generics.where_clause {
        return Err(unsupported_signature(
            "rule where clauses are not supported",
            where_clause.span(),
        ));
    }
    if let Some(variadic) = &signature.variadic {
        return Err(unsupported_signature(
            "variadic rules are not supported",
            variadic.span(),
        ));
    }
    Ok(())
}

pub(crate) fn parse_term_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    let Type::Path(term_path) = &ty else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    };
    if term_path.qself.is_some() || term_path.path.segments.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    }
    let last_index = term_path.path.segments.len() - 1;
    for (index, segment) in term_path.path.segments.iter().enumerate() {
        if index != last_index && !matches!(segment.arguments, PathArguments::None) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidTermType,
                segment.span(),
            ));
        }
    }
    let last = &term_path.path.segments[last_index];
    if last.ident != "Term" {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            last.span(),
        ));
    }
    let PathArguments::AngleBracketed(arguments) = &last.arguments else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            last.span(),
        ));
    };
    if arguments.args.len() != 1 {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            arguments.span(),
        ));
    }
    let Some(GenericArgument::Type(sort_type)) = arguments.args.first() else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            arguments.span(),
        ));
    };

    let (sort, dynamic) = match sort_type {
        Type::Path(sort) if sort.qself.is_none() && is_plain_path(&sort.path) => {
            (sort.path.clone(), false)
        }
        Type::TraitObject(object) if object.dyn_token.is_some() && object.bounds.len() == 1 => {
            let Some(TypeParamBound::Trait(bound)) = object.bounds.first() else {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidTermType,
                    object.span(),
                ));
            };
            if !matches!(bound.modifier, TraitBoundModifier::None)
                || bound.lifetimes.is_some()
                || bound.paren_token.is_some()
                || !is_plain_path(&bound.path)
            {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidTermType,
                    bound.span(),
                ));
            }
            (bound.path.clone(), true)
        }
        _ => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidTermType,
                sort_type.span(),
            ));
        }
    };
    Ok(TermSort { ty, sort, dynamic })
}

pub(crate) fn parse_readable_sort(ty: Type) -> Result<TermSort, SyntaxError> {
    let Type::Path(path) = &ty else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    };
    if path.qself.is_some() || !is_plain_path(&path.path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidTermType,
            ty.span(),
        ));
    }
    Ok(TermSort {
        sort: path.path.clone(),
        ty,
        dynamic: false,
    })
}

fn parse_rule_pattern(
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

fn is_bound_reference(symbol: &crate::TermSymbol, bindings: &[Ident]) -> bool {
    symbol.kind() == crate::TermSymbolKind::Reference && is_bound_path(symbol.path(), bindings)
}

fn is_bound_path(path: &Path, bindings: &[Ident]) -> bool {
    bare_path_ident(path).is_some_and(|ident| {
        let spelling = ident.to_string();
        bindings.iter().any(|binding| binding == &spelling)
    })
}

fn push_term_node_anchors(
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

fn push_wildcard_anchors(
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

fn push_term_reference_candidates(
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

fn push_candidate(
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

fn canonical_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
}

fn parse_rule_body(item: &ItemFn) -> Result<TermExpression, SyntaxError> {
    if item.block.stmts.len() != 1 {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "the body must contain exactly one term expression",
            },
            item.block.span(),
        ));
    }
    let Stmt::Expr(expression, None) = &item.block.stmts[0] else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "the sole result term must not have a trailing semicolon",
            },
            item.block.stmts[0].span(),
        ));
    };
    match expression {
        Expr::Macro(expression_macro) => {
            if !is_term_macro(&expression_macro.mac.path) {
                return Err(unexpected_macro(&expression_macro.mac.path));
            }
            TermExpression::parse_tokens(expression_macro.mac.tokens.clone())
        }
        expression => TermExpression::from_expression(expression.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::{RuleBlock, TokenRange};
    use crate::KrsSyntax;

    fn source_slice(source: &str, range: TokenRange) -> &str {
        &source[range.first().byte_range().start..range.last().byte_range().end]
    }

    #[test]
    fn clause_layout_ranges_preserve_authored_components() {
        let source = "for Expr; step: Wrap(value) => int::add(value, 1)\n\
                      where value: Int, update env = map::update(env, value, value);\n\
                      bare: Wrap(other) => other;";
        let block = RuleBlock::parse_source(source).unwrap();
        let layout = block.clauses()[0].layout();
        assert_eq!(source_slice(source, layout.label), "step");
        assert_eq!(source_slice(source, layout.pattern), "Wrap(value)");
        assert_eq!(source_slice(source, layout.result), "int::add(value, 1)");
        assert_eq!(
            source_slice(source, layout.conditions.unwrap()),
            "value: Int, update env = map::update(env, value, value)"
        );
        assert!(block.clauses()[1].layout().conditions.is_none());

        let source = "for Machine; step: { computation: [Wrap(value), ..], }\n\
                      => { computation: [value, ..], } where value: Int;";
        let block = RuleBlock::parse_source(source).unwrap();
        let layout = block.clauses()[0].layout();
        assert_eq!(source_slice(source, layout.label), "step");
        assert_eq!(
            source_slice(source, layout.pattern),
            "{ computation: [Wrap(value), ..], }"
        );
        assert_eq!(
            source_slice(source, layout.result),
            "{ computation: [value, ..], }"
        );
        assert_eq!(
            source_slice(source, layout.conditions.unwrap()),
            "value: Int"
        );
    }
}
