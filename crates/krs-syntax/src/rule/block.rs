use proc_macro2::TokenStream;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemFn, ItemUse, Meta, Path, Token, Type, UseTree};

use super::condition::{
    HaveMapExtra, MapUpdateExtra, RuleExtra, condition_token_range, parse_have_extra,
    parse_update_extra,
};
use super::item::RuleItem;
use super::machine::parse_machine_clause;
use super::pattern::{
    RuleTermCounters, RuleTermSide, append_rule_pattern_anchors, append_rule_term_anchors,
    parse_pattern_with_signs,
};
use crate::parse::{
    KrsSyntax, ParseError, checked_ordinal, structured,
    unsupported_rule_signature as unsupported_signature,
};
use crate::path::is_plain_path;
use crate::term_sort::{TermSort, parse_readable_sort};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, TermExpression, TokenRange};

enum TermTableExtra {
    Have(HaveMapExtra),
    Update(MapUpdateExtra),
}

impl TermTableExtra {
    fn introduced_binding(&self) -> &Ident {
        match self {
            Self::Have(extra) => &extra.value,
            Self::Update(extra) => &extra.cell,
        }
    }

    fn cell(&self) -> &Ident {
        match self {
            Self::Have(extra) => &extra.cell,
            Self::Update(extra) => &extra.cell,
        }
    }
}

impl From<TermTableExtra> for RuleExtra {
    fn from(extra: TermTableExtra) -> Self {
        match extra {
            TermTableExtra::Have(extra) => extra.into(),
            TermTableExtra::Update(extra) => extra.into(),
        }
    }
}

/// One explicit binding-sort refinement after a readable rule clause.
#[derive(Clone, Debug)]
pub struct RuleNarrowing {
    pub(super) binding: Ident,
    pub(super) sort: Path,
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
    pub(super) rule: RuleItem,
    pub(super) attribute: crate::RuleAttribute,
    pub(super) narrowings: Vec<RuleNarrowing>,
    pub(super) head_result: Option<RuleHeadResult>,
    pub(super) extras: Vec<RuleExtra>,
    pub(super) bindings: Vec<Ident>,
    pub(super) computation_cell: Option<Ident>,
    pub(super) source_range: TokenRange,
    pub(super) layout: RuleClauseLayout,
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

    /// Returns replacement, splice, or erasure head meaning, absent for a
    /// cell-record clause that leaves the computation cell out.
    #[must_use]
    pub const fn head_result(&self) -> Option<&RuleHeadResult> {
        self.head_result.as_ref()
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
    #[expect(
        clippy::too_many_lines,
        reason = "One ordered pass retains exact aggregate term ordinals."
    )]
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
        if self.head_result.is_none() {
            // The placeholder subject of a clause without the computation cell
            // has no authored tokens: the pattern is the whole subject record,
            // and every left-side anchor comes from the cell entries below.
            anchors.retain(|anchor| {
                !matches!(
                    anchor.role(),
                    ProvenanceRole::RulePattern
                        | ProvenanceRole::RuleLeftPath
                        | ProvenanceRole::RuleLeftApplicationHead
                        | ProvenanceRole::RuleLeftReference
                        | ProvenanceRole::RuleLeftLiteral
                        | ProvenanceRole::RuleLeftRecordFieldName
                        | ProvenanceRole::RuleLeftWildcard
                )
            });
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RulePattern,
                0,
                self.layout.pattern,
            ));
        }
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::RuleResult,
            0,
            self.head_result
                .as_ref()
                .map_or(Ok(self.layout.result), RuleHeadResult::range)?,
        ));
        let mut right = RuleTermCounters::default();
        match &self.head_result {
            None | Some(RuleHeadResult::Erase(_)) => {}
            Some(RuleHeadResult::Replace(term)) => {
                append_rule_term_anchors(&mut anchors, term, RuleTermSide::Right, &mut right)?;
            }
            Some(RuleHeadResult::Splice { range, items }) => {
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
        }

        let mut left = if self.head_result.is_some() {
            let mut left =
                RuleTermCounters::from_rule_pattern(self.rule.parameter().pattern.nodes());
            let mut subject_fields = Vec::new();
            self.rule
                .subject_tree()
                .record_field_names_preorder(&mut subject_fields);
            left.field = subject_fields.len();
            left
        } else {
            RuleTermCounters::default()
        };
        let mut have_cell = 0_usize;
        let mut update_cell = 0_usize;
        // Wildcards in extra-cell patterns, such as `frame: _`, continue the
        // subject's wildcard ordinals in clause order.
        let mut wildcard = anchors
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::RuleLeftWildcard)
            .count();
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
                    let [base, key, value] = update.arguments();
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
                        update.term(),
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
                    let mut wildcards = Vec::new();
                    before_tree.wildcard_ranges_preorder(&mut wildcards);
                    for range in wildcards {
                        anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::RuleLeftWildcard,
                            checked_ordinal(
                                wildcard,
                                ProvenanceRole::RuleLeftWildcard,
                                range.first(),
                            )?,
                            range,
                        ));
                        wildcard += 1;
                    }

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

    #[expect(
        clippy::too_many_lines,
        reason = "One linear parser keeps clause diagnostics at authored tokens."
    )]
    fn from_stream(input: ParseStream<'_>) -> Result<Self, ParseError> {
        input.parse::<Token![for]>()?;
        let sort_type: Type = input.parse()?;
        let sort = parse_readable_sort(sort_type.clone())?;
        if input.peek(Token![in]) {
            return Err(input
                .error(
                    "`for Sort in cell` is a control-flow rule surface and is not implemented yet",
                )
                .into());
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
                )
                .into());
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
                )
                .into());
            }
            input.parse::<Token![:]>()?;
            let machine_clause = input.peek(syn::token::Brace);
            if let Some(expected) = configuration {
                if expected != machine_clause {
                    return Err(syn::Error::new(
                        name.span(),
                        "a readable rule block cannot mix term clauses and cell-record clauses",
                    )
                    .into());
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
            let (pattern, signs) = parse_pattern_with_signs(input)?;
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
                        "have" => extras.push(TermTableExtra::Have(parse_have_extra(input)?)),
                        "update" => extras.push(TermTableExtra::Update(parse_update_extra(input)?)),
                        _ => {
                            let binding = first;
                            input.parse::<Token![:]>()?;
                            let sort: Path = input.parse()?;
                            if !is_plain_path(&sort) {
                                return Err(syn::Error::new(
                                    sort.span(),
                                    "a rule narrowing requires a plain object-sort path",
                                )
                                .into());
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
                                )
                                .into());
                            }
                            narrowings.push(RuleNarrowing { binding, sort });
                        }
                    }
                    if !input.peek(Token![,]) {
                        break;
                    }
                    input.parse::<Token![,]>()?;
                    if input.peek(Token![;]) {
                        return Err(input
                            .error("expected a binding refinement after `,`")
                            .into());
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
            let rule = RuleItem::from_readable_item(item, signs)?;
            let mut bindings = rule.parameter.pattern.bindings().to_vec();
            for extra in &extras {
                let introduced = extra.introduced_binding();
                if bindings
                    .iter()
                    .any(|binding| binding.unraw() == introduced.unraw())
                {
                    return Err(syn::Error::new(
                        introduced.span(),
                        format!("duplicate readable rule binding `{}`", introduced.unraw()),
                    )
                    .into());
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
                    )
                    .into());
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
                    )
                    .into());
                }
            }
            clauses.push(RuleClause {
                rule,
                attribute,
                narrowings,
                head_result: Some(head_result),
                extras: extras.into_iter().map(RuleExtra::from).collect(),
                bindings,
                computation_cell: None,
                source_range: TokenRange::new(clause_start, semicolon.span),
                layout,
            });
        }
        if clauses.is_empty() {
            return Err(input
                .error("a readable rule block requires at least one clause")
                .into());
        }
        if !configuration.unwrap_or(false)
            && imports.iter().any(|import| import.variant().is_some())
        {
            return Err(syn::Error::new(
                imports[0].item().span(),
                "a `for Sort` rule table accepts only `use Enum::*;` imports",
            )
            .into());
        }
        Ok(Self {
            sort,
            configuration: configuration.unwrap_or(false),
            imports,
            clauses,
        })
    }
}

fn parse_head_result(result: Expr) -> Result<RuleHeadResult, ParseError> {
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
            )
            .into());
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

impl KrsSyntax for RuleBlock {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, Self::from_stream)
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

pub(super) fn take_rule_clause_attribute(
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
            let parsed = crate::RuleAttribute::parse_tokens(list.tokens.clone())?;
            if let Some(anywhere) = parsed.anywhere() {
                return Err(SyntaxError::new(
                    crate::SyntaxErrorKind::InvalidRuleKey {
                        reason: crate::ANYWHERE_NOT_TERM_SHAPED,
                    },
                    anywhere.span(),
                ));
            }
            rule = Some(parsed);
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
