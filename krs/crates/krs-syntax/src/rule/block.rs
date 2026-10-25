use proc_macro2::TokenStream;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemFn, ItemUse, Meta, Path, Token, Type};

use super::condition::{
    HaveMapExtra, MapUpdateExtra, RuleExtra, RuleMapEntry, condition_token_range, parse_have_extra,
    parse_update_extra,
};
use super::item::RuleItem;
use super::machine::parse_machine_clause;
use super::pattern::{
    RuleTermSide, allocate_rule_pattern_keys, allocate_rule_term_keys, allocate_wildcard_keys,
    parse_pattern_with_signs,
};
use crate::parse::{
    KeyAllocator, KrsSyntax, ParseError, structured,
    unsupported_rule_signature as unsupported_signature,
};
use crate::path::{is_plain_path, parametric_collection_error};
use crate::term::TermKeys;
use crate::term_sort::{TermSort, parse_readable_sort};
use crate::{
    ProvenanceAnchor, ProvenanceRole, SyntaxError, TermExpression, TermNode, TermTree, TokenRange,
};

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

/// The computation-cell items a readable clause matches: `[p1, .., pn, ..]`
/// matches at least `n` items and keeps the rest, `[p1, .., pn]` exactly `n`.
#[derive(Clone, Debug)]
pub struct RuleHead {
    pub(super) subject: bool,
    pub(super) following: Vec<RuleHeadItem>,
    pub(super) exact: bool,
}

/// One computation-cell item after the first that a readable clause matches.
#[derive(Clone, Debug)]
pub struct RuleHeadItem {
    pub(super) pattern: crate::RulePattern,
    pub(super) tree: TermTree,
}

/// The rest of one side of a list cell in a readable record (F6).
#[derive(Clone, Debug)]
pub enum RuleListRest<T> {
    /// No rest: the list ends after the elements (`[a, b]`).
    Exact,
    /// The anonymous `..`, one rest that both sides share.
    Shared(TokenRange),
    /// A named rest: the binder of `rest @ ..` in the pattern, the term of
    /// `..t` (or a whole term) in the result.
    Named(T),
}

impl<T> RuleListRest<T> {
    /// Whether this is the anonymous `..`.
    #[must_use]
    pub const fn is_shared(&self) -> bool {
        matches!(self, Self::Shared(_))
    }
}

/// The matched side of a list cell in a readable record (F6):
/// `stack: [a, b, ..]`, `queue: [.., z]`.
#[derive(Clone, Debug)]
pub struct RuleListPattern {
    pub(super) items: Vec<RuleHeadItem>,
    pub(super) rest: RuleListRest<RuleHeadItem>,
    pub(super) back: Vec<RuleHeadItem>,
}

impl RuleListPattern {
    /// The matched elements before the rest, front first.
    #[must_use]
    pub fn items(&self) -> &[RuleHeadItem] {
        &self.items
    }

    /// What the pattern matches between its front and back elements.
    #[must_use]
    pub const fn rest(&self) -> &RuleListRest<RuleHeadItem> {
        &self.rest
    }

    /// The matched elements after the rest, front first; only a builtin
    /// `List` has them.
    #[must_use]
    pub fn back(&self) -> &[RuleHeadItem] {
        &self.back
    }

    /// The front element patterns, the named rest's binder, then the back
    /// element patterns, in expansion order.
    pub(super) fn patterns(&self) -> impl Iterator<Item = &RuleHeadItem> {
        let rest = match &self.rest {
            RuleListRest::Named(rest) => Some(rest),
            RuleListRest::Exact | RuleListRest::Shared(_) => None,
        };
        self.items.iter().chain(rest).chain(&self.back)
    }

    /// The binders the pattern introduces, in order.
    pub(super) fn bindings(&self) -> impl Iterator<Item = &Ident> {
        self.patterns().flat_map(|item| item.pattern.bindings())
    }
}

/// The rewritten side of a list cell in a readable record (F6):
/// `stack: [c, ..]`, `logs: [..logs, entry]`.
#[derive(Clone, Debug)]
pub struct RuleListResult {
    pub(super) items: Vec<TermExpression>,
    pub(super) rest: RuleListRest<TermExpression>,
    pub(super) back: Vec<TermExpression>,
}

impl RuleListResult {
    /// The written elements before the rest, front first.
    #[must_use]
    pub fn items(&self) -> &[TermExpression] {
        &self.items
    }

    /// What stands between the front and back elements.
    #[must_use]
    pub const fn rest(&self) -> &RuleListRest<TermExpression> {
        &self.rest
    }

    /// The written elements after the rest, front first.
    #[must_use]
    pub fn back(&self) -> &[TermExpression] {
        &self.back
    }

    /// The front element terms, the named rest's term, then the back
    /// element terms, in expansion order.
    #[must_use]
    pub fn terms(&self) -> Vec<&TermExpression> {
        let rest = match &self.rest {
            RuleListRest::Named(rest) => Some(rest),
            RuleListRest::Exact | RuleListRest::Shared(_) => None,
        };
        self.items.iter().chain(rest).chain(&self.back).collect()
    }
}

impl RuleHead {
    /// Whether the clause's rule subject is the first matched item; it is a
    /// placeholder for `[]`, which matches no item.
    #[must_use]
    pub const fn subject(&self) -> bool {
        self.subject
    }

    /// The matched items after the first, front first.
    #[must_use]
    pub fn following(&self) -> &[RuleHeadItem] {
        &self.following
    }

    /// Whether the pattern names the whole cell, with no `..`.
    #[must_use]
    pub const fn exact(&self) -> bool {
        self.exact
    }
}

impl RuleHeadItem {
    /// The item's rule pattern.
    #[must_use]
    pub const fn pattern(&self) -> &crate::RulePattern {
        &self.pattern
    }

    /// The item's term tree.
    #[must_use]
    pub const fn tree(&self) -> &TermTree {
        &self.tree
    }
}

/// One named `pattern => result` clause in a readable rule block.
#[derive(Clone, Debug)]
pub struct RuleClause {
    pub(super) rule: RuleItem,
    pub(super) attribute: crate::RuleAttribute,
    pub(super) narrowings: Vec<RuleNarrowing>,
    pub(super) head: Option<RuleHead>,
    pub(super) head_result: Option<RuleHeadResult>,
    pub(super) extras: Vec<RuleExtra>,
    pub(super) bindings: Vec<Ident>,
    pub(super) computation_cell: Option<Ident>,
    pub(super) source_range: TokenRange,
    pub(super) layout: RuleClauseLayout,
    pub(super) bracket_alternative: Option<Box<BracketAlternative>>,
    /// The modality and flags of a `k::claims!` clause (F7), which is then a
    /// claim and carries no `#[k::rule]` metadata.
    pub(super) claim: Option<crate::ClaimAttribute>,
}

/// Which sentences a readable record block declares: `k::rules!` rules or
/// `k::claims!` claims (F7).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ReadableSentence {
    Rule,
    Claim,
}

/// The List-collection reading of a cell-record clause whose bracketed
/// value reads both as a List collection's instances and as the computation
/// cell's `[head, ..]` or a list's elements, such as `job: [Job { payload:
/// p }, ..] => job: [..]` (KF-023) or `job: [.., Job { payload: p }]`. Only
/// the cell's declared type, which the collector knows, tells them apart:
/// the clause is parsed in its computation-cell or elements reading and
/// carries this one beside it.
#[derive(Clone, Debug)]
pub struct BracketAlternative {
    pub(super) cell: Ident,
    pub(super) before: crate::StateTerm,
    pub(super) result_cell: Option<Ident>,
    pub(super) after: Option<crate::StateTerm>,
    pub(super) bindings: Vec<Ident>,
}

impl BracketAlternative {
    /// The cell, as the subject record names it.
    #[must_use]
    pub const fn cell(&self) -> &Ident {
        &self.cell
    }

    /// The subject instances: one front record and a rest.
    #[must_use]
    pub const fn before(&self) -> &crate::StateTerm {
        &self.before
    }

    /// The cell as the result record names it, absent when the result leaves
    /// it out.
    #[must_use]
    pub const fn result_cell(&self) -> Option<&Ident> {
        self.result_cell.as_ref()
    }

    /// The result instances, absent when the result leaves the cell out.
    #[must_use]
    pub const fn after(&self) -> Option<&crate::StateTerm> {
        self.after.as_ref()
    }

    /// The clause's bindings in this reading, in introduction order.
    #[must_use]
    pub fn bindings(&self) -> &[Ident] {
        &self.bindings
    }
}

impl RuleClause {
    /// Checks the clause's `#[k::exists]` binders against every binding it
    /// introduces and every term it writes (head result and extra cells).
    pub(super) fn check_existentials(&self) -> Result<(), SyntaxError> {
        let existentials = self.rule.existentials();
        if existentials.is_empty() {
            return Ok(());
        }
        existentials.check_shadowing(&self.bindings)?;
        let mut written = Vec::new();
        match &self.head_result {
            Some(RuleHeadResult::Replace(term)) => written.push(term.as_ref()),
            Some(RuleHeadResult::Splice { items, .. }) => written.extend(items.iter()),
            Some(RuleHeadResult::Erase(_)) | None => {}
        }
        for extra in &self.extras {
            match extra {
                RuleExtra::UpdateMap { update, .. } => written.push(update.term()),
                RuleExtra::RewriteCell { after, .. } => written.extend(after.as_deref()),
                RuleExtra::RewriteState { after, .. } => {
                    written.extend(after.iter().flat_map(|after| after.terms()));
                }
                RuleExtra::RewriteList { after, .. } => {
                    written.extend(after.iter().flat_map(|after| after.terms()));
                }
                RuleExtra::HaveMap { .. } => {}
            }
        }
        existentials.check_scope(
            self.rule.requires().map(super::RuleCondition::term),
            &written,
        )
    }

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

    /// Returns the modality and flags of a `k::claims!` clause (F7), which
    /// is a claim labelled by its name; `None` for a rule.
    #[must_use]
    pub const fn claim(&self) -> Option<&crate::ClaimAttribute> {
        self.claim.as_ref()
    }

    /// Keys a clause's literal islands (`k::id!`, `k::bytes!`, and a
    /// claim's `k::anonymous!`, `k::or_bool!`), each kind numbered in one sequence
    /// across the clause in the order expansion visits the clause's terms:
    /// the subject's terms, then the result's, then the `requires` and
    /// `ensures` conditions.
    fn allocate_claim_literal_keys(&self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        fn state_nodes<'a>(state: &'a crate::StateTerm, output: &mut Vec<&'a [TermNode]>) {
            output.extend(state.terms().into_iter().map(TermExpression::nodes));
            for nested in state.nested_states() {
                state_nodes(nested, output);
            }
        }
        let mut nodes: Vec<&[TermNode]> = Vec::new();
        if let Some(head) = &self.head {
            if head.subject {
                nodes.push(self.rule.parameter().pattern.nodes());
            }
            nodes.extend(head.following.iter().map(|item| item.pattern.nodes()));
        }
        for extra in &self.extras {
            match extra {
                RuleExtra::HaveMap { entries, .. } => {
                    nodes.extend(entries.iter().map(|entry| entry.key.nodes()));
                }
                RuleExtra::RewriteCell { before, .. } => nodes.push(before.nodes()),
                RuleExtra::RewriteState { before, .. } => state_nodes(before, &mut nodes),
                RuleExtra::RewriteList { before, .. } => {
                    nodes.extend(before.patterns().map(|item| item.pattern.nodes()));
                }
                RuleExtra::UpdateMap { .. } => {}
            }
        }
        match &self.head_result {
            Some(RuleHeadResult::Replace(term)) => nodes.push(term.nodes()),
            Some(RuleHeadResult::Splice { items, .. }) => {
                nodes.extend(items.iter().map(TermExpression::nodes));
            }
            None | Some(RuleHeadResult::Erase(_)) => {}
        }
        for extra in &self.extras {
            match extra {
                RuleExtra::RewriteState {
                    after: Some(after), ..
                } => state_nodes(after, &mut nodes),
                RuleExtra::UpdateMap { update, .. } => nodes.push(update.term().nodes()),
                RuleExtra::RewriteCell {
                    after: Some(after), ..
                } => nodes.push(after.nodes()),
                RuleExtra::RewriteList {
                    after: Some(after), ..
                } => {
                    nodes.extend(after.terms().into_iter().map(TermExpression::nodes));
                }
                _ => {}
            }
        }
        if let Some(requires) = self.rule.requires() {
            nodes.push(requires.term().nodes());
        }
        if let Some(ensures) = self.rule.existentials().ensures() {
            nodes.push(ensures.nodes());
        }
        crate::state_rule::allocate_claim_node_keys(
            keys,
            nodes.into_iter().map(|nodes| (nodes, TermKeys::default())),
        )
    }

    /// Returns the provenance of the clause's metadata attribute:
    /// `#[k::rule(..)]` for a rule, `#[k::claim(..)]` for a claim.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error if an authored token has no recoverable range.
    pub fn attribute_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        match &self.claim {
            Some(claim) => claim.provenance(),
            None => self.attribute.provenance(),
        }
    }

    /// Returns binding refinements in authored order.
    #[must_use]
    pub fn narrowings(&self) -> &[RuleNarrowing] {
        &self.narrowings
    }

    /// Returns the matched computation-cell items, absent for a cell-record
    /// clause that leaves the computation cell out.
    #[must_use]
    pub const fn head(&self) -> Option<&RuleHead> {
        self.head.as_ref()
    }

    /// Returns replacement, splice, or erasure head meaning, absent for a
    /// cell-record clause that leaves the computation cell out of its
    /// pattern or its result (which only reads it).
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

    /// Returns the List-collection reading of the computation cell's
    /// bracketed value when that value also reads as a List collection's
    /// instances (KF-023).
    #[must_use]
    pub fn bracket_alternative(&self) -> Option<&BracketAlternative> {
        self.bracket_alternative.as_deref()
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
        // The clause numbers its literal islands across all its cells, not
        // across the head item's alone.
        anchors.retain(|anchor| {
            !matches!(
                anchor.role(),
                ProvenanceRole::ClaimIdToken
                    | ProvenanceRole::ClaimBytesToken
                    | ProvenanceRole::ClaimAnonymous
                    | ProvenanceRole::ClaimAnonymousSort
                    | ProvenanceRole::ClaimAnonymousSpelling
                    | ProvenanceRole::ClaimOrBool
            )
        });
        let mut keys = KeyAllocator::continuing(anchors);
        self.allocate_claim_literal_keys(&mut keys)?;
        // A claim clause's name, its label, is anchored by its
        // `#[k::claim(..)]` (F7).
        if self.claim.is_none() && self.attribute.label().is_none() {
            keys.key(
                ProvenanceRole::RuleLabel,
                TokenRange::for_tokens(&self.rule.item.sig.ident)?,
            )?;
        }
        let mut anchors = keys.into_anchors();
        // A claim clause is a claim: its declaration has the claim role.
        if self.claim.is_some() {
            anchors = anchors
                .into_iter()
                .map(|anchor| {
                    if anchor.role() == ProvenanceRole::RuleDeclaration {
                        ProvenanceAnchor::new(
                            ProvenanceRole::ClaimDeclaration,
                            anchor.key().ordinal(),
                            anchor.range(),
                        )
                    } else {
                        anchor
                    }
                })
                .collect();
        }
        anchors.retain(|anchor| {
            !matches!(
                anchor.role(),
                ProvenanceRole::LexemeSort
                    | ProvenanceRole::LexemeText
                    | ProvenanceRole::SortTest
                    | ProvenanceRole::SortTestSort
                    | ProvenanceRole::ApplicationInstance
                    | ProvenanceRole::PatternAs
                    | ProvenanceRole::PatternAsBinding
                    | ProvenanceRole::PatternOr
                    | ProvenanceRole::Matches
                    | ProvenanceRole::MatchesWildcard
                    | ProvenanceRole::Let
                    | ProvenanceRole::LetSort
                    | ProvenanceRole::LetWildcard
                    | ProvenanceRole::MlConnective
                    | ProvenanceRole::MlBinder
                    | ProvenanceRole::MlBinderSort
                    | ProvenanceRole::RuleResult
                    | ProvenanceRole::RuleRightPath
                    | ProvenanceRole::RuleRightApplicationHead
                    | ProvenanceRole::RuleRightReference
                    | ProvenanceRole::RuleRightLiteral
                    | ProvenanceRole::RuleRightRecordFieldName
            )
        });
        let subject = self.head.as_ref().is_some_and(|head| head.subject);
        if !subject {
            // The placeholder subject of a clause without the computation cell
            // (or matching `[]`) has no authored tokens: the pattern is the whole subject record,
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
        }
        // The clause's own keys number on after the subject's: the
        // computation items after the first, the cells read, and the
        // wildcards of extra-cell patterns, such as `frame: _`, continue the
        // subject's left-hand ordinals in clause order.
        let mut keys = KeyAllocator::continuing(anchors);
        if !subject {
            keys.key(ProvenanceRole::RulePattern, self.layout.pattern)?;
        }
        keys.key(
            ProvenanceRole::RuleResult,
            self.head_result
                .as_ref()
                .map_or(Ok(self.layout.result), RuleHeadResult::range)?,
        )?;
        // Optional and collection states (KF-023) number their K-sequence
        // and instance keys per side; the right side continues after a
        // spliced head result's sequence keys.
        match &self.head_result {
            None | Some(RuleHeadResult::Erase(_)) => {}
            Some(RuleHeadResult::Replace(term)) => {
                allocate_rule_term_keys(&mut keys, &mut term.unkeyed(), RuleTermSide::Right)?;
            }
            Some(RuleHeadResult::Splice { range, items }) => {
                keys.key(ProvenanceRole::RuleRightKSequencePayload, *range)?;
                for item in items {
                    keys.key(
                        ProvenanceRole::RuleRightKSequenceItem,
                        TokenRange::for_tokens(item.expression())?,
                    )?;
                    allocate_rule_term_keys(&mut keys, &mut item.unkeyed(), RuleTermSide::Right)?;
                }
            }
        }
        for item in self.head.iter().flat_map(|head| &head.following) {
            allocate_rule_pattern_keys(&mut keys, &mut item.pattern.unkeyed(), &item.tree)?;
            allocate_wildcard_keys(
                &mut keys,
                &item.tree,
                &mut TermKeys::default(),
                ProvenanceRole::RuleLeftWildcard,
            )?;
        }
        for extra in &self.extras {
            allocate_extra_keys(&mut keys, extra)?;
        }
        if let Some(alternative) = &self.bracket_alternative {
            // The List reading's cell names and instance structure, numbered
            // after every other extra; its instance children are the head
            // record's terms, already keyed above.
            keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(&alternative.cell)?,
            )?;
            allocate_alternative_state_keys(&mut keys, &alternative.before, RuleTermSide::Left)?;
            if let (Some(result_cell), Some(after)) = (&alternative.result_cell, &alternative.after)
            {
                keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?;
                allocate_alternative_state_keys(&mut keys, after, RuleTermSide::Right)?;
            }
        }
        for narrowing in &self.narrowings {
            keys.key(
                ProvenanceRole::RuleBindingType,
                TokenRange::for_tokens(&narrowing.sort)?,
            )?;
        }
        self.allocate_island_keys(&mut keys)?;
        Ok(keys.into_anchors())
    }

    /// Numbers `k::lexeme!` terms, then `k::is!` and `k::project!` terms, in
    /// expansion order: the subject, the cells read, the head result, the
    /// cells written, the condition, then the ensures condition.
    fn allocate_island_keys(&self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        use crate::term::{allocate_lexeme_keys, allocate_sort_test_keys};
        let terms = self.expansion_order_nodes();
        for nodes in &terms {
            allocate_lexeme_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            allocate_sort_test_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_application_instance_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_pattern_as_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_pattern_or_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_matches_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_let_keys(keys, nodes, &mut TermKeys::default())?;
        }
        for nodes in &terms {
            crate::term::allocate_ml_binder_keys(keys, nodes, &mut TermKeys::default())?;
        }
        Ok(())
    }

    /// The term nodes of the clause in expansion order.
    fn expansion_order_nodes(&self) -> Vec<&[crate::term::TermNode]> {
        let mut terms = vec![self.rule.parameter().pattern.nodes()];
        terms.extend(
            self.head
                .iter()
                .flat_map(|head| &head.following)
                .map(|item| item.pattern.nodes()),
        );
        for extra in &self.extras {
            match extra {
                RuleExtra::HaveMap { entries, .. } => {
                    terms.extend(entries.iter().map(|entry| entry.key.nodes()));
                }
                RuleExtra::RewriteCell { before, .. } => terms.push(before.nodes()),
                RuleExtra::RewriteState { before, .. } => {
                    terms.extend(before.terms().into_iter().map(TermExpression::nodes));
                }
                RuleExtra::RewriteList { before, .. } => {
                    terms.extend(before.patterns().map(|item| item.pattern.nodes()));
                }
                RuleExtra::UpdateMap { .. } => {}
            }
        }
        match &self.head_result {
            Some(RuleHeadResult::Replace(term)) => terms.push(term.nodes()),
            Some(RuleHeadResult::Splice { items, .. }) => {
                terms.extend(items.iter().map(crate::term::TermExpression::nodes));
            }
            Some(RuleHeadResult::Erase(_)) | None => {}
        }
        for extra in &self.extras {
            match extra {
                RuleExtra::UpdateMap { update, .. } => terms.push(update.term().nodes()),
                RuleExtra::RewriteCell { after, .. } => {
                    terms.extend(after.iter().map(|after| after.nodes()));
                }
                RuleExtra::RewriteState { after, .. } => terms.extend(
                    after
                        .iter()
                        .flat_map(|after| after.terms())
                        .map(TermExpression::nodes),
                ),
                RuleExtra::RewriteList { after, .. } => terms.extend(
                    after
                        .iter()
                        .flat_map(|after| after.terms())
                        .map(TermExpression::nodes),
                ),
                RuleExtra::HaveMap { .. } => {}
            }
        }
        if let Some(requires) = self.rule.requires() {
            terms.push(requires.term().nodes());
        }
        if let Some(ensures) = self.rule.existentials().ensures() {
            terms.push(ensures.nodes());
        }
        terms
    }
}

/// Keys one extra cell: its field on each side it is written on, then its
/// terms. A map read numbers its keys and values per entry, across every
/// map read; a map update's base, key, and value are numbered as its
/// result cell is.
#[expect(
    clippy::too_many_lines,
    reason = "One arm per extra-cell form, each keying its cells in expansion order."
)]
fn allocate_extra_keys(keys: &mut KeyAllocator, extra: &RuleExtra) -> Result<(), SyntaxError> {
    match extra {
        RuleExtra::HaveMap { cell, entries } => {
            keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            for RuleMapEntry { key, value } in entries {
                keys.key(
                    ProvenanceRole::RuleLeftMapKey,
                    TokenRange::for_tokens(key.expression())?,
                )?;
                keys.key(
                    ProvenanceRole::RuleLeftMapValue,
                    TokenRange::for_tokens(value)?,
                )?;
                allocate_rule_term_keys(keys, &mut key.unkeyed(), RuleTermSide::Left)?;
                // A `_` key matches any entry's key.
                allocate_wildcard_keys(
                    keys,
                    key.tree(),
                    &mut TermKeys::default(),
                    ProvenanceRole::RuleLeftWildcard,
                )?;
            }
        }
        RuleExtra::UpdateMap { cell, update, .. } => {
            let [base, key, value] = update.arguments();
            let field = keys.key(
                ProvenanceRole::RuleRightCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            keys.paired(
                ProvenanceRole::RuleRightMapUpdateBase,
                &field,
                TokenRange::for_tokens(base)?,
            );
            keys.paired(
                ProvenanceRole::RuleRightMapKey,
                &field,
                TokenRange::for_tokens(key)?,
            );
            keys.paired(
                ProvenanceRole::RuleRightMapValue,
                &field,
                TokenRange::for_tokens(value)?,
            );
            allocate_rule_term_keys(keys, &mut update.term().unkeyed(), RuleTermSide::Right)?;
        }
        RuleExtra::RewriteState {
            cell,
            before,
            result_cell,
            after,
        } => {
            keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            allocate_readable_state_keys(keys, before, RuleTermSide::Left)?;
            if let (Some(result_cell), Some(after)) = (result_cell, after) {
                keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?;
                allocate_readable_state_keys(keys, after, RuleTermSide::Right)?;
            }
        }
        RuleExtra::RewriteList {
            cell,
            before,
            result_cell,
            after,
        } => {
            keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            for item in before.patterns() {
                allocate_rule_pattern_keys(keys, &mut item.pattern.unkeyed(), &item.tree)?;
                allocate_wildcard_keys(
                    keys,
                    &item.tree,
                    &mut TermKeys::default(),
                    ProvenanceRole::RuleLeftWildcard,
                )?;
            }
            if let (Some(result_cell), Some(after)) = (result_cell, after) {
                keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?;
                for term in after.terms() {
                    allocate_rule_term_keys(keys, &mut term.unkeyed(), RuleTermSide::Right)?;
                }
            }
        }
        RuleExtra::RewriteCell {
            cell,
            before,
            before_tree,
            after,
        } => {
            keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            allocate_rule_pattern_keys(keys, &mut before.unkeyed(), before_tree)?;
            allocate_wildcard_keys(
                keys,
                before_tree,
                &mut TermKeys::default(),
                ProvenanceRole::RuleLeftWildcard,
            )?;
            // A cell the result leaves out is read only and has no
            // result keys.
            if let Some(after) = after {
                keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(cell)?,
                )?;
                allocate_rule_term_keys(keys, &mut after.unkeyed(), RuleTermSide::Right)?;
            }
        }
    }
    Ok(())
}

/// Per-side ordinals of the K-sequence and collection anchors of readable
/// optional and collection states (KF-023). `krs-expand` numbers the keys in
/// the same traversal order.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReadableStateCounters {
    /// Next `k` payload ordinal.
    pub k_payload: usize,
    /// Next `k` item ordinal.
    pub k_item: usize,
    /// Next `k` tail ordinal.
    pub k_tail: usize,
    /// Next instance-record ordinal.
    pub instance: usize,
    /// Next instance child-field ordinal.
    pub instance_field: usize,
    /// Next collection-rest ordinal.
    pub instances_rest: usize,
}

impl ReadableStateCounters {
    /// The right side's counters: a spliced head result owns sequence payload
    /// `#0` and the first item ordinals.
    #[must_use]
    pub fn after_head(head: Option<&RuleHeadResult>) -> Self {
        match head {
            Some(RuleHeadResult::Splice { items, .. }) => Self {
                k_payload: 1,
                k_item: items.len(),
                ..Self::default()
            },
            _ => Self::default(),
        }
    }
}

/// Keys a readable cell state on `side`: a term's nodes, a `k!`'s structure
/// and items, and a collection's instances, child fields, and rest, in the
/// order expansion visits them.
fn allocate_readable_state_keys(
    keys: &mut KeyAllocator,
    state: &crate::StateTerm,
    side: RuleTermSide,
) -> Result<(), SyntaxError> {
    let left = matches!(side, RuleTermSide::Left);
    let role = |left_role: ProvenanceRole, right_role: ProvenanceRole| {
        if left { left_role } else { right_role }
    };
    match state {
        crate::StateTerm::Present(inner) => {
            allocate_readable_state_keys(keys, inner, side)?;
        }
        crate::StateTerm::Absent(_) => {}
        crate::StateTerm::Term(term) | crate::StateTerm::Group(term) => {
            allocate_readable_term_keys(keys, term, side)?;
        }
        crate::StateTerm::KSequence(sequence) => {
            for anchor in sequence.provenance()? {
                let target = match anchor.role() {
                    ProvenanceRole::KSequencePayload => role(
                        ProvenanceRole::RuleLeftKSequencePayload,
                        ProvenanceRole::RuleRightKSequencePayload,
                    ),
                    ProvenanceRole::KSequenceItem => role(
                        ProvenanceRole::RuleLeftKSequenceItem,
                        ProvenanceRole::RuleRightKSequenceItem,
                    ),
                    ProvenanceRole::KSequenceTail => role(
                        ProvenanceRole::RuleLeftKSequenceTail,
                        ProvenanceRole::RuleRightKSequenceTail,
                    ),
                    _ => continue,
                };
                keys.key(target, anchor.range())?;
            }
            for item in sequence.items() {
                allocate_readable_term_keys(keys, item, side)?;
            }
        }
        crate::StateTerm::Map(_) => {
            return Err(SyntaxError::new(
                crate::SyntaxErrorKind::InvalidStateMacro {
                    macro_name: "rules",
                    reason: "a readable collection instance holds terms and `[..]` sequences; write a map child with `cells!`",
                },
                proc_macro2::Span::call_site(),
            ));
        }
        crate::StateTerm::Instances(list) => {
            let instance = |keys: &mut KeyAllocator, item: &crate::InstanceItem| {
                keys.key(
                    role(
                        ProvenanceRole::RuleLeftCellsInstance,
                        ProvenanceRole::RuleRightCellsInstance,
                    ),
                    item.range(),
                )?;
                for field in item.fields() {
                    keys.key(
                        role(
                            ProvenanceRole::RuleLeftCellsInstanceField,
                            ProvenanceRole::RuleRightCellsInstanceField,
                        ),
                        TokenRange::for_tokens(field.name())?,
                    )?;
                    allocate_readable_state_keys(keys, field.value(), side)?;
                }
                Ok::<_, SyntaxError>(())
            };
            for item in list.front() {
                instance(keys, item)?;
            }
            if let Some(range) = list.rest().range() {
                keys.key(
                    role(
                        ProvenanceRole::RuleLeftCellsInstancesRest,
                        ProvenanceRole::RuleRightCellsInstancesRest,
                    ),
                    range,
                )?;
            }
            for item in list.back() {
                instance(keys, item)?;
            }
        }
    }
    Ok(())
}

/// Keys the structure of a bracket alternative's instance list: each
/// instance record, each child name, and the rest. The children's terms are
/// the head record's, which the clause keys already.
fn allocate_alternative_state_keys(
    keys: &mut KeyAllocator,
    state: &crate::StateTerm,
    side: RuleTermSide,
) -> Result<(), SyntaxError> {
    let left = matches!(side, RuleTermSide::Left);
    let role = |left_role: ProvenanceRole, right_role: ProvenanceRole| {
        if left { left_role } else { right_role }
    };
    let crate::StateTerm::Instances(list) = state else {
        return Ok(());
    };
    let instance = |keys: &mut KeyAllocator, item: &crate::InstanceItem| {
        keys.key(
            role(
                ProvenanceRole::RuleLeftCellsInstance,
                ProvenanceRole::RuleRightCellsInstance,
            ),
            item.range(),
        )?;
        for field in item.fields() {
            keys.key(
                role(
                    ProvenanceRole::RuleLeftCellsInstanceField,
                    ProvenanceRole::RuleRightCellsInstanceField,
                ),
                TokenRange::for_tokens(field.name())?,
            )?;
        }
        Ok::<_, SyntaxError>(())
    };
    for item in list.front() {
        instance(keys, item)?;
    }
    for item in list.back() {
        instance(keys, item)?;
    }
    if let Some(range) = list.rest().range() {
        keys.key(
            role(
                ProvenanceRole::RuleLeftCellsInstancesRest,
                ProvenanceRole::RuleRightCellsInstancesRest,
            ),
            range,
        )?;
    }
    Ok(())
}

/// Keys a readable term's nodes on `side` and, on the left, its wildcards.
fn allocate_readable_term_keys(
    keys: &mut KeyAllocator,
    term: &TermExpression,
    side: RuleTermSide,
) -> Result<(), SyntaxError> {
    allocate_rule_term_keys(keys, &mut term.unkeyed(), side)?;
    if matches!(side, RuleTermSide::Left) {
        allocate_wildcard_keys(
            keys,
            term.tree(),
            &mut TermKeys::default(),
            ProvenanceRole::RuleLeftWildcard,
        )?;
    }
    Ok(())
}

/// A readable family of independently named ordinary term rules.
#[derive(Clone, Debug)]
pub struct RuleBlock {
    sort: TermSort,
    configuration: bool,
    imports: Vec<ItemUse>,
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

    /// Returns the block's `use` items in authored order. Every path of the
    /// block resolves with them in scope, as the same items would in Rust.
    #[must_use]
    pub fn imports(&self) -> &[ItemUse] {
        &self.imports
    }

    /// Returns independent clauses in authored order. Their order has no
    /// semantic priority.
    #[must_use]
    pub fn clauses(&self) -> &[RuleClause] {
        &self.clauses
    }

    fn from_stream(input: ParseStream<'_>) -> Result<Self, ParseError> {
        Self::from_stream_of(input, ReadableSentence::Rule)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One linear parser keeps clause diagnostics at authored tokens."
    )]
    fn from_stream_of(
        input: ParseStream<'_>,
        sentence: ReadableSentence,
    ) -> Result<Self, ParseError> {
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

        // Any number of `use` items, which resolve the block's paths as
        // Rust resolves a scope's paths: an explicit import shadows a glob,
        // and a name two globs supply is ambiguous only where it is used.
        let mut imports = Vec::new();
        while input.peek(Token![use]) {
            imports.push(input.parse::<ItemUse>()?);
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
            // A claim states whole configurations (F7).
            if sentence == ReadableSentence::Claim && !machine_clause {
                return Err(syn::Error::new(
                    name.span(),
                    "a `k::claims!` clause is a pair of cell records `{ .. } => { .. }` over the block's configuration",
                )
                .into());
            }
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
                    &attributes,
                    &name,
                    &sort_type,
                    clause_start,
                    sentence,
                )?);
                continue;
            }
            let fork = input.fork();
            let (pattern, signs) = parse_pattern_with_signs(input)
                .map_err(|error| crate::notation::pattern_parse_error(&fork, error))?;
            // A pattern may stop before `&&`, `||`, or a method call.
            if !input.peek(Token![=>])
                && let Some(error) = crate::notation::notation_at(&fork)
            {
                return Err(error.into());
            }
            input.parse::<Token![=>]>()?;
            let result_tokens = input.fork();
            let result = input.parse::<Expr>();
            if result.is_err() || input.peek(Token![@]) {
                // `name @ pattern` binds only on a left-hand side; syn would
                // report it as an unexpected token.
                let mut tokens = proc_macro2::TokenStream::new();
                while !result_tokens.is_empty() && !result_tokens.peek(Token![;]) {
                    tokens.extend([result_tokens.parse::<proc_macro2::TokenTree>()?]);
                }
                crate::term::reject_pattern_alias(&tokens)?;
            }
            let result: Expr = result?;
            // The clause's item below may hold a placeholder result, so the
            // fields of the pattern's bit templates are written into the
            // clause's own result here.
            let mut substituted = result.clone();
            super::bits::substitute_clause_result(&pattern, &mut substituted)?;
            let head_result = parse_head_result(substituted)?;
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
                            if let Some(error) = parametric_collection_error(&sort, true) {
                                return Err(error.into());
                            }
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
                    // A trailing comma before the `;` ends the list.
                    if input.peek(Token![;]) {
                        break;
                    }
                }
            }
            let semicolon = input.parse::<Token![;]>()?;

            let (attribute, retained) = take_rule_clause_attribute(attributes)?;
            let placeholder = match &head_result {
                RuleHeadResult::Replace(_) => result,
                RuleHeadResult::Splice { .. } | RuleHeadResult::Erase(_) => syn::parse_quote!(true),
            };
            // A parameter takes one pattern, so a top-level `A | B` is
            // parenthesised to parse and then restored, keeping every range
            // on the authored tokens.
            let top_level_or = matches!(pattern, syn::Pat::Or(_));
            let parameter = if top_level_or {
                quote!((#pattern))
            } else {
                quote!(#pattern)
            };
            let mut item: ItemFn = syn::parse2(quote! {
                #(#retained)*
                pub fn #name(#parameter: #sort_type) -> #sort_type { #placeholder }
            })?;
            if top_level_or && let Some(syn::FnArg::Typed(typed)) = item.sig.inputs.first_mut() {
                *typed.pat = pattern.clone();
            }
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
            // `have` marks every name it introduces with `let`, so a key
            // name is a reference to a binding of the rule; reading any
            // entry is the record read's free key.
            for extra in &extras {
                let TermTableExtra::Have(have) = extra else {
                    continue;
                };
                for node in have.key.nodes() {
                    if let crate::TermNode::Reference(path) = node
                        && let Some(name) = crate::path::pattern_binder(path)
                        && !bindings
                            .iter()
                            .any(|binding| binding.unraw() == name.unraw())
                    {
                        return Err(syn::Error::new(
                            name.span(),
                            format!(
                                "`{name}` is bound nowhere in this rule; `have` reads the entry at a key the rule already knows; to read any entry, bind the key with a record read `{cell}: {{ {name} -> {value}, .. }}`",
                                name = name.unraw(),
                                cell = have.cell.unraw(),
                                value = have.value.unraw(),
                            ),
                        )
                        .into());
                    }
                }
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
            let clause = RuleClause {
                rule,
                attribute,
                narrowings,
                head: Some(RuleHead {
                    subject: true,
                    following: Vec::new(),
                    exact: false,
                }),
                head_result: Some(head_result),
                extras: extras.into_iter().map(RuleExtra::from).collect(),
                bindings,
                computation_cell: None,
                source_range: TokenRange::new(clause_start, semicolon.span),
                layout,
                bracket_alternative: None,
                claim: None,
            };
            clause.check_existentials()?;
            clauses.push(clause);
        }
        if clauses.is_empty() {
            return Err(input
                .error("a readable rule block requires at least one clause")
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

/// A readable block of reachability claims, `k::claims!` (F7): the claim
/// counterpart of a `for Configuration` rule block. Each clause `label:
/// subject => result;` is the `#[k::claim]` fn whose `cells!` records its
/// readable records stand for, labelled by its name.
#[derive(Clone, Debug)]
pub struct ClaimBlock {
    block: RuleBlock,
}

impl ClaimBlock {
    /// Returns the configuration type the clauses' records are over.
    #[must_use]
    pub const fn sort(&self) -> &TermSort {
        self.block.sort()
    }

    /// Returns the block's `use` items in authored order.
    #[must_use]
    pub fn imports(&self) -> &[ItemUse] {
        self.block.imports()
    }

    /// Returns the claims in authored order; each [`RuleClause::claim`] is
    /// present.
    #[must_use]
    pub fn clauses(&self) -> &[RuleClause] {
        self.block.clauses()
    }

    /// Returns the clauses as a configuration-owned readable block, which
    /// they share the grammar and expansion of.
    #[must_use]
    pub const fn block(&self) -> &RuleBlock {
        &self.block
    }
}

impl KrsSyntax for ClaimBlock {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, |input| -> Result<Self, ParseError> {
            Ok(Self {
                block: RuleBlock::from_stream_of(input, ReadableSentence::Claim)?,
            })
        })
    }
}

/// Parses a readable claim block together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`ClaimBlock::parse_tokens`] and
/// rejects non-documentation block comments with a byte-exact source range.
pub fn parse_claim_block_source_with_trivia(
    source: &str,
) -> Result<(ClaimBlock, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("k::claims")?;
    Ok((ClaimBlock::parse_tokens(tokens)?, trivia))
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

/// Takes a `k::claims!` clause's `#[k::claim(..)]`, which states its
/// modality, and keeps the helpers a claim takes (`#[k::requires]`,
/// `#[k::exists]`, `#[k::ensures]`, and doc comments) for its rule item. A
/// rule's `#[k::rule(..)]` and `#[k::fresh]` have no meaning on a claim.
pub(super) fn take_claim_clause_attribute(
    attributes: Vec<Attribute>,
    name: &Ident,
) -> Result<(crate::ClaimAttribute, Vec<Attribute>), SyntaxError> {
    let mut claim = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in attributes {
        let helper = attribute
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string());
        match helper.as_deref() {
            Some("claim") => {
                if claim.is_some() {
                    return Err(unsupported_signature(
                        "a claim clause carries one `#[k::claim(..)]`",
                        attribute.span(),
                    ));
                }
                let Meta::List(list) = &attribute.meta else {
                    return Err(unsupported_signature(
                        "`#[k::claim(..)]` states the claim's modality: `#[k::claim(all_paths)]` or `#[k::claim(one_path)]`",
                        attribute.span(),
                    ));
                };
                claim = Some(crate::ClaimAttribute::parse_clause_tokens(
                    list.tokens.clone(),
                    name,
                )?);
            }
            Some(other @ ("rule" | "fresh")) => {
                return Err(unsupported_signature(
                    if other == "rule" {
                        "`#[k::rule(..)]` is a rule's metadata; a claim clause takes `#[k::claim(..)]`"
                    } else {
                        "`#[k::fresh]` draws values in a rule step; a claim has no fresh binders"
                    },
                    attribute.span(),
                ));
            }
            _ => retained.push(attribute),
        }
    }
    let claim = claim.ok_or_else(|| {
        unsupported_signature(
            "a claim clause states its modality: write `#[k::claim(all_paths)]` or `#[k::claim(one_path)]` before it",
            name.span(),
        )
    })?;
    Ok((claim, retained))
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
