use proc_macro2::TokenStream;
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemUse, Meta, Path, Token, Type};

use super::condition::{
    HaveMapExtra, MapUpdateExtra, RuleExtra, condition_token_range, parse_have_extra,
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
use crate::state_macro::StatePosition;
use crate::term::{IslandKeys, TermVisit};
use crate::term_sort::{TermSort, parse_readable_sort};
use crate::{
    ProvenanceAnchor, ProvenanceRole, RuleSide, SyntaxError, TermExpression, TermTree, TokenRange,
};
use krs_ir::ProvenanceKey;

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
    sort_key: Option<ProvenanceKey>,
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
    pub(super) const fn new(binding: Ident, sort: Path) -> Self {
        Self {
            binding,
            sort,
            sort_key: None,
        }
    }

    /// The key of the sort path, given by the clause's keying.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

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

    /// The patterns of [`Self::patterns`], for a pass that keys them.
    fn patterns_mut(&mut self) -> impl Iterator<Item = &mut RuleHeadItem> {
        let rest = match &mut self.rest {
            RuleListRest::Named(rest) => Some(rest),
            RuleListRest::Exact | RuleListRest::Shared(_) => None,
        };
        self.items.iter_mut().chain(rest).chain(&mut self.back)
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

    /// The terms of [`Self::terms`], for a pass that keys them.
    fn terms_mut(&mut self) -> impl Iterator<Item = &mut TermExpression> {
        let rest = match &mut self.rest {
            RuleListRest::Named(rest) => Some(rest),
            RuleListRest::Exact | RuleListRest::Shared(_) => None,
        };
        self.items.iter_mut().chain(rest).chain(&mut self.back)
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
    pub(super) computation_cell: Option<ComputationCell>,
    pub(super) source_range: TokenRange,
    pub(super) layout: RuleClauseLayout,
    pub(super) bracket_alternative: Option<Box<BracketAlternative>>,
    /// The modality and flags of a `k::claims!` clause (F7), which is then a
    /// claim and carries no `#[k::rule]` metadata.
    pub(super) claim: Option<crate::ClaimAttribute>,
    /// The keys of the clause's own nodes, which no part holds.
    pub(super) keys: ClauseKeys,
    /// The anchors of the clause's keying.
    pub(super) anchors: Vec<ProvenanceAnchor>,
}

/// The computation cell a cell-record clause names: its field in the
/// subject record and, when the result restates the cell, in the result
/// record.
#[derive(Clone, Debug)]
pub(super) struct ComputationCell {
    pub(super) cell: Ident,
    pub(super) result_cell: Option<Ident>,
}

/// The keys a readable clause gives the nodes it anchors that are no term,
/// binder or state of its own parts.
#[derive(Clone, Debug, Default)]
pub(super) struct ClauseKeys {
    label: Option<ProvenanceKey>,
    pattern: Option<ProvenanceKey>,
    result: Option<ProvenanceKey>,
    splice: Option<ProvenanceKey>,
    extras: Vec<RuleExtraKeys>,
    computation_cell: RuleExtraKeys,
}

/// The keys a readable clause gives one cell's names, an extra cell's or the
/// computation cell's: the cell as the subject record names it, and as the
/// result record restates it (for a map update, the cell it writes).
#[derive(Clone, Debug, Default)]
pub struct RuleExtraKeys {
    cell: Option<ProvenanceKey>,
    result_cell: Option<ProvenanceKey>,
}

impl RuleExtraKeys {
    /// The key of the cell's name in the subject record, absent for a map
    /// update, which only writes the cell.
    #[must_use]
    pub const fn cell(&self) -> Option<&ProvenanceKey> {
        self.cell.as_ref()
    }

    /// The key of the cell's name in the result record, absent for a cell
    /// the clause only reads.
    #[must_use]
    pub const fn result_cell(&self) -> Option<&ProvenanceKey> {
        self.result_cell.as_ref()
    }
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
    pub(super) cell_key: Option<ProvenanceKey>,
    pub(super) result_cell_key: Option<ProvenanceKey>,
}

impl BracketAlternative {
    /// The key of the cell's name in the subject record, in this reading.
    #[must_use]
    pub const fn cell_key(&self) -> Option<&ProvenanceKey> {
        self.cell_key.as_ref()
    }

    /// The key of the cell's name in the result record, in this reading.
    #[must_use]
    pub const fn result_cell_key(&self) -> Option<&ProvenanceKey> {
        self.result_cell_key.as_ref()
    }

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

    /// Keys the clause as a sentence of its own and stores its anchors.
    pub(super) fn keyed(&mut self) -> Result<(), SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(())
    }

    /// Forgets the keys of the clause's own parts, before its pass keys
    /// them; the item's pass clears the item's.
    fn clear_keys(&mut self) {
        self.keys = ClauseKeys::default();
        for item in self.head.iter_mut().flat_map(|head| &mut head.following) {
            item.pattern.clear_keys();
        }
        match &mut self.head_result {
            Some(RuleHeadResult::Replace(term)) => term.clear_keys(),
            Some(RuleHeadResult::Splice { items, .. }) => {
                for item in items {
                    item.clear_keys();
                }
            }
            Some(RuleHeadResult::Erase(_)) | None => {}
        }
        for extra in &mut self.extras {
            match extra {
                RuleExtra::HaveMap { entries, .. } => {
                    for entry in entries {
                        entry.key.clear_keys();
                        entry.value_key = None;
                    }
                }
                RuleExtra::UpdateMap { update, .. } => update.clear_keys(),
                RuleExtra::RewriteCell { before, after, .. } => {
                    before.clear_keys();
                    if let Some(after) = after {
                        after.clear_keys();
                    }
                }
                RuleExtra::RewriteState { before, after, .. } => {
                    before.clear_keys();
                    if let Some(after) = after {
                        after.clear_keys();
                    }
                }
                RuleExtra::RewriteList { before, after, .. } => {
                    for item in before.patterns_mut() {
                        item.pattern.clear_keys();
                    }
                    for term in after.iter_mut().flat_map(|after| after.terms_mut()) {
                        term.clear_keys();
                    }
                }
            }
        }
        // The List reading's instance structure is keyed again below. Its
        // children are the head record's terms read a second way: the clause
        // keys those terms in its primary reading, so the children hold no
        // keys.
        if let Some(alternative) = &mut self.bracket_alternative {
            alternative.cell_key = None;
            alternative.result_cell_key = None;
            alternative.before.clear_keys();
            if let Some(after) = &mut alternative.after {
                after.clear_keys();
            }
        }
        for narrowing in &mut self.narrowings {
            narrowing.sort_key = None;
        }
    }

    /// Keys the clause: its item's nodes, in the item's order and under the
    /// declaration role of its sentence; the claim-only literals of every
    /// cell; the label; the subject record when the subject is no
    /// computation item; the result and the head result's terms; the
    /// computation items after the first; the extra cells; the List reading
    /// of a bracketed cell; the narrowings; the islands of every term in
    /// expansion order; then the computation cell's names, in the subject
    /// record and in the result record. The clause numbers its literals and
    /// islands across all its cells, not across the item's alone, and it
    /// keys its own result, so the item's result term holds no keys. The
    /// computation cell's names come last so that keying them moves no other
    /// node's key or anchor: the extra cells' names share their roles, and
    /// keyed before them they would shift those cells' ordinals.
    fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        use crate::term::{
            allocate_application_instance_keys, allocate_let_keys, allocate_lexeme_keys,
            allocate_matches_keys, allocate_ml_binder_keys, allocate_pattern_as_keys,
            allocate_pattern_or_keys, allocate_sort_test_keys,
        };
        let subject = self.head.as_ref().is_some_and(|head| head.subject);
        // A claim clause is a claim: its declaration has the claim role.
        let declaration = if self.claim.is_some() {
            ProvenanceRole::ClaimDeclaration
        } else {
            ProvenanceRole::RuleDeclaration
        };
        self.rule.allocate_clause_keys(keys, declaration, subject)?;
        self.visit_terms(&mut |nodes, term_keys| {
            crate::state_rule::allocate_claim_node_keys(keys, [(nodes, term_keys)])
        })?;
        // A claim clause's name, its label, is anchored by its
        // `#[k::claim(..)]` (F7).
        if self.claim.is_none() && self.attribute.label().is_none() {
            self.keys.label = Some(keys.key(
                ProvenanceRole::RuleLabel,
                TokenRange::for_tokens(&self.rule.item.sig.ident)?,
            )?);
        }
        // The clause's own keys number on after the subject's: the
        // computation items after the first, the cells read, and the
        // wildcards of extra-cell patterns, such as `frame: _`, continue the
        // subject's left-hand ordinals in clause order. The placeholder
        // subject of a clause without the computation cell (or matching
        // `[]`) has no authored tokens: the pattern is the whole subject
        // record, and every left-side key comes from the cells.
        if !subject {
            self.keys.pattern = Some(keys.key(ProvenanceRole::RulePattern, self.layout.pattern)?);
        }
        let result = self
            .head_result
            .as_ref()
            .map_or(Ok(self.layout.result), RuleHeadResult::range)?;
        let result = keys.key(ProvenanceRole::RuleResult, result)?;
        self.keys.result = Some(result.clone());
        // Optional and collection states (KF-023) number their K-sequence
        // and instance keys per side; the right side continues after a
        // spliced head result's sequence keys.
        match &mut self.head_result {
            None | Some(RuleHeadResult::Erase(_)) => {}
            Some(RuleHeadResult::Replace(term)) => {
                term.keying().2.set_payload(result);
                allocate_rule_term_keys(keys, term, RuleTermSide::Right)?;
            }
            Some(RuleHeadResult::Splice { range, items }) => {
                self.keys.splice =
                    Some(keys.key(ProvenanceRole::RuleRightKSequencePayload, *range)?);
                for item in items {
                    item.allocate_payload_key(keys, ProvenanceRole::RuleRightKSequenceItem)?;
                    allocate_rule_term_keys(keys, item, RuleTermSide::Right)?;
                }
            }
        }
        for item in self.head.iter_mut().flat_map(|head| &mut head.following) {
            allocate_head_item_keys(keys, item)?;
        }
        self.keys.extras = self
            .extras
            .iter_mut()
            .map(|extra| allocate_extra_keys(keys, extra))
            .collect::<Result<_, _>>()?;
        if let Some(alternative) = &mut self.bracket_alternative {
            // The List reading's cell names and instance structure, numbered
            // after every other extra; its instance children are the head
            // record's terms, already keyed above.
            alternative.cell_key = Some(keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(&alternative.cell)?,
            )?);
            allocate_alternative_state_keys(keys, &mut alternative.before, RuleSide::Left)?;
            if let (Some(result_cell), Some(after)) =
                (&alternative.result_cell, &mut alternative.after)
            {
                alternative.result_cell_key = Some(keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?);
                allocate_alternative_state_keys(keys, after, RuleSide::Right)?;
            }
        }
        for narrowing in &mut self.narrowings {
            narrowing.sort_key = Some(keys.key(
                ProvenanceRole::RuleBindingType,
                TokenRange::for_tokens(&narrowing.sort)?,
            )?);
        }
        // `k::lexeme!` terms, then `k::is!` and `k::project!` terms, then the
        // other islands, each kind in expansion order.
        let islands: [IslandKeys; 8] = [
            allocate_lexeme_keys,
            allocate_sort_test_keys,
            allocate_application_instance_keys,
            allocate_pattern_as_keys,
            allocate_pattern_or_keys,
            allocate_matches_keys,
            allocate_let_keys,
            allocate_ml_binder_keys,
        ];
        for island in islands {
            self.visit_terms(&mut |nodes, term_keys| island(keys, nodes, term_keys))?;
        }
        self.allocate_computation_cell_keys(keys)
    }

    /// Keys the computation cell's fields, in the subject record and in the
    /// result record, after every other node of the clause.
    fn allocate_computation_cell_keys(
        &mut self,
        keys: &mut KeyAllocator,
    ) -> Result<(), SyntaxError> {
        let Some(computation) = &self.computation_cell else {
            return Ok(());
        };
        self.keys.computation_cell.cell = Some(keys.key(
            ProvenanceRole::RuleLeftCellsField,
            TokenRange::for_tokens(&computation.cell)?,
        )?);
        if let Some(result_cell) = &computation.result_cell {
            self.keys.computation_cell.result_cell = Some(keys.key(
                ProvenanceRole::RuleRightCellsField,
                TokenRange::for_tokens(result_cell)?,
            )?);
        }
        Ok(())
    }

    /// Calls `visit` on the nodes and keys of each term of the clause, once
    /// each, in the order expansion visits them: the subject (a placeholder
    /// has neither literals nor islands), the computation items after the
    /// first, the terms of the cells read, the head result's, the terms
    /// written into the other cells, then the `requires` and `ensures`
    /// conditions. A state's terms include those of the states nested in
    /// it ([`crate::StateTerm::terms_mut`]).
    fn visit_terms(&mut self, visit: &mut TermVisit<'_>) -> Result<(), SyntaxError> {
        let (nodes, term_keys) = self.rule.parameter.pattern.keying();
        visit(nodes, term_keys)?;
        for item in self.head.iter_mut().flat_map(|head| &mut head.following) {
            let (nodes, term_keys) = item.pattern.keying();
            visit(nodes, term_keys)?;
        }
        for extra in &mut self.extras {
            match extra {
                RuleExtra::HaveMap { entries, .. } => {
                    for entry in entries {
                        visit_term(&mut entry.key, visit)?;
                    }
                }
                RuleExtra::RewriteCell { before, .. } => {
                    let (nodes, term_keys) = before.keying();
                    visit(nodes, term_keys)?;
                }
                RuleExtra::RewriteState { before, .. } => visit_state(before, visit)?,
                RuleExtra::RewriteList { before, .. } => {
                    for item in before.patterns_mut() {
                        let (nodes, term_keys) = item.pattern.keying();
                        visit(nodes, term_keys)?;
                    }
                }
                RuleExtra::UpdateMap { .. } => {}
            }
        }
        match &mut self.head_result {
            Some(RuleHeadResult::Replace(term)) => visit_term(term, visit)?,
            Some(RuleHeadResult::Splice { items, .. }) => {
                for item in items {
                    visit_term(item, visit)?;
                }
            }
            Some(RuleHeadResult::Erase(_)) | None => {}
        }
        for extra in &mut self.extras {
            match extra {
                RuleExtra::UpdateMap { update, .. } => visit_term(update.term_mut(), visit)?,
                RuleExtra::RewriteCell {
                    after: Some(after), ..
                } => visit_term(after, visit)?,
                RuleExtra::RewriteState {
                    after: Some(after), ..
                } => visit_state(after, visit)?,
                RuleExtra::RewriteList {
                    after: Some(after), ..
                } => {
                    for term in after.terms_mut() {
                        visit_term(term, visit)?;
                    }
                }
                RuleExtra::HaveMap { .. }
                | RuleExtra::RewriteCell { after: None, .. }
                | RuleExtra::RewriteState { after: None, .. }
                | RuleExtra::RewriteList { after: None, .. } => {}
            }
        }
        if let Some(requires) = self.rule.requires_mut() {
            visit_term(requires.term_mut(), visit)?;
        }
        if let Some(ensures) = self.rule.existentials_mut().ensures_mut() {
            visit_term(ensures, visit)?;
        }
        Ok(())
    }

    /// The key of the clause's name when it is the rule's label: a rule
    /// clause without a `#[k::rule(label = ..)]`; a claim clause's label is
    /// its `#[k::claim(..)]`'s.
    #[must_use]
    pub const fn label_key(&self) -> Option<&ProvenanceKey> {
        self.keys.label.as_ref()
    }

    /// The key of the whole subject record, when the subject is no
    /// computation item and the item's pattern is a placeholder.
    #[must_use]
    pub const fn pattern_key(&self) -> Option<&ProvenanceKey> {
        self.keys.pattern.as_ref()
    }

    /// The key of the clause's result: the head result (for a replacement,
    /// also its term's payload key), or the whole result record of a
    /// clause whose result leaves the computation cell out.
    #[must_use]
    pub const fn result_key(&self) -> Option<&ProvenanceKey> {
        self.keys.result.as_ref()
    }

    /// The key of a spliced head result's `k![..]` payload; each item's key
    /// is its term's payload key.
    #[must_use]
    pub const fn splice_key(&self) -> Option<&ProvenanceKey> {
        self.keys.splice.as_ref()
    }

    /// The keys of each extra cell's names, indexed as [`Self::extras`].
    #[must_use]
    pub fn extra_keys(&self) -> &[RuleExtraKeys] {
        &self.keys.extras
    }

    /// The keys of the computation cell's names, as the subject record names
    /// it and as the result record restates it; both absent for a clause
    /// that names no computation cell.
    #[must_use]
    pub const fn computation_cell_keys(&self) -> &RuleExtraKeys {
        &self.keys.computation_cell
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
    pub fn computation_cell(&self) -> Option<&Ident> {
        self.computation_cell
            .as_ref()
            .map(|computation| &computation.cell)
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

    /// Returns the exact descriptor provenance for the completed head rule:
    /// the anchors of the clause's keying.
    ///
    /// # Errors
    ///
    /// None: the clause was keyed when its block was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }
}

fn visit_term(term: &mut TermExpression, visit: &mut TermVisit<'_>) -> Result<(), SyntaxError> {
    let (nodes, _, term_keys) = term.keying();
    visit(nodes, term_keys)
}

fn visit_state(state: &mut crate::StateTerm, visit: &mut TermVisit<'_>) -> Result<(), SyntaxError> {
    for term in state.terms_mut() {
        visit_term(term, visit)?;
    }
    Ok(())
}

/// Keys a left-hand computation item or list element: its paths, nodes and
/// record field names, then its wildcards.
fn allocate_head_item_keys(
    keys: &mut KeyAllocator,
    item: &mut RuleHeadItem,
) -> Result<(), SyntaxError> {
    allocate_rule_pattern_keys(keys, &mut item.pattern, &item.tree)?;
    let (_, term_keys) = item.pattern.keying();
    allocate_wildcard_keys(
        keys,
        &item.tree,
        term_keys,
        ProvenanceRole::RuleLeftWildcard,
    )
}

/// Keys one extra cell: its field on each side it is written on, then its
/// terms, and returns the keys of its names. A map read numbers its keys
/// and values per entry, across every map read; a map update's base, key,
/// and value are numbered as its result cell is.
#[expect(
    clippy::too_many_lines,
    reason = "One arm per extra-cell form, each keying its cells in expansion order."
)]
fn allocate_extra_keys(
    keys: &mut KeyAllocator,
    extra: &mut RuleExtra,
) -> Result<RuleExtraKeys, SyntaxError> {
    let mut names = RuleExtraKeys::default();
    match extra {
        RuleExtra::HaveMap { cell, entries } => {
            names.cell = Some(keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?);
            for entry in entries {
                entry
                    .key
                    .allocate_payload_key(keys, ProvenanceRole::RuleLeftMapKey)?;
                entry.value_key = Some(keys.key(
                    ProvenanceRole::RuleLeftMapValue,
                    TokenRange::for_tokens(&entry.value)?,
                )?);
                allocate_rule_term_keys(keys, &mut entry.key, RuleTermSide::Left)?;
                // A `_` key matches any entry's key.
                let (_, tree, term_keys) = entry.key.keying();
                allocate_wildcard_keys(keys, tree, term_keys, ProvenanceRole::RuleLeftWildcard)?;
            }
        }
        RuleExtra::UpdateMap { cell, update, .. } => {
            let [base, key, value] = update.arguments().map(TokenRange::for_tokens);
            let field = keys.key(
                ProvenanceRole::RuleRightCellsField,
                TokenRange::for_tokens(cell)?,
            )?;
            update.set_argument_keys([
                keys.paired(ProvenanceRole::RuleRightMapUpdateBase, &field, base?)?,
                keys.paired(ProvenanceRole::RuleRightMapKey, &field, key?)?,
                keys.paired(ProvenanceRole::RuleRightMapValue, &field, value?)?,
            ]);
            names.result_cell = Some(field);
            allocate_rule_term_keys(keys, update.term_mut(), RuleTermSide::Right)?;
        }
        RuleExtra::RewriteState {
            cell,
            before,
            result_cell,
            after,
        } => {
            names.cell = Some(keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?);
            allocate_readable_state_keys(keys, before, RuleTermSide::Left)?;
            if let (Some(result_cell), Some(after)) = (result_cell, after) {
                names.result_cell = Some(keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?);
                allocate_readable_state_keys(keys, after, RuleTermSide::Right)?;
            }
        }
        RuleExtra::RewriteList {
            cell,
            before,
            result_cell,
            after,
        } => {
            names.cell = Some(keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?);
            for item in before.patterns_mut() {
                allocate_head_item_keys(keys, item)?;
            }
            if let (Some(result_cell), Some(after)) = (result_cell, after) {
                names.result_cell = Some(keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(result_cell)?,
                )?);
                for term in after.terms_mut() {
                    allocate_rule_term_keys(keys, term, RuleTermSide::Right)?;
                }
            }
        }
        RuleExtra::RewriteCell {
            cell,
            before,
            before_tree,
            after,
        } => {
            names.cell = Some(keys.key(
                ProvenanceRole::RuleLeftCellsField,
                TokenRange::for_tokens(cell)?,
            )?);
            allocate_rule_pattern_keys(keys, before, before_tree)?;
            let (_, term_keys) = before.keying();
            allocate_wildcard_keys(
                keys,
                before_tree,
                term_keys,
                ProvenanceRole::RuleLeftWildcard,
            )?;
            // A cell the result leaves out is read only and has no
            // result keys.
            if let Some(after) = after {
                names.result_cell = Some(keys.key(
                    ProvenanceRole::RuleRightCellsField,
                    TokenRange::for_tokens(cell)?,
                )?);
                allocate_rule_term_keys(keys, after, RuleTermSide::Right)?;
            }
        }
    }
    Ok(names)
}

/// The state-macro side of a rule term side.
const fn rule_side(side: RuleTermSide) -> RuleSide {
    match side {
        RuleTermSide::Left => RuleSide::Left,
        RuleTermSide::Right => RuleSide::Right,
    }
}

/// Keys a readable cell state on `side`: a term's nodes, a `k!`'s structure
/// and items, and a collection's instances, child fields, and rest, in the
/// order expansion visits them.
fn allocate_readable_state_keys(
    keys: &mut KeyAllocator,
    state: &mut crate::StateTerm,
    side: RuleTermSide,
) -> Result<(), SyntaxError> {
    let position = StatePosition::Rule(rule_side(side));
    match state {
        crate::StateTerm::Present(inner) => {
            allocate_readable_state_keys(keys, inner, side)?;
        }
        crate::StateTerm::Absent(_) => {}
        crate::StateTerm::Term(term) | crate::StateTerm::Group(term) => {
            allocate_readable_term_keys(keys, term, side)?;
        }
        crate::StateTerm::KSequence(sequence) => {
            sequence.allocate_keys(keys, position)?;
            for item in sequence.items_mut() {
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
            // Each child's state is keyed right after its name.
            let mut child = |keys: &mut KeyAllocator, state: &mut crate::StateTerm| {
                allocate_readable_state_keys(keys, state, side)
            };
            for item in list.front_mut() {
                item.allocate_keys(keys, position, &mut child)?;
            }
            list.allocate_rest_key(keys, position)?;
            for item in list.back_mut() {
                item.allocate_keys(keys, position, &mut child)?;
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
    state: &mut crate::StateTerm,
    side: RuleSide,
) -> Result<(), SyntaxError> {
    let crate::StateTerm::Instances(list) = state else {
        return Ok(());
    };
    let position = StatePosition::Rule(side);
    for item in list.front_mut() {
        item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
    }
    for item in list.back_mut() {
        item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
    }
    list.allocate_rest_key(keys, position)
}

/// Keys a readable term's nodes on `side` and, on the left, its wildcards.
fn allocate_readable_term_keys(
    keys: &mut KeyAllocator,
    term: &mut TermExpression,
    side: RuleTermSide,
) -> Result<(), SyntaxError> {
    allocate_rule_term_keys(keys, term, side)?;
    if matches!(side, RuleTermSide::Left) {
        let (_, tree, term_keys) = term.keying();
        allocate_wildcard_keys(keys, tree, term_keys, ProvenanceRole::RuleLeftWildcard)?;
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
            let result: Expr = input.call(crate::term::parse_term_expression)?;
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
                            narrowings.push(RuleNarrowing::new(binding, sort));
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
            let item = super::item::clause_item(
                &retained,
                &quote!(pub),
                &name,
                &sort_type,
                pattern.clone(),
                placeholder,
            )?;
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
                keys: ClauseKeys::default(),
                anchors: Vec::new(),
            };
            clause.check_existentials()?;
            clauses.push(clause);
        }
        if clauses.is_empty() {
            return Err(input
                .error("a readable rule block requires at least one clause")
                .into());
        }
        // Each clause is a sentence of its own, keyed once its block parses.
        for clause in &mut clauses {
            clause.keyed()?;
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
impl RuleClause {
    /// Records the clause's keyed nodes: those it keys on its item, its
    /// label, subject record, result and head result's terms, the
    /// computation items after the first, its extra cells, the List
    /// reading's instance structure, and its narrowings.
    ///
    /// The item's result term, a placeholder subject and the List
    /// reading's instance children are no nodes of the clause, and hold no
    /// keys: the clause keys its own result and the head record's terms.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        self.rule.keyed_nodes(nodes)?;
        nodes.push_tokens(self.keys.label.as_ref(), &self.rule.item.sig.ident)?;
        nodes.push(self.keys.pattern.as_ref(), self.layout.pattern);
        let result = self
            .head_result
            .as_ref()
            .map_or(Ok(self.layout.result), RuleHeadResult::range)?;
        nodes.push(self.keys.result.as_ref(), result);
        match &self.head_result {
            Some(RuleHeadResult::Replace(term)) => term.keyed_nodes(nodes)?,
            Some(RuleHeadResult::Splice { range, items }) => {
                nodes.push(self.keys.splice.as_ref(), *range);
                for item in items {
                    item.keyed_nodes(nodes)?;
                }
            }
            Some(RuleHeadResult::Erase(_)) | None => {}
        }
        for item in self.head.iter().flat_map(|head| &head.following) {
            item.pattern.keyed_nodes(nodes, &item.tree)?;
        }
        assert!(self.keys.extras.len() <= self.extras.len());
        for (extra, names) in self.extras.iter().zip(&self.keys.extras) {
            keyed_extra_nodes(nodes, extra, names)?;
        }
        if let Some(alternative) = &self.bracket_alternative {
            nodes.push_tokens(alternative.cell_key.as_ref(), &alternative.cell)?;
            alternative.before.keyed_nodes(nodes)?;
            if let Some(result_cell) = &alternative.result_cell {
                nodes.push_tokens(alternative.result_cell_key.as_ref(), result_cell)?;
            }
            if let Some(after) = &alternative.after {
                after.keyed_nodes(nodes)?;
            }
        }
        for narrowing in &self.narrowings {
            nodes.push_tokens(narrowing.sort_key.as_ref(), &narrowing.sort)?;
        }
        if let Some(computation) = &self.computation_cell {
            let names = &self.keys.computation_cell;
            nodes.push_tokens(names.cell.as_ref(), &computation.cell)?;
            if let Some(result_cell) = &computation.result_cell {
                nodes.push_tokens(names.result_cell.as_ref(), result_cell)?;
            }
        }
        Ok(())
    }
}

/// Records the keyed nodes of one extra cell: its names, with the keys the
/// clause gave them, and its terms and states.
#[cfg(test)]
fn keyed_extra_nodes(
    nodes: &mut crate::keyed_nodes::KeyedNodes,
    extra: &RuleExtra,
    names: &RuleExtraKeys,
) -> Result<(), SyntaxError> {
    match extra {
        RuleExtra::HaveMap { cell, entries } => {
            nodes.push_tokens(names.cell.as_ref(), cell)?;
            for entry in entries {
                entry.key.keyed_nodes(nodes)?;
                nodes.push_tokens(entry.value_key.as_ref(), &entry.value)?;
            }
        }
        RuleExtra::UpdateMap { cell, update, .. } => {
            nodes.push_tokens(names.result_cell.as_ref(), cell)?;
            for (key, argument) in update.argument_keys().into_iter().zip(update.arguments()) {
                nodes.push_tokens(key, argument)?;
            }
            update.term().keyed_nodes(nodes)?;
        }
        RuleExtra::RewriteState {
            cell,
            before,
            result_cell,
            after,
        } => {
            nodes.push_tokens(names.cell.as_ref(), cell)?;
            before.keyed_nodes(nodes)?;
            if let Some(result_cell) = result_cell {
                nodes.push_tokens(names.result_cell.as_ref(), result_cell)?;
            }
            if let Some(after) = after {
                after.keyed_nodes(nodes)?;
            }
        }
        RuleExtra::RewriteList {
            cell,
            before,
            result_cell,
            after,
        } => {
            nodes.push_tokens(names.cell.as_ref(), cell)?;
            for item in before.patterns() {
                item.pattern.keyed_nodes(nodes, &item.tree)?;
            }
            if let Some(result_cell) = result_cell {
                nodes.push_tokens(names.result_cell.as_ref(), result_cell)?;
            }
            for term in after.iter().flat_map(|after| after.terms()) {
                term.keyed_nodes(nodes)?;
            }
        }
        RuleExtra::RewriteCell {
            cell,
            before,
            before_tree,
            after,
        } => {
            nodes.push_tokens(names.cell.as_ref(), cell)?;
            before.keyed_nodes(nodes, before_tree)?;
            nodes.push_tokens(names.result_cell.as_ref(), cell)?;
            if let Some(after) = after {
                after.keyed_nodes(nodes)?;
            }
        }
    }
    Ok(())
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
