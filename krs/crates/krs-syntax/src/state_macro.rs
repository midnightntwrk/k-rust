use std::cell::RefCell;
use std::collections::BTreeSet;

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::quote;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Ident, Path, Token, parenthesized};

use crate::parse::{KeyAllocator, KrsSyntax, structured_with};
use crate::path::{path_text, plain_path_last};
use crate::{
    ProvenanceAnchor, ProvenanceRole, RuleRole, RuleSide, SyntaxError, SyntaxErrorKind,
    TermExpression, TermTree, TokenRange,
};
use krs_ir::ProvenanceKey;

/// Where a state macro stands in its sentence, which decides the roles of its
/// nodes: alone, under the standalone `cells_*`, `k_sequence_*` and `map_*`
/// roles, or on one side of a rule, under that side's roles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StatePosition {
    /// The state macro is its own sentence.
    Standalone,
    /// The state macro is one side's cells, or a state inside them.
    Rule(RuleSide),
}

impl StatePosition {
    /// The role of a node in `slot` at this position.
    pub(crate) const fn role(self, slot: RuleRole) -> ProvenanceRole {
        match self {
            Self::Standalone => match slot {
                RuleRole::CellsPayload => ProvenanceRole::CellsPayload,
                RuleRole::CellsField => ProvenanceRole::CellsField,
                RuleRole::CellsWrapper => ProvenanceRole::CellsWrapper,
                RuleRole::CellsRemainder => ProvenanceRole::CellsRemainder,
                RuleRole::KSequencePayload => ProvenanceRole::KSequencePayload,
                RuleRole::KSequenceItem => ProvenanceRole::KSequenceItem,
                RuleRole::KSequenceTail => ProvenanceRole::KSequenceTail,
                RuleRole::MapPayload => ProvenanceRole::MapPayload,
                RuleRole::MapKey => ProvenanceRole::MapKey,
                RuleRole::MapValue => ProvenanceRole::MapValue,
                RuleRole::MapRemainder => ProvenanceRole::MapRemainder,
                RuleRole::MapUpdateBase => ProvenanceRole::MapUpdateBase,
                RuleRole::CellsInstance => ProvenanceRole::CellsInstance,
                RuleRole::CellsInstanceField => ProvenanceRole::CellsInstanceField,
                RuleRole::CellsInstancesRest => ProvenanceRole::CellsInstancesRest,
            },
            Self::Rule(side) => slot.on_side(side),
        }
    }
}

/// Hands out the next key of `slot`'s role at `position` to the node at
/// `range`.
fn key_at(
    keys: &mut KeyAllocator,
    position: StatePosition,
    slot: RuleRole,
    range: TokenRange,
) -> Result<ProvenanceKey, SyntaxError> {
    keys.key(position.role(slot), range)
}

/// Where a shell's payload key is anchored: at the payload, or, when the
/// payload is empty, at the invocation that delimits it, since the empty
/// shell's text is its invocation. An empty payload read without its
/// invocation has nowhere to anchor.
fn payload_range(
    tokens: &TokenStream,
    invocation: Option<TokenRange>,
) -> Result<Option<TokenRange>, SyntaxError> {
    if tokens.is_empty() {
        Ok(invocation)
    } else {
        TokenRange::for_tokens(tokens).map(Some)
    }
}

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
    /// Anonymous remainder (`..`): a pattern's unnamed rest, or, at a
    /// `cells!` result's `KCell(..)`, that rest kept.
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

    /// Returns the authored range of a non-exact remainder.
    #[must_use]
    pub fn range(&self) -> Option<TokenRange> {
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
    /// The delimited text that holds the payload (the `k::k![..]`
    /// invocation, `KCell(..)`'s parentheses, a readable `[..]`), when the
    /// parser of an enclosing form read it.
    invocation: Option<TokenRange>,
    payload_key: Option<ProvenanceKey>,
    tail_key: Option<ProvenanceKey>,
    /// The anchors of the sequence's standalone keying.
    anchors: Vec<ProvenanceAnchor>,
    /// The refusal of an item written after the tail of a `KCell(..)` entry's sequence, whose
    /// items are kept in order before the tail ([`Self::misplaced_tail`]).
    misplaced_tail: Option<SyntaxError>,
}

impl KSequence {
    /// A readable `[items.., ..]` sequence (KF-023): `tokens` is the bracket
    /// payload and `tail` is exact or anonymous.
    ///
    /// # Errors
    ///
    /// Returns an endpoint or ordinal-overflow error of its standalone keying.
    pub(crate) fn readable(
        brackets: &proc_macro2::Group,
        items: Vec<TermExpression>,
        tail: StateMacroRemainder,
    ) -> Result<Self, SyntaxError> {
        Self::new(brackets.stream(), items, tail, KSequenceNotation::Comma)
            .invoked_at(Some(TokenRange::for_tokens(brackets)?))
            .keyed_standalone()
    }

    const fn new(
        tokens: TokenStream,
        items: Vec<TermExpression>,
        tail: StateMacroRemainder,
        notation: KSequenceNotation,
    ) -> Self {
        Self {
            tokens,
            items,
            tail,
            notation,
            invocation: None,
            payload_key: None,
            tail_key: None,
            anchors: Vec::new(),
            misplaced_tail: None,
        }
    }

    /// Records the delimited text that holds the payload, where the empty
    /// sequence is anchored.
    const fn invoked_at(mut self, invocation: Option<TokenRange>) -> Self {
        self.invocation = invocation;
        self
    }

    /// Records the refusal of the items written after the tail ([`Self::misplaced_tail`]).
    fn misplacing(mut self, refusal: SyntaxError) -> Self {
        self.misplaced_tail = Some(refusal);
        self
    }

    /// Ordered K items before the tail.
    #[must_use]
    pub fn items(&self) -> &[TermExpression] {
        &self.items
    }

    /// Ordered K items before the tail, for a pass that keys them.
    pub(crate) fn items_mut(&mut self) -> &mut [TermExpression] {
        &mut self.items
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

    /// The refusal of an item written after the tail of a `KCell(..)` entry's sequence,
    /// `KCell(.., x)` or `KCell(x, .., y)`, `None` where every item precedes the tail.
    ///
    /// The computation is read from its front, where the next step is, so its rest ends it
    /// (E1). That is the computation cell's own rule: on a cell of another kind the wrapper
    /// `KCell(..)` is the mistake, whatever its payload's order, and the cell's kind is the
    /// declaration's, which this parser does not know. So the parser keeps such an entry, its
    /// items in order before the tail, for the caller that judges the entry against its cell
    /// first, which asks this once the entries are admitted, or at once where it judges none
    /// ([`crate::StateRuleItem::misplaced_tail`]). The item is a part of the entry, so its fault
    /// waits for the whole ([`PartFaults`]); it binds nothing the sequence does not still read,
    /// so it waits on either side.
    #[must_use]
    pub const fn misplaced_tail(&self) -> Option<&SyntaxError> {
        self.misplaced_tail.as_ref()
    }

    /// Whether the sequence denotes exact `.K` (explicitly or as `k![]`).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty() && matches!(self.tail, StateMacroRemainder::Exact)
    }

    /// The key of the payload, anchored at the payload, or at the
    /// invocation when the payload is empty (`k::k![]`); absent only for an
    /// empty sequence parsed without its invocation. An item's key is the
    /// payload key of its term ([`crate::TermKeys::payload`]).
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the tail: the remainder, or the authored `.K`.
    #[must_use]
    pub const fn tail_key(&self) -> Option<&ProvenanceKey> {
        self.tail_key.as_ref()
    }

    /// Returns payload, item, and tail anchors of the sequence's standalone
    /// keying.
    ///
    /// # Errors
    ///
    /// None: the sequence was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets the keys of the sequence and of its items, and the anchors
    /// of its standalone keying, before an enclosing sentence's pass keys
    /// them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.tail_key = None;
        self.anchors.clear();
        for item in &mut self.items {
            item.clear_keys();
        }
    }

    /// Keys the payload, each item (as its term's payload), then the tail,
    /// under the roles of `position`. The items' own nodes are the enclosing
    /// sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = payload_range(&self.tokens, self.invocation)? {
            self.payload_key = Some(key_at(keys, position, RuleRole::KSequencePayload, range)?);
        }
        for item in &mut self.items {
            item.allocate_payload_key(keys, position.role(RuleRole::KSequenceItem))?;
        }
        let tail = match self.tail.range() {
            Some(range) => Some(range),
            None if self.notation == KSequenceNotation::DotK => {
                Some(TokenRange::for_tokens(&self.tokens)?)
            }
            None => None,
        };
        if let Some(range) = tail {
            self.tail_key = Some(key_at(keys, position, RuleRole::KSequenceTail, range)?);
        }
        Ok(())
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
#[expect(
    clippy::large_enum_variant,
    reason = "Span-preserving term nodes are the public parser contract."
)]
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

#[derive(Clone, Debug, Default)]
pub(crate) struct MapPatternBindings {
    pub(crate) terms: Vec<Ident>,
    pub(crate) frame: Option<Ident>,
}

impl MapPatternBindings {
    fn from_items(items: &[MapItem], remainder: &StateMacroRemainder) -> Self {
        // Only the left image binds (KF-011).
        let terms = items
            .iter()
            .flat_map(|item| [item.key(), item.value()])
            .flat_map(|term| crate::term::pattern_tree_binders(term.tree(), false))
            .collect();
        let frame = match remainder {
            StateMacroRemainder::Bind { binding, .. } => Some(binding.clone()),
            _ => None,
        };
        Self { terms, frame }
    }
}

/// Parsed `map!` payload.
#[derive(Clone, Debug)]
pub struct MapExpression {
    tokens: TokenStream,
    body: MapBody,
    pattern_bindings: Option<MapPatternBindings>,
    /// The delimited text that holds the payload (`k::map![..]`), when the
    /// parser of an enclosing form read it.
    invocation: Option<TokenRange>,
    /// The macro's path as written (`map`, `k::map`), when the map is a
    /// cell's own content, an island the enclosing macro consumes.
    island: Option<Path>,
    payload_key: Option<ProvenanceKey>,
    remainder_key: Option<ProvenanceKey>,
    /// The anchors of the map's standalone keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl MapExpression {
    /// Returns the tokens the expression was parsed from.
    #[must_use]
    pub const fn tokens(&self) -> &TokenStream {
        &self.tokens
    }

    fn empty(tokens: TokenStream, explicit_dot: bool, context: StateMacroContext) -> Self {
        Self::new(
            tokens,
            MapBody::Empty { explicit_dot },
            (context == StateMacroContext::Pattern).then(MapPatternBindings::default),
        )
    }

    const fn new(
        tokens: TokenStream,
        body: MapBody,
        pattern_bindings: Option<MapPatternBindings>,
    ) -> Self {
        Self {
            tokens,
            body,
            pattern_bindings,
            invocation: None,
            island: None,
            payload_key: None,
            remainder_key: None,
            anchors: Vec::new(),
        }
    }

    /// Records the delimited text that holds the payload, where the empty
    /// map is anchored.
    const fn invoked_at(mut self, invocation: Option<TokenRange>) -> Self {
        self.invocation = invocation;
        self
    }

    /// Records the path of the macro that writes a cell's own map.
    pub(crate) fn island_of(mut self, path: Option<Path>) -> Self {
        self.island = path;
        self
    }

    /// The path of the macro (`map`, `k::map`) that writes the map as a
    /// cell's own content, which the enclosing macro consumes before rustc
    /// sees it; `None` for a map no cell's macro wrote.
    #[must_use]
    pub const fn island_path(&self) -> Option<&Path> {
        self.island.as_ref()
    }

    fn items(
        tokens: TokenStream,
        items: Vec<MapItem>,
        remainder: StateMacroRemainder,
        context: StateMacroContext,
    ) -> Self {
        let pattern_bindings = (context == StateMacroContext::Pattern)
            .then(|| MapPatternBindings::from_items(&items, &remainder));
        Self::new(
            tokens,
            MapBody::Items { items, remainder },
            pattern_bindings,
        )
    }

    pub(crate) const fn pattern_bindings(&self) -> Option<&MapPatternBindings> {
        self.pattern_bindings.as_ref()
    }

    /// Returns the classified map operation.
    #[must_use]
    pub const fn body(&self) -> &MapBody {
        &self.body
    }

    /// The key of the payload, anchored at the payload, or at the
    /// invocation when the payload is empty (`k::map![]`); absent only for
    /// an empty map parsed without its invocation. An item's key and value,
    /// and an update's base, key and value, are keyed as their terms'
    /// payloads ([`crate::TermKeys::payload`]).
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the items' remainder.
    #[must_use]
    pub const fn remainder_key(&self) -> Option<&ProvenanceKey> {
        self.remainder_key.as_ref()
    }

    /// Returns payload and structural map anchors of the map's standalone
    /// keying.
    ///
    /// # Errors
    ///
    /// None: the map was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The map's terms in key order: each item's key and value, or an
    /// update's base, key and value.
    pub(crate) fn terms_mut(&mut self) -> Vec<&mut TermExpression> {
        match &mut self.body {
            MapBody::Empty { .. } => Vec::new(),
            MapBody::Items { items, .. } => items
                .iter_mut()
                .flat_map(|item| [&mut item.key, &mut item.value])
                .collect(),
            MapBody::Update { base, key, value } => vec![base, key, value],
        }
    }

    /// Forgets the keys of the map and of its terms, and the anchors of its
    /// standalone keying, before an enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.remainder_key = None;
        self.anchors.clear();
        for term in self.terms_mut() {
            term.clear_keys();
        }
    }

    /// Keys the payload, then each item's key and value and the remainder, or
    /// an update's base, key and value, under the roles of `position`. The
    /// terms' own nodes are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = payload_range(&self.tokens, self.invocation)? {
            self.payload_key = Some(key_at(keys, position, RuleRole::MapPayload, range)?);
        }
        let key_role = position.role(RuleRole::MapKey);
        let value_role = position.role(RuleRole::MapValue);
        match &mut self.body {
            MapBody::Empty { .. } => {}
            MapBody::Items { items, remainder } => {
                for item in items {
                    item.key.allocate_payload_key(keys, key_role)?;
                    item.value.allocate_payload_key(keys, value_role)?;
                }
                if let Some(range) = remainder.range() {
                    self.remainder_key =
                        Some(key_at(keys, position, RuleRole::MapRemainder, range)?);
                }
            }
            MapBody::Update { base, key, value } => {
                base.allocate_payload_key(keys, position.role(RuleRole::MapUpdateBase))?;
                key.allocate_payload_key(keys, key_role)?;
                value.allocate_payload_key(keys, value_role)?;
            }
        }
        Ok(())
    }
}

/// Term families admitted as fixed leaf-cell contents.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Avoid hiding parser AST ownership behind allocation."
)]
pub enum StateTerm {
    /// Ordinary named term.
    Term(TermExpression),
    /// Compiler-parsed K sequence.
    KSequence(KSequence),
    /// Compiler-parsed map operation.
    Map(MapExpression),
    /// A whole nested (group) cell written without a wrapper: a group
    /// binder, `_`, or a complete `k::fragment!` term (KF-016).
    Group(TermExpression),
    /// `Some(..)` of an optional (`?`) cell: the present cell's state; a
    /// leaf's `Cell(..)` wrapper is the entry's wrapper (KF-023, R7).
    Present(Box<StateTerm>),
    /// `None` of an optional (`?`) cell: the cell is absent (KF-023).
    Absent(TokenRange),
    /// The instances of a collection (`*`) cell (KF-023, R8).
    Instances(InstanceList),
    /// A group record at a configuration position some child of which is an entry no term
    /// spells, a map (ruling R4, TRI-D2): the record of the group's children, each that child
    /// cell's entry.
    Record(Box<GroupRecord>),
}

impl StateTerm {
    /// The state with its instances' heads left out: a reading whose children are another
    /// reading's terms (a List collection's bracket alternative), which that reading's record
    /// names ([`InstanceItem::without_head`]).
    #[must_use]
    pub(crate) fn without_instance_heads(self) -> Self {
        match self {
            Self::Instances(mut list) => {
                list.front = list
                    .front
                    .into_iter()
                    .map(InstanceItem::without_head)
                    .collect();
                list.back = list
                    .back
                    .into_iter()
                    .map(InstanceItem::without_head)
                    .collect();
                Self::Instances(list)
            }
            other => other,
        }
    }

    /// The state inside any `Some(..)` wrappers.
    #[must_use]
    pub fn unwrap_present(&self) -> &Self {
        match self {
            Self::Present(inner) => inner.unwrap_present(),
            other => other,
        }
    }

    /// Every term of the state in traversal order: a term or group, the
    /// items of `k!`, the keys and values of `map!`, and the terms nested in
    /// `Some(..)` and collection instances.
    #[must_use]
    pub fn terms(&self) -> Vec<&TermExpression> {
        match self {
            Self::Term(term) | Self::Group(term) => vec![term],
            Self::KSequence(sequence) => sequence.items().iter().collect(),
            Self::Map(map) => match map.body() {
                MapBody::Empty { .. } => Vec::new(),
                MapBody::Items { items, .. } => items
                    .iter()
                    .flat_map(|item| [item.key(), item.value()])
                    .collect(),
                MapBody::Update { base, key, value } => vec![base, key, value],
            },
            Self::Present(_) | Self::Absent(_) | Self::Instances(_) | Self::Record(_) => self
                .nested_states()
                .into_iter()
                .flat_map(Self::terms)
                .collect(),
        }
    }

    /// Every term of the state, mutably, in [`Self::terms`] order.
    pub(crate) fn terms_mut(&mut self) -> Vec<&mut TermExpression> {
        match self {
            Self::Term(term) | Self::Group(term) => vec![term],
            Self::KSequence(sequence) => sequence.items.iter_mut().collect(),
            Self::Map(map) => map.terms_mut(),
            Self::Present(inner) => inner.terms_mut(),
            Self::Absent(_) => Vec::new(),
            Self::Instances(list) => list
                .nested_states_mut()
                .into_iter()
                .flat_map(Self::terms_mut)
                .collect(),
            Self::Record(record) => record.states_mut().flat_map(Self::terms_mut).collect(),
        }
    }

    /// Forgets the keys of the state and of everything inside it, before an
    /// enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        match self {
            Self::Term(term) | Self::Group(term) => term.clear_keys(),
            Self::KSequence(sequence) => sequence.clear_keys(),
            Self::Map(map) => map.clear_keys(),
            Self::Present(inner) => inner.clear_keys(),
            Self::Absent(_) => {}
            Self::Instances(list) => list.clear_keys(),
            Self::Record(record) => record.clear_keys(),
        }
    }

    /// The paths of the `map!` islands that write this state's maps, its
    /// nested states' included, in source order ([`MapExpression::island_path`]).
    #[must_use]
    pub fn map_islands(&self) -> Vec<&Path> {
        match self {
            Self::Map(map) => map.island_path().into_iter().collect(),
            Self::Present(_) | Self::Instances(_) | Self::Record(_) => self
                .nested_states()
                .into_iter()
                .flat_map(Self::map_islands)
                .collect(),
            Self::Term(_) | Self::KSequence(_) | Self::Group(_) | Self::Absent(_) => Vec::new(),
        }
    }

    /// Every directly nested state: the inside of `Some(..)` and the
    /// children of collection instances, in source order.
    #[must_use]
    pub fn nested_states(&self) -> Vec<&Self> {
        match self {
            Self::Present(inner) => vec![inner],
            Self::Instances(list) => list.instances().flat_map(InstanceItem::states).collect(),
            Self::Record(record) => record.states().collect(),
            Self::Term(_)
            | Self::KSequence(_)
            | Self::Map(_)
            | Self::Group(_)
            | Self::Absent(_) => Vec::new(),
        }
    }
}

/// A group record at a configuration position whose children are entries (ruling R4, TRI-D2):
/// `k::fragment![Group { child: k::map![k -> v, ..], .. }]`, or readable
/// `Group { child: { k -> v, .. }, .. }`. Each child is that child cell's entry, read as an
/// instance's child is, and the head names the struct the record is of.
#[derive(Clone, Debug)]
pub struct GroupRecord {
    range: TokenRange,
    head: Box<StateTerm>,
    fields: Vec<InstanceField>,
    open: Option<TokenRange>,
}

impl GroupRecord {
    /// The record of `owner`'s children `fields`, ending in `..` when `open`, written inside
    /// `k::fragment![..]` when `fragment`.
    pub(crate) fn new(
        range: TokenRange,
        owner: &Path,
        fragment: bool,
        fields: Vec<InstanceField>,
        open: Option<TokenRange>,
    ) -> Result<Self, SyntaxError> {
        Ok(Self {
            range,
            head: Box::new(record_head(owner, fragment)?),
            fields,
            open,
        })
    }

    /// The complete record range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// The record's head, the item-less pattern `P { .. }` its path reads as ([`record_head`]).
    #[must_use]
    pub fn head(&self) -> &TermExpression {
        let StateTerm::Term(head) = &*self.head else {
            unreachable!("a record's head is a term")
        };
        head
    }

    /// The named children in source order.
    #[must_use]
    pub fn fields(&self) -> &[InstanceField] {
        &self.fields
    }

    /// Whether the record ends in `..`.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open.is_some()
    }

    fn states(&self) -> impl Iterator<Item = &StateTerm> {
        std::iter::once(&*self.head).chain(self.fields.iter().map(InstanceField::value))
    }

    fn states_mut(&mut self) -> impl Iterator<Item = &mut StateTerm> {
        std::iter::once(&mut *self.head).chain(self.fields.iter_mut().map(|field| &mut field.value))
    }

    fn clear_keys(&mut self) {
        self.head.clear_keys();
        for field in &mut self.fields {
            field.name_key = None;
            field.value.clear_keys();
        }
    }

    /// Keys the record's head with `child`, then each child's name under the roles of
    /// `position`, each name followed by what `child` keys in that child's state. The record's
    /// node is its head's, the path the record names its struct by.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
        child: &mut dyn FnMut(&mut KeyAllocator, &mut StateTerm) -> Result<(), SyntaxError>,
    ) -> Result<(), SyntaxError> {
        child(keys, &mut self.head)?;
        // A record's children are named as a record term's fields are: a `cells!` fragment's
        // record is that term's, read as its children's entries.
        let role = match position {
            StatePosition::Rule(crate::RuleSide::Right) => ProvenanceRole::RuleRightRecordFieldName,
            _ => ProvenanceRole::RuleLeftRecordFieldName,
        };
        for field in &mut self.fields {
            let range = TokenRange::for_tokens(&field.name)?;
            field.name_key = Some(keys.key(role, range)?);
            child(keys, &mut field.value)?;
        }
        Ok(())
    }
}

/// The head of a record of `owner`'s children (TRI-D2): the item-less pattern `owner { .. }`,
/// inside `k::fragment![..]` when the record is written so, on the path's own tokens. It is read
/// as the term its path names, which the collector resolves as every record path, so it says
/// which struct the record is of and nothing else: it names no field, so it matches and writes
/// nothing, and it stands only in a record's `head`, never where a rule's terms are.
pub(crate) fn record_head(owner: &Path, fragment: bool) -> Result<StateTerm, SyntaxError> {
    let span = owner.span();
    let mut dots = TokenStream::new();
    for spacing in [proc_macro2::Spacing::Joint, proc_macro2::Spacing::Alone] {
        let mut dot = proc_macro2::Punct::new('.', spacing);
        dot.set_span(span);
        dots.extend([TokenTree::Punct(dot)]);
    }
    let mut body = proc_macro2::Group::new(Delimiter::Brace, dots);
    body.set_span(span);
    let mut record = quote::quote!(#owner);
    record.extend([TokenTree::Group(body)]);
    let tokens = if fragment {
        let mut invocation = proc_macro2::Group::new(Delimiter::Bracket, record);
        invocation.set_span(span);
        let mut tokens = quote::quote_spanned!(span=> k::fragment!);
        tokens.extend([TokenTree::Group(invocation)]);
        tokens
    } else {
        record
    };
    Ok(StateTerm::Term(TermExpression::parse_pattern_tokens(
        tokens,
    )?))
}

/// The delimiter of a collection entry (KF-023, R8).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstanceListDelimiter {
    /// `{ .. }`: some instances of a Set or Map collection.
    Brace,
    /// `[ .. ]`: the ends of a List collection.
    Bracket,
}

/// The rest of one collection instance record.
#[derive(Clone, Debug)]
pub enum InstanceRest {
    /// No rest: the record names every child.
    Exact,
    /// `..`: unconstrained children (pattern) or template defaults (result).
    Open(TokenRange),
    /// `..label` in a result: the matched instance `label`, updated.
    Update {
        /// The pattern instance label.
        label: Ident,
        /// Complete `..label` range.
        range: TokenRange,
    },
}

/// One named child of a collection instance record.
#[derive(Clone, Debug)]
pub struct InstanceField {
    name: Ident,
    value: StateTerm,
    name_key: Option<ProvenanceKey>,
}

impl InstanceField {
    pub(crate) const fn new(name: Ident, value: StateTerm) -> Self {
        Self {
            name,
            value,
            name_key: None,
        }
    }

    /// The key of the child's field name, given by the rule side that
    /// anchors the collection.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The child's Rust field name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// The child's state: a term, a whole group, `k!`, or `map!`.
    #[must_use]
    pub const fn value(&self) -> &StateTerm {
        &self.value
    }
}

/// The reason an instance child `child` written `Some(..)` (`present`) or `None` is not lowered:
/// a `?` cell's presence or absence inside one instance ([`INSTANCE_CHILD_MULTIPLICITY`]), which
/// the collector says once the entries are admitted
/// ([`crate::cell_entries::instance_child_presence`]).
#[must_use]
pub fn instance_child_multiplicity_reason(child: &str, present: bool) -> String {
    let written = presence_written(present);
    format!("the instance child `{child}` holds {written}: {INSTANCE_CHILD_MULTIPLICITY}")
}

/// The reason a `?` cell `cell`'s `Some(..)` (`present`) or `None`, a field of a record the
/// instance child `child` writes, at any depth of records, is not lowered: a presence inside one
/// instance ([`INSTANCE_CHILD_MULTIPLICITY`]).
#[must_use]
pub fn instance_record_multiplicity_reason(cell: &str, child: &str, present: bool) -> String {
    let written = presence_written(present);
    format!(
        "the cell `{cell}`, inside the instance child `{child}`, holds {written}: {INSTANCE_CHILD_MULTIPLICITY}"
    )
}

/// What a `?` cell's `Some(..)` (`present`) or `None` writes, as a refusal names it.
const fn presence_written(present: bool) -> &'static str {
    if present {
        "`Some(..)`, a `?` cell's presence"
    } else {
        "`None`, a `?` cell's absence"
    }
}

/// An instance child's tokens that write a `?` cell's state, `Some(content)` or `None`, read by
/// their spelling as a cell entry's are.
pub(crate) enum PresenceTokens {
    /// `Some(content)`: the content's tokens.
    Present(TokenStream),
    /// `None`: its range.
    Absent(TokenRange),
}

impl PresenceTokens {
    /// The state `tokens` write, if they are exactly `Some(..)` or `None`.
    pub(crate) fn of(tokens: &TokenStream) -> Result<Option<Self>, SyntaxError> {
        let trees = tokens.clone().into_iter().collect::<Vec<_>>();
        Ok(match Self::spelled(&trees) {
            Some((_, Some(content))) => Some(Self::Present(content)),
            Some((_, None)) => Some(Self::Absent(TokenRange::for_tokens(tokens)?)),
            None => None,
        })
    }

    /// The one reading of a presence's spelling: where `trees` are exactly `Some(..)` or `None`,
    /// the head (`Some` or `None`), and the content of `Some(..)`.
    pub(crate) fn spelled(trees: &[TokenTree]) -> Option<(&Ident, Option<TokenStream>)> {
        match trees {
            [TokenTree::Ident(ident)] if ident == "None" => Some((ident, None)),
            [TokenTree::Ident(ident), TokenTree::Group(group)]
                if ident == "Some" && group.delimiter() == proc_macro2::Delimiter::Parenthesis =>
            {
                Some((ident, Some(group.stream())))
            }
            _ => None,
        }
    }
}

/// What an instance record meets at a child that is a `?` cell or a collection of its own: what
/// the child would mean is whether, or which, cells that one instance holds, and no lowering
/// writes that yet, a stated limitation. The collector says it where `Some(..)` or `None` stand
/// as an instance child or inside a record the child writes, at any depth, once the entries are
/// admitted ([`crate::cell_entries::instance_child_presence`]); and the compiler where the child's
/// declaration shows it.
pub const INSTANCE_CHILD_MULTIPLICITY: &str =
    "an instance record does not name a `?` or `*` child yet";

/// One instance record of a collection entry: `label @ Decl { .. }` or
/// `k::fragment![Decl { .. }]` (KF-023), or an item that is one name or `_`,
/// the whole instance that record names ([`InstanceItem::whole`]).
#[derive(Clone, Debug)]
pub struct InstanceItem {
    range: TokenRange,
    label: Option<Ident>,
    owner: Option<Path>,
    /// The record's path read as the item-less pattern `P { .. }` ([`record_head`]); `None`
    /// for a whole instance written as a name or `_`.
    head: Option<Box<StateTerm>>,
    fields: Vec<InstanceField>,
    rest: InstanceRest,
    fragment: bool,
    key: Option<ProvenanceKey>,
}

impl InstanceItem {
    /// Keys the instance record, then each child's name under the roles of
    /// `position`, each followed by what `child` keys in that child's state.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
        child: &mut dyn FnMut(&mut KeyAllocator, &mut StateTerm) -> Result<(), SyntaxError>,
    ) -> Result<(), SyntaxError> {
        self.key = Some(key_at(keys, position, RuleRole::CellsInstance, self.range)?);
        if let Some(head) = &mut self.head {
            child(keys, head)?;
        }
        for field in &mut self.fields {
            let range = TokenRange::for_tokens(&field.name)?;
            field.name_key = Some(key_at(keys, position, RuleRole::CellsInstanceField, range)?);
            child(keys, &mut field.value)?;
        }
        Ok(())
    }

    pub(crate) fn new(
        range: TokenRange,
        label: Option<Ident>,
        owner: Path,
        fields: Vec<InstanceField>,
        rest: InstanceRest,
    ) -> Result<Self, SyntaxError> {
        Ok(Self {
            range,
            label,
            head: Some(Box::new(record_head(&owner, false)?)),
            owner: Some(owner),
            fields,
            rest,
            fragment: false,
            key: None,
        })
    }

    /// The instance without its head: a reading whose children are another reading's terms
    /// (a List collection's bracket alternative), whose record the other reading names.
    #[must_use]
    pub(crate) fn without_head(mut self) -> Self {
        self.head = None;
        self
    }

    /// The record's head, the item-less pattern `P { .. }` its path reads as: which struct the
    /// record names, checked against the collection's instance cell. `None` for a whole
    /// instance written as a name or `_`.
    #[must_use]
    pub fn head(&self) -> Option<&TermExpression> {
        match self.head.as_deref() {
            Some(StateTerm::Term(head)) => Some(head),
            _ => None,
        }
    }

    /// The head's state and the children's states, in source order: what the enclosing
    /// sentence keys and walks.
    fn states(&self) -> impl Iterator<Item = &StateTerm> {
        self.head
            .as_deref()
            .into_iter()
            .chain(self.fields.iter().map(InstanceField::value))
    }

    fn states_mut(&mut self) -> impl Iterator<Item = &mut StateTerm> {
        self.head
            .as_deref_mut()
            .into_iter()
            .chain(self.fields.iter_mut().map(|field| &mut field.value))
    }

    /// The instance an instance-list item that is exactly one name `x` or `_` stands for, read
    /// in `context`; `None` for any other item. In a pattern it is the instance record
    /// `x @ Decl { .. }` (`Decl { .. }` for `_`): one whole instance, any child, labelled with
    /// the name, where `Decl` is the collection's declared instance group, which the collector
    /// knows, so the item names none. In a result it is the instance the pattern bound to `x`,
    /// kept as matched: the update `Decl { ..x }`, which writes no child. A keyword or literal
    /// (`true`, `0`) is no name, and is read as any other item is.
    pub(crate) fn whole(
        tokens: &TokenStream,
        context: StateMacroContext,
    ) -> Result<Option<Self>, SyntaxError> {
        let trees = tokens.clone().into_iter().collect::<Vec<_>>();
        let [TokenTree::Ident(name)] = trees.as_slice() else {
            return Ok(None);
        };
        let wildcard = name == "_";
        if !wildcard && syn::parse2::<Ident>(tokens.clone()).is_err() {
            return Ok(None);
        }
        let range = TokenRange::for_tokens(tokens)?;
        let (label, rest) = match context {
            StateMacroContext::Pattern => {
                if !wildcard {
                    crate::parse::validate_authored_binder(&name.to_string(), name.span())?;
                }
                ((!wildcard).then(|| name.clone()), InstanceRest::Open(range))
            }
            StateMacroContext::Expression => (
                None,
                InstanceRest::Update {
                    label: name.clone(),
                    range,
                },
            ),
        };
        Ok(Some(Self {
            range,
            label,
            owner: None,
            head: None,
            fields: Vec::new(),
            rest,
            fragment: false,
            key: None,
        }))
    }

    /// The key of the instance record, given by the rule side that anchors
    /// the collection.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The complete instance-record range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// The pattern label (`me @ ..`); a label is not a term binder.
    #[must_use]
    pub const fn label(&self) -> Option<&Ident> {
        self.label.as_ref()
    }

    /// The instance's `#[k::cell]` struct path, as the record writes it; `None` for an item
    /// that is one name or `_`, whose group is the collection's declared one
    /// ([`Self::whole`]).
    #[must_use]
    pub const fn owner(&self) -> Option<&Path> {
        self.owner.as_ref()
    }

    /// The named children in source order.
    #[must_use]
    pub fn fields(&self) -> &[InstanceField] {
        &self.fields
    }

    /// The record's rest.
    #[must_use]
    pub const fn rest(&self) -> &InstanceRest {
        &self.rest
    }

    /// Whether the record was written inside `k::fragment![..]`.
    #[must_use]
    pub const fn is_fragment(&self) -> bool {
        self.fragment
    }
}

/// A collection entry: instance records and an optional rest (KF-023, R8).
#[derive(Clone, Debug)]
pub struct InstanceList {
    delimiter: InstanceListDelimiter,
    front: Vec<InstanceItem>,
    rest: StateMacroRemainder,
    back: Vec<InstanceItem>,
    rest_key: Option<ProvenanceKey>,
}

impl InstanceList {
    pub(crate) const fn new(
        delimiter: InstanceListDelimiter,
        front: Vec<InstanceItem>,
        rest: StateMacroRemainder,
        back: Vec<InstanceItem>,
    ) -> Self {
        Self {
            delimiter,
            front,
            rest,
            back,
            rest_key: None,
        }
    }

    /// The key of the collection rest, given by the rule side that anchors
    /// the collection.
    #[must_use]
    pub const fn rest_key(&self) -> Option<&ProvenanceKey> {
        self.rest_key.as_ref()
    }

    /// Braces (Set, Map) or brackets (List).
    #[must_use]
    pub const fn delimiter(&self) -> InstanceListDelimiter {
        self.delimiter
    }

    /// The instances before the rest.
    #[must_use]
    pub fn front(&self) -> &[InstanceItem] {
        &self.front
    }

    /// The collection rest; [`StateMacroRemainder::Exact`] when absent.
    #[must_use]
    pub const fn rest(&self) -> &StateMacroRemainder {
        &self.rest
    }

    /// The instances after the rest of a bracketed list.
    #[must_use]
    pub fn back(&self) -> &[InstanceItem] {
        &self.back
    }

    /// Every instance, front then back.
    pub fn instances(&self) -> impl Iterator<Item = &InstanceItem> {
        self.front.iter().chain(&self.back)
    }

    /// Forgets the keys of the list and of its instances' children, before
    /// an enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.rest_key = None;
        for item in self.front.iter_mut().chain(&mut self.back) {
            item.key = None;
            if let Some(head) = &mut item.head {
                head.clear_keys();
            }
            for field in &mut item.fields {
                field.name_key = None;
                field.value.clear_keys();
            }
        }
    }

    /// Keys the front instances (each followed by its children's names), the
    /// rest, then the back instances, under the roles of `position`. The
    /// children's states are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        for item in &mut self.front {
            item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
        }
        self.allocate_rest_key(keys, position)?;
        for item in &mut self.back {
            item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
        }
        Ok(())
    }

    /// Keys the collection rest, if any, under the role of `position`.
    pub(crate) fn allocate_rest_key(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = self.rest.range() {
            self.rest_key = Some(key_at(keys, position, RuleRole::CellsInstancesRest, range)?);
        }
        Ok(())
    }

    /// The instances before the rest, for a pass that keys them.
    pub(crate) fn front_mut(&mut self) -> &mut [InstanceItem] {
        &mut self.front
    }

    /// The instances after the rest, for a pass that keys them.
    pub(crate) fn back_mut(&mut self) -> &mut [InstanceItem] {
        &mut self.back
    }

    /// Every instance's children's states, mutably, in [`Self::instances`]
    /// order.
    pub(crate) fn nested_states_mut(&mut self) -> Vec<&mut StateTerm> {
        self.front
            .iter_mut()
            .chain(&mut self.back)
            .flat_map(InstanceItem::states_mut)
            .collect()
    }
}

/// One selected fixed cell in a `cells!` payload: a leaf with its
/// `Cell(..)`/`KCell(..)` wrapper, or a whole nested cell without one.
#[derive(Clone, Debug)]
pub struct CellsEntry {
    name: Ident,
    owner: Option<Path>,
    wrapper: Option<ReadWrapper>,
    value: StateTerm,
    name_key: Option<ProvenanceKey>,
    wrapper_key: Option<ProvenanceKey>,
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

    /// Returns the `Cell`/`KCell` wrapper path, absent exactly for a whole
    /// nested-cell entry ([`StateTerm::Group`]), `None`, and a collection
    /// entry; for `Some(Cell(..))` it is the inner wrapper. It is the authored
    /// path, or a `Cell` the entry is read under while the refusal of a
    /// content written without its wrapper waits ([`Self::implied_wrapper`]).
    #[must_use]
    pub fn wrapper(&self) -> Option<&Path> {
        self.wrapper.as_ref().map(|wrapper| &wrapper.path)
    }

    /// Whether the wrapper is no authored path but the `Cell` a content written without its
    /// wrapper is read under while its refusal waits for the judgement of the entry
    /// ([`PartFaults`]): no reference names it.
    #[must_use]
    pub fn implied_wrapper(&self) -> bool {
        self.wrapper.as_ref().is_some_and(|wrapper| wrapper.implied)
    }

    /// Returns the compiler-parsed leaf contents.
    #[must_use]
    pub const fn value(&self) -> &StateTerm {
        &self.value
    }

    /// Returns the compiler-parsed leaf contents, for a pass that keys them.
    pub(crate) const fn value_mut(&mut self) -> &mut StateTerm {
        &mut self.value
    }

    /// The key of the field name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the `Cell`/`KCell` wrapper.
    #[must_use]
    pub const fn wrapper_key(&self) -> Option<&ProvenanceKey> {
        self.wrapper_key.as_ref()
    }
}

/// Parsed `cells!` pattern or expression payload.
#[derive(Clone, Debug)]
pub struct CellsExpression {
    tokens: TokenStream,
    context: StateMacroContext,
    entries: Vec<CellsEntry>,
    remainder: StateMacroRemainder,
    payload_key: Option<ProvenanceKey>,
    remainder_key: Option<ProvenanceKey>,
    /// The macro's delimiters, where the caller has them: the payload's range when it holds no
    /// token, a result that names no cell (`cells! {}`). Without them such a payload has no key,
    /// as an empty K sequence's has none without its invocation.
    invocation: Option<TokenRange>,
    /// The anchors of the cells' standalone keying.
    anchors: Vec<ProvenanceAnchor>,
    /// The refusal of the first entry part whose fault waits for the judgement of the entry
    /// ([`PartFaults`]): a record child that writes a `?` cell's presence, at any depth
    /// ([`RecordPresences`]), or a result instance record's child whose value the term reader
    /// refuses.
    carried: Option<SyntaxError>,
}

impl CellsExpression {
    /// The refusal of the first entry, in source order, that the parser keeps for the judgement
    /// of the entries against their cells: a part's fault, which waits for the whole it is in
    /// ([`PartFaults`]): a record child that writes a `?` cell's presence ([`RecordPresences`]),
    /// a result instance record's child the term reader refuses, or a `KCell(..)` sequence's
    /// item after its tail ([`KSequence::misplaced_tail`]); `None` where no entry does.
    #[must_use]
    pub fn misplaced_tail(&self) -> Option<&SyntaxError> {
        fn within(state: &StateTerm) -> Option<&SyntaxError> {
            match state {
                StateTerm::KSequence(sequence) => sequence.misplaced_tail(),
                other => other.nested_states().into_iter().find_map(within),
            }
        }
        self.carried
            .as_ref()
            .or_else(|| self.entries.iter().find_map(|entry| within(&entry.value)))
    }

    /// The payload, refused where an entry writes an item after its sequence's tail: for a
    /// caller that judges no entry's kind first.
    fn in_order(self) -> Result<Self, SyntaxError> {
        match self.misplaced_tail() {
            Some(refusal) => Err(refusal.clone()),
            None => Ok(self),
        }
    }

    /// The payload's tokens, as written.
    #[must_use]
    pub const fn tokens(&self) -> &TokenStream {
        &self.tokens
    }

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

    /// The paths of the `map!` islands that write the cells' maps, in source
    /// order ([`StateTerm::map_islands`]).
    #[must_use]
    pub fn map_islands(&self) -> Vec<&Path> {
        self.entries
            .iter()
            .flat_map(|entry| entry.value().map_islands())
            .collect()
    }

    /// Exact, anonymous, bound, or reused configuration frame.
    #[must_use]
    pub const fn remainder(&self) -> &StateMacroRemainder {
        &self.remainder
    }

    /// Selected cells in authored order, for a pass that keys them.
    pub(crate) fn entries_mut(&mut self) -> &mut [CellsEntry] {
        &mut self.entries
    }

    /// The key of the payload.
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the configuration remainder.
    #[must_use]
    pub const fn remainder_key(&self) -> Option<&ProvenanceKey> {
        self.remainder_key.as_ref()
    }

    /// Returns payload, field, wrapper, and remainder anchors of the cells'
    /// standalone keying.
    ///
    /// Nested `k!`/`map!` provenance is returned by each entry's [`StateTerm`].
    ///
    /// # Errors
    ///
    /// None: the cells were keyed when they were parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the cells as a sentence of their own. Their entries' states are
    /// not part of it: each `k!` or `map!` among them is keyed as its own.
    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets the keys of the cells and of every entry's state, and the
    /// anchors of its standalone keying, before an enclosing sentence's pass
    /// keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.remainder_key = None;
        self.anchors.clear();
        for entry in &mut self.entries {
            entry.name_key = None;
            entry.wrapper_key = None;
            entry.value.clear_keys();
        }
    }

    /// Keys the payload, each field with its wrapper, then the remainder,
    /// under the roles of `position`. A standalone wrapper is numbered as its
    /// field is; a rule side numbers its wrappers on their own. The entries'
    /// states are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = payload_range(&self.tokens, self.invocation)? {
            self.payload_key = Some(key_at(keys, position, RuleRole::CellsPayload, range)?);
        }
        for entry in &mut self.entries {
            let field = key_at(
                keys,
                position,
                RuleRole::CellsField,
                TokenRange::for_tokens(&entry.name)?,
            )?;
            if let Some(wrapper) = entry.wrapper() {
                let range = TokenRange::for_tokens(wrapper)?;
                let role = position.role(RuleRole::CellsWrapper);
                entry.wrapper_key = Some(match position {
                    StatePosition::Standalone => keys.paired(role, &field, range)?,
                    StatePosition::Rule(_) => keys.key(role, range)?,
                });
            }
            entry.name_key = Some(field);
        }
        if let Some(range) = self.remainder.range() {
            self.remainder_key = Some(key_at(keys, position, RuleRole::CellsRemainder, range)?);
        }
        Ok(())
    }
}

/// Parses a `k!` pattern payload.
///
/// # Errors
///
/// Rejects malformed separators, misplaced `.K`, duplicate tails, and
/// expression-style `..tail` at the responsible token.
pub fn parse_k_sequence_pattern(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Pattern, None)
}

/// Parses a `k!` expression payload.
///
/// # Errors
///
/// Rejects pattern-only tail bindings and malformed sequence syntax.
pub fn parse_k_sequence_expression(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Expression, None)
}

/// Parses a `map!` pattern payload.
///
/// # Errors
///
/// Rejects updates and expression-style remainders in pattern position.
pub fn parse_map_pattern(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Pattern, None)
}

/// Parses a `map!` expression payload, including functional updates.
///
/// # Errors
///
/// Rejects pattern-only remainder bindings and malformed items/updates.
pub fn parse_map_expression(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Expression, None)
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
    parse_cells(tokens, StateMacroContext::Pattern, true).and_then(CellsExpression::in_order)
}

/// Whether the `cells!` payload `tokens` names no cell: it is empty, or only the state's rest,
/// `..` or `label @ ..`, with or without a trailing comma.
pub(crate) fn names_no_cell(tokens: &TokenStream) -> bool {
    let trees = crate::parse::strip_trailing_comma(tokens.clone())
        .into_iter()
        .collect::<Vec<_>>();
    let rest = |trees: &[TokenTree]| {
        matches!(trees, [TokenTree::Punct(first), TokenTree::Punct(second)]
            if first.as_char() == '.' && second.as_char() == '.')
    };
    match trees.as_slice() {
        [] => true,
        [TokenTree::Ident(_), TokenTree::Punct(at), tail @ ..] if at.as_char() == '@' => rest(tail),
        all => rest(all),
    }
}

/// Parses a `cells!` pattern payload, keeping a `KCell(..)` entry that writes an item after its
/// sequence's tail for the caller that judges the entries' kinds first
/// ([`KSequence::misplaced_tail`]).
///
/// # Errors
///
/// As [`parse_cells_pattern`], but for such an item.
pub(crate) fn parse_cells_pattern_judged_later(
    tokens: TokenStream,
) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Pattern, true)
}

/// Parses a `cells!` claim's start state, which holds its collection
/// instances as written: their cells are read as any pattern is, not as keys
/// a rule's pattern looks a Set collection up by ([`parse_instance_list`]). A
/// `KCell(..)` entry that writes an item after its sequence's tail is kept for
/// the judgement of the entries, as [`parse_cells_pattern_judged_later`] keeps it.
///
/// # Errors
///
/// As [`parse_cells_pattern_judged_later`].
pub(crate) fn parse_cells_claim_pattern(
    tokens: TokenStream,
) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Pattern, false)
}

/// Parses a `cells!` expression payload.
///
/// # Errors
///
/// Rejects duplicate cells, malformed wrappers, and pattern-only frames.
pub fn parse_cells_expression(tokens: TokenStream) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Expression, false).and_then(CellsExpression::in_order)
}

/// Parses a `cells!` expression payload, keeping a `KCell(..)` entry that writes an item after
/// its sequence's tail, as [`parse_cells_pattern_judged_later`] does.
///
/// # Errors
///
/// As [`parse_cells_expression`], but for such an item. `invocation` is the macro's delimiters,
/// the range of a payload that holds no token.
pub(crate) fn parse_cells_expression_judged_later(
    tokens: TokenStream,
    invocation: Option<TokenRange>,
) -> Result<CellsExpression, SyntaxError> {
    parse_unkeyed_cells(tokens, StateMacroContext::Expression, false, invocation)
        .and_then(CellsExpression::keyed_standalone)
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

/// Parses a `k!` payload held by `invocation`, if an enclosing form read
/// it, and keys it as a sentence of its own.
pub(crate) fn parse_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
) -> Result<KSequence, SyntaxError> {
    parse_keyed_k_sequence(tokens, context, invocation, SequenceRoot::Term)
}

/// Parses an initializer's `k!` payload held by `invocation`, the cell's whole initial content,
/// and keys it as a sentence of its own.
pub(crate) fn parse_initializer_k_sequence(
    tokens: TokenStream,
    invocation: Option<TokenRange>,
) -> Result<KSequence, SyntaxError> {
    parse_keyed_k_sequence(
        tokens,
        StateMacroContext::Expression,
        invocation,
        SequenceRoot::Initializer,
    )
}

/// Parses a `KCell(..)` entry's K sequence, the whole content of its cell: a content root, where
/// a result's anonymous `..` is the subject's unnamed rest of the cell, kept (P6, D2), as it is
/// in a pattern. Whether the subject has such a rest is the entry's pairing.
fn parse_cell_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
) -> Result<KSequence, SyntaxError> {
    parse_keyed_k_sequence(tokens, context, invocation, SequenceRoot::Cell)
}

/// Where a remainder stands, which decides what an expression's remainder means.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SequenceRoot {
    /// Inside a term (a `k::k![..]` island), or a `map!`'s or a `cells!` payload's own remainder.
    Term,
    /// A `KCell(..)` entry's sequence, the whole content of its cell ([`parse_cell_k_sequence`]).
    Cell,
    /// An initializer's `k!`, the cell's whole initial content
    /// ([`parse_initializer_k_sequence`]).
    Initializer,
}

fn parse_keyed_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
    root: SequenceRoot,
) -> Result<KSequence, SyntaxError> {
    parse_unkeyed_k_sequence(tokens, context, root)
        .map(|sequence| sequence.invoked_at(invocation))
        .and_then(KSequence::keyed_standalone)
}

#[expect(
    clippy::too_many_lines,
    reason = "One closed sequence grammar keeps tail diagnostics local."
)]
fn parse_unkeyed_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
    root: SequenceRoot,
) -> Result<KSequence, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            if input.is_empty() {
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    StateMacroRemainder::Exact,
                    KSequenceNotation::Comma,
                ));
            }
            if starts_remainder(input) {
                let tail = parse_remainder_kept(input, context, "k", root)?;
                if !input.is_empty() {
                    let misplaced = state_error("k", MISPLACED_TAIL, input.span());
                    let Some((items, notation)) = parse_back_items(input, context, root, None)
                    else {
                        return Err(misplaced);
                    };
                    return Ok(KSequence::new(
                        original.clone(),
                        items,
                        tail,
                        notation.unwrap_or(KSequenceNotation::Comma),
                    )
                    .misplacing(misplaced));
                }
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    tail,
                    KSequenceNotation::Comma,
                ));
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
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    StateMacroRemainder::Exact,
                    KSequenceNotation::DotK,
                ));
            }

            let mut items = Vec::new();
            let mut tail = StateMacroRemainder::Exact;
            let mut notation = None;
            loop {
                if starts_remainder(input) {
                    tail = parse_remainder_kept(input, context, "k", root)?;
                    break;
                }
                items.push(parse_state_item(input, context)?);
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
                let misplaced = state_error("k", MISPLACED_TAIL, input.span());
                let Some((back, notation)) = parse_back_items(input, context, root, notation)
                else {
                    return Err(misplaced);
                };
                items.extend(back);
                return Ok(KSequence::new(
                    original.clone(),
                    items,
                    tail,
                    notation.unwrap_or(KSequenceNotation::Comma),
                )
                .misplacing(misplaced));
            }
            Ok(KSequence::new(
                original.clone(),
                items,
                tail,
                notation.unwrap_or(KSequenceNotation::Comma),
            ))
        },
        |error| state_error("k", "malformed compiler-owned state syntax", error.span()),
    )
}

/// The refusal of an item after a sequence's tail.
const MISPLACED_TAIL: &str = "the sequence tail must be last";

/// The refusal of an anonymous `..` in an initializer's `k!`.
const INITIALIZER_REMAINDER: &str = "an initializer's `k!` is the cell's whole initial content, so it lists every item and keeps no rest (`..`): there is no subject whose rest the `..` could stand for";

/// The items a `KCell(..)` entry's sequence writes after its tail, `KCell(.., x)` or
/// `KCell(x, .., y)`, with the separator the sequence is written with: `None` where the sequence
/// is no `KCell(..)` entry's, or where what follows the tail is not one more item after each
/// separator (another rest, `.K`, mixed separators), which is refused as written. An item after
/// the computation's rest is the computation cell's mistake, and `KCell(..)` on a cell of another
/// kind is the wrapper's mistake first, so the entry is kept for the judgement that knows the
/// cell's kind ([`KSequence::misplaced_tail`]).
fn parse_back_items(
    input: ParseStream<'_>,
    context: StateMacroContext,
    root: SequenceRoot,
    notation: Option<KSequenceNotation>,
) -> Option<(Vec<TermExpression>, Option<KSequenceNotation>)> {
    use syn::parse::discouraged::Speculative;
    if root != SequenceRoot::Cell {
        return None;
    }
    let ahead = input.fork();
    let mut items = Vec::new();
    let mut notation = notation;
    while !ahead.is_empty() {
        let separator = if ahead.peek(Token![,]) {
            ahead.parse::<Token![,]>().ok()?;
            KSequenceNotation::Comma
        } else if ahead.peek(Token![~]) {
            ahead.parse::<Token![~]>().ok()?;
            ahead.parse::<Token![>]>().ok()?;
            KSequenceNotation::Operator
        } else {
            return None;
        };
        if notation.is_some_and(|previous| previous != separator) {
            return None;
        }
        notation = Some(separator);
        if ahead.is_empty() || ahead.peek(Token![.]) || starts_remainder(&ahead) {
            return None;
        }
        items.push(parse_state_item(&ahead, context).ok()?);
    }
    input.advance_to(&ahead);
    Some((items, notation))
}

/// Whether an initializer cell's own `map![..]` payload is read as a collection literal: one with
/// a rest (`map![k -> v, ..m]`, the update chain over `m`), or one the cell's own map does not
/// read at all, whose error the literal reports. The empty map, a functional update
/// (`map![m; k <- v]`) and the entries alone keep the cell's own reading, whose entries the
/// compiler builds as the literal's value (`krs_compiler`'s built maps).
pub(crate) fn built_map_is_literal(payload: TokenStream) -> bool {
    !matches!(
        parse_unkeyed_map(payload, StateMacroContext::Expression).map(|map| map.body),
        Ok(MapBody::Empty { .. }
            | MapBody::Update { .. }
            | MapBody::Items {
                remainder: StateMacroRemainder::Exact,
                ..
            })
    )
}

/// Parses a `map!` payload held by `invocation`, if an enclosing form read
/// it, and keys it as a sentence of its own.
pub(crate) fn parse_map(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
) -> Result<MapExpression, SyntaxError> {
    parse_unkeyed_map(tokens, context)
        .map(|map| map.invoked_at(invocation))
        .and_then(MapExpression::keyed_standalone)
}

#[expect(
    clippy::too_many_lines,
    reason = "One closed grammar keeps update/item diagnostics local."
)]
fn parse_unkeyed_map(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<MapExpression, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    if let Some((base, bracket)) = split_bracket_update(&tokens) {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                bracket.span(),
            ));
        }
        let base = TermExpression::parse_tokens(base)?;
        let (key, value) = parse_update_inner(bracket.stream())?;
        return Ok(MapExpression::new(
            tokens,
            MapBody::Update { base, key, value },
            None,
        ));
    }
    if let Some((base_tokens, update_tokens)) = split_once_punct(&tokens, ';') {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                tokens.span(),
            ));
        }
        let base = TermExpression::parse_tokens(base_tokens)?;
        let (key, value) = parse_update_inner(update_tokens)?;
        return Ok(MapExpression::new(
            tokens,
            MapBody::Update { base, key, value },
            None,
        ));
    }
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            if input.is_empty() {
                return Ok(MapExpression::empty(original.clone(), false, context));
            }
            // A payload that is only a rest, `map![..]` or `map![r @ ..]`, names no entry: it is
            // read before `.Map`, whose first token a rest's `..` also begins with.
            if starts_remainder(input) {
                let remainder = parse_remainder(input, context, "map")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "map",
                        "the map remainder must be the complete payload",
                        input.span(),
                    ));
                }
                return Ok(MapExpression::items(
                    original.clone(),
                    Vec::new(),
                    remainder,
                    context,
                ));
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
                return Ok(MapExpression::empty(original.clone(), true, context));
            }

            let first = parse_map_item_key(input)?;
            let mut keys = vec![first.to_string()];
            parse_map_item_arrow(input)?;
            let value = parse_state_item(input, context)?;
            let mut items = vec![MapItem {
                key: state_key_tokens(first, context)?,
                value,
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
                // A pattern's items are distinct entries of the map, so two
                // keys that are the same term can never both match; two `_`
                // keys match two distinct entries. A built map writes each
                // entry over the map before it, so of two keys that are the
                // same term the earlier value could never be read.
                let text = key.to_string();
                if text != "_" && keys.contains(&text) {
                    return Err(if context == StateMacroContext::Pattern {
                        state_error(
                            "map",
                            "a map pattern names one key twice; \
                             its items are distinct entries of the map, so no map matches it",
                            key.span(),
                        )
                    } else {
                        crate::collection_literal::repeated_key(&text, key.span())
                    });
                }
                keys.push(text);
                parse_map_item_arrow(input)?;
                let value = parse_state_item(input, context)?;
                items.push(MapItem {
                    key: state_key_tokens(key, context)?,
                    value,
                });
            }
            if !input.is_empty() {
                return Err(state_error(
                    "map",
                    "the map remainder must be last",
                    input.span(),
                ));
            }
            Ok(MapExpression::items(
                original.clone(),
                items,
                remainder,
                context,
            ))
        },
        |error| state_error("map", "malformed compiler-owned state syntax", error.span()),
    )
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

fn parse_map_item_key(input: ParseStream<'_>) -> Result<TokenStream, SyntaxError> {
    let mut tokens = TokenStream::new();
    while !input.is_empty() && !input.peek(Token![->]) && !input.peek(Token![=>]) {
        tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    if tokens.is_empty() {
        return Err(state_error("map", "expected a map-item key", input.span()));
    }
    Ok(tokens)
}

/// Parses a `cells!` payload and keys it as a sentence of its own.
/// A rule's pattern reads a braced instance's cells as keys when
/// `looks_up` ([`parse_instance_list`]).
fn parse_cells(
    tokens: TokenStream,
    context: StateMacroContext,
    looks_up: bool,
) -> Result<CellsExpression, SyntaxError> {
    parse_unkeyed_cells(tokens, context, looks_up, None).and_then(CellsExpression::keyed_standalone)
}

fn parse_unkeyed_cells(
    tokens: TokenStream,
    context: StateMacroContext,
    looks_up: bool,
    invocation: Option<TokenRange>,
) -> Result<CellsExpression, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            let mut entries = Vec::new();
            let mut names = BTreeSet::new();
            let mut remainder = StateMacroRemainder::Exact;
            let mut carried = None;
            while !input.is_empty() {
                if starts_remainder(input) {
                    // A result's anonymous `..` stands for the cells the record does not name,
                    // which a `cells!` result leaves as they are whether it writes the `..` or
                    // not: it is read as its absence. `..name` puts back a subject's named rest.
                    remainder =
                        if context == StateMacroContext::Expression && input.peek(Token![..]) && {
                            let fork = input.fork();
                            fork.parse::<Token![..]>().is_ok() && !fork.peek(Ident)
                        } {
                            input.parse::<Token![..]>().map_err(SyntaxError::from)?;
                            StateMacroRemainder::Exact
                        } else {
                            parse_remainder(input, context, "cells")?
                        };
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
                let Some(last) = plain_path_last(&field) else {
                    return Err(state_error(
                        "cells",
                        "cell fields must be plain Rust paths",
                        field.span(),
                    ));
                };
                let name = last.ident.clone();
                field.segments.pop();
                field.segments.pop_punct();
                let owner = if field.segments.is_empty() {
                    None
                } else {
                    Some(field)
                };
                let identity = owner.as_ref().map_or_else(
                    || name.to_string(),
                    |owner| format!("{}::{name}", path_text(owner)),
                );
                if !names.insert(identity) {
                    return Err(state_error(
                        "cells",
                        "an owner-qualified cell field occurs more than once",
                        name.span(),
                    ));
                }
                input.parse::<Token![:]>().map_err(SyntaxError::from)?;
                let (wrapper, value) =
                    parse_carried_entry_value(input, context, looks_up, &name, &mut carried)?;
                entries.push(CellsEntry {
                    name,
                    owner,
                    wrapper,
                    value,
                    name_key: None,
                    wrapper_key: None,
                });
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            // A result that names no cell leaves every cell as its subject found it, since a
            // `cells!` result leaves each cell it does not name as it is, whether it ends in
            // `..state`, in `..` or in nothing: the state the subject denotes, unchanged.
            // Whether the sentence may say that is its own form's to judge (a rule that writes
            // no cell repeats forever; a claim that a state reaches itself is no mistake). A
            // pattern names at least one cell, as a readable subject does.
            if entries.is_empty() && context == StateMacroContext::Pattern {
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
                payload_key: None,
                remainder_key: None,
                invocation,
                anchors: Vec::new(),
                carried,
            })
        },
        |error| {
            state_error(
                "cells",
                "malformed compiler-owned state syntax",
                error.span(),
            )
        },
    )
}

/// [`parse_entry_value`], where a record value whose children write a `?` cell's presence is read
/// without them, or as the names they bind ([`RecordPresences`]), and so is a result instance
/// record's child whose value the term reader refuses; the first such refusal is kept in
/// `carried` ([`PartFaults`]).
fn parse_carried_entry_value(
    input: ParseStream<'_>,
    context: StateMacroContext,
    looks_up: bool,
    cell: &Ident,
    carried: &mut Option<SyntaxError>,
) -> Result<(Option<ReadWrapper>, StateTerm), SyntaxError> {
    let faults = PartFaults::new(context);
    let fork = input.fork();
    let mut value = TokenStream::new();
    while !fork.is_empty() && !fork.peek(Token![,]) {
        value.extend([fork.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    let parsed = match RecordPresences::of(&value, context) {
        Some(presences) => {
            syn::parse::discouraged::Speculative::advance_to(input, &fork);
            presences.carry(&faults)?;
            structured_with(
                presences.read,
                |input| parse_entry_value(input, context, looks_up, cell, &faults),
                |error| state_error("cells", "malformed fragment", error.span()),
            )?
        }
        None => parse_entry_value(input, context, looks_up, cell, &faults)?,
    };
    if let Some(fault) = faults.first() {
        carried.get_or_insert(fault);
    }
    Ok(parsed)
}

/// The one rule for which faults wait (RDRB): a fault of a part of an entry waits for the
/// judgement of the whole it is in. A part is a record's child (a group record's or an instance
/// record's) or an item of a sequence; the whole is the entry, judged against its cell's kind,
/// each record child against its own cell's kind, and then the sentence's pairing. Which
/// mistake an author meets first follows what is wrong: a part's fault is only an answer once
/// the whole it is in is something the part can be wrong inside, and a part's limit (a `?`
/// child's presence, which no record names yet) never hides a principle that refuses the
/// whole (a record on a leaf, a presence on a cell that is not optional).
///
/// So the reader reads the whole without the faulty part and keeps the part's refusal, which
/// the collector raises once the whole is judged ([`CellsExpression::misplaced_tail`],
/// [`crate::RuleClause::part_refusal`]). What the whole needs of the part is kept: every name
/// the part binds, since the rest of the sentence may read it. In a result a part binds none, so
/// it is left out; in a pattern it is read as the names it binds (a presence `Some(p)` as `p`,
/// `None` as `_`). Where the reader cannot read those names (a pattern child the term reader
/// refuses), leaving the part out would change what the rule matches and unbind its names, so
/// the fault cannot wait and is the record's at once ([`Self::carry`]).
pub(crate) struct PartFaults {
    context: Option<StateMacroContext>,
    first: RefCell<Option<SyntaxError>>,
}

impl PartFaults {
    /// The faults of the parts of an entry read in `context`.
    pub(crate) const fn new(context: StateMacroContext) -> Self {
        Self {
            context: Some(context),
            first: RefCell::new(None),
        }
    }

    /// Faults nowhere: a reader that is itself a part's (the group-record reader of a
    /// `k::fragment!` with a map child), whose whole is read by another reader.
    const fn none() -> Self {
        Self {
            context: None,
            first: RefCell::new(None),
        }
    }

    /// Keeps `fault`, a part's, until the whole is judged (`Ok(())`), or hands it back where it
    /// cannot wait: `keeps_names` says whether the reader reads the names the part binds.
    pub(crate) fn carry(&self, fault: SyntaxError, keeps_names: bool) -> Result<(), SyntaxError> {
        let waits = match self.context {
            Some(StateMacroContext::Expression) => true,
            Some(StateMacroContext::Pattern) => keeps_names,
            None => false,
        };
        if !waits {
            return Err(fault);
        }
        self.first.borrow_mut().get_or_insert(fault);
        Ok(())
    }

    /// The first fault kept, in source order.
    pub(crate) fn first(&self) -> Option<SyntaxError> {
        self.first.borrow_mut().take()
    }
}

/// The children of a record value at a configuration position that write a `?` cell's
/// presence, `Some(..)` or `None`, at any depth of records, and the value read without them.
///
/// At a configuration position (a cell's entry, and each group child of a record there) a
/// record names cells' entries (ruling R4), so a child written `Some(..)` or `None` is that
/// child's presence, its entry, read by the child's declared kind, which the collector judges
/// from the authored spelling: an entry state, and no term (KRS has no `Option` term). The
/// descriptor carries a record's children as terms, so no reading writes such a child yet, a
/// stated limitation ([`record_child_presence`]); it is a fault of a part, which waits for the
/// judgement of the whole ([`PartFaults`]).
pub(crate) struct RecordPresences {
    /// Each such child, in source order.
    found: Vec<Presence>,
    /// The value's tokens with each such child read as its side keeps it: left out of a result,
    /// and in a pattern read as the names it binds, `Some(p)` as `p` and `None` as `_`.
    pub(crate) read: TokenStream,
}

impl RecordPresences {
    /// The presences of `value`, an entry's value read in `context`, where it is a record,
    /// `Path { .. }`, a `k::fragment![Path { .. }]`, either under `name @`, or any of these as the
    /// content of the entry's own `Some(..)`, and one of its children, or of the records its
    /// children write, at any depth, is `Some(..)` or `None`; `None` otherwise.
    ///
    /// The content of a `?` group's `Some(..)` is the present group's record, at the group's own
    /// configuration position as a fixed group's record is at its cell's, so its children are
    /// their cells' entries there too; the entry's presence is the group's, kept as written.
    pub(crate) fn of(value: &TokenStream, context: StateMacroContext) -> Option<Self> {
        let mut found = Vec::new();
        let trees = value.clone().into_iter().collect::<Vec<_>>();
        let read = marked_presences(&trees, context, &mut found)?;
        (!found.is_empty()).then_some(Self { found, read })
    }

    /// Keeps the first presence's refusal in `faults`, the limit a group record's child meets
    /// ([`record_child_presence`]): the part's names are kept, so it waits.
    pub(crate) fn carry(&self, faults: &PartFaults) -> Result<(), SyntaxError> {
        match self.found.first() {
            Some(presence) => faults.carry(
                SyntaxError::new(
                    record_child_presence(&presence.child, presence.present),
                    presence.span,
                ),
                true,
            ),
            None => Ok(()),
        }
    }
}

/// One record child that writes a `?` cell's presence ([`RecordPresences`]).
#[derive(Clone, Debug)]
pub(crate) struct Presence {
    /// The child's name, unraw.
    child: String,
    /// `Some(..)`, or `None`.
    present: bool,
    /// The span of its `Some` or `None`.
    span: Span,
}

/// [`RecordPresences::of`] over an entry value's trees, through the entry's own marks, its
/// `Some(..)` and a leaf's `Cell(..)`: the record inside is the cell's content as written there
/// (a `?` group's present record, or a group's cell term a leaf holds), so its children are the
/// same entries, and the marks are kept as written.
fn marked_presences(
    trees: &[TokenTree],
    context: StateMacroContext,
    found: &mut Vec<Presence>,
) -> Option<TokenStream> {
    let marked = match trees {
        [TokenTree::Ident(_), TokenTree::Group(_)]
            if PresenceTokens::spelled(trees).is_some_and(|(_, inside)| inside.is_some()) =>
        {
            true
        }
        [prefix @ .., TokenTree::Ident(cell), TokenTree::Group(body)]
            if cell == "Cell" && body.delimiter() == Delimiter::Parenthesis =>
        {
            let (chunks, remainder) = prefix.as_chunks::<3>();
            remainder.is_empty()
                && chunks.iter().all(|chunk| {
                    matches!(chunk, [TokenTree::Ident(_), TokenTree::Punct(first), TokenTree::Punct(second)]
                        if first.as_char() == ':' && second.as_char() == ':')
                })
        }
        _ => false,
    };
    let Some((TokenTree::Group(body), head)) = trees.split_last().filter(|_| marked) else {
        return record_presences(trees, context, found);
    };
    let inside = body.stream().into_iter().collect::<Vec<_>>();
    let mut group =
        proc_macro2::Group::new(body.delimiter(), marked_presences(&inside, context, found)?);
    group.set_span(body.span());
    let mut read = head.iter().cloned().collect::<TokenStream>();
    read.extend([TokenTree::Group(group)]);
    Some(read)
}

/// [`RecordPresences::of`] over a value's trees: the value read, where it is a record.
fn record_presences(
    trees: &[TokenTree],
    context: StateMacroContext,
    found: &mut Vec<Presence>,
) -> Option<TokenStream> {
    if let [TokenTree::Ident(label), TokenTree::Punct(at), pattern @ ..] = trees
        && at.as_char() == '@'
    {
        let mut read = TokenStream::from_iter([
            TokenTree::Ident(label.clone()),
            TokenTree::Punct(at.clone()),
        ]);
        read.extend(record_presences(pattern, context, found)?);
        return Some(read);
    }
    let value = trees.iter().cloned().collect::<TokenStream>();
    if let Some((name, payload)) = qualified_macro_payload(&value) {
        if name != "fragment" {
            return None;
        }
        let (TokenTree::Group(invocation), head) = trees.split_last()? else {
            return None;
        };
        let payload = payload.into_iter().collect::<Vec<_>>();
        let mut group = proc_macro2::Group::new(
            invocation.delimiter(),
            braced_presences(&payload, context, found)?,
        );
        group.set_span(invocation.span());
        let mut read = head.iter().cloned().collect::<TokenStream>();
        read.extend([TokenTree::Group(group)]);
        return Some(read);
    }
    braced_presences(trees, context, found)
}

/// [`record_presences`] of a record `Path { .. }`'s trees.
fn braced_presences(
    trees: &[TokenTree],
    context: StateMacroContext,
    found: &mut Vec<Presence>,
) -> Option<TokenStream> {
    let (TokenTree::Group(body), owner) = trees.split_last()? else {
        return None;
    };
    if body.delimiter() != Delimiter::Brace
        || owner.is_empty()
        || syn::parse2::<Path>(owner.iter().cloned().collect()).is_err()
    {
        return None;
    }
    let mut items = vec![Vec::new()];
    for tree in body.stream() {
        if matches!(&tree, TokenTree::Punct(comma) if comma.as_char() == ',') {
            items.push(Vec::new());
        } else {
            items.last_mut()?.push(tree);
        }
    }
    let mut fields = TokenStream::new();
    for item in items.into_iter().filter(|item| !item.is_empty()) {
        let read = match item.as_slice() {
            [TokenTree::Ident(child), TokenTree::Punct(colon), value @ ..]
                if colon.as_char() == ':' =>
            {
                field_presences(child, colon, value, context, found)
            }
            _ => Some(item.into_iter().collect()),
        };
        let Some(read) = read else {
            continue;
        };
        if !fields.is_empty() {
            fields.extend([TokenTree::Punct(proc_macro2::Punct::new(
                ',',
                proc_macro2::Spacing::Alone,
            ))]);
        }
        fields.extend(read);
    }
    let mut group = proc_macro2::Group::new(Delimiter::Brace, fields);
    group.set_span(body.span());
    let mut read = owner.iter().cloned().collect::<TokenStream>();
    read.extend([TokenTree::Group(group)]);
    Some(read)
}

/// One record field `child: value` read by [`record_presences`]: `None` where it is a presence
/// a result leaves out.
fn field_presences(
    child: &Ident,
    colon: &proc_macro2::Punct,
    value: &[TokenTree],
    context: StateMacroContext,
    found: &mut Vec<Presence>,
) -> Option<TokenStream> {
    let mut read = TokenStream::from_iter([
        TokenTree::Ident(child.clone()),
        TokenTree::Punct(colon.clone()),
    ]);
    let Some((head, inside)) = PresenceTokens::spelled(value) else {
        match record_presences(value, context, found) {
            Some(nested) => read.extend(nested),
            None => read.extend(value.iter().cloned()),
        }
        return Some(read);
    };
    found.push(Presence {
        child: syn::ext::IdentExt::unraw(child).to_string(),
        present: inside.is_some(),
        span: head.span(),
    });
    let names = inside.unwrap_or_default();
    if context == StateMacroContext::Expression {
        return None;
    }
    if names.is_empty() {
        read.extend([TokenTree::Ident(proc_macro2::Ident::new("_", head.span()))]);
    } else {
        read.extend(names);
    }
    Some(read)
}

/// The limit a group record's `?` child written `Some(..)` (`present`) or `None` meets, read as a
/// readable record's field or a `k::fragment!` child: no term, and in a group record the child's
/// entry, which a group record does not name yet.
pub(crate) fn record_child_presence(child: &str, present: bool) -> SyntaxErrorKind {
    let written = presence_written(present);
    SyntaxErrorKind::InstanceChildMultiplicity {
        reason: format!(
            "the record's field `{child}` holds {written}, and no term: KRS has no `Option` term; \
             in a group record it is the `?` child's entry, which a group record does not name \
             yet, as {INSTANCE_CHILD_MULTIPLICITY}"
        ),
    }
}

/// The wrapper a `cells!` entry's value is read in.
#[derive(Clone, Debug)]
struct ReadWrapper {
    /// The authored `Cell`/`KCell` path, or the implied one's.
    path: Path,
    /// Whether the wrapper is implied: a content written without its wrapper is read under
    /// `Cell`, at the content, while its refusal waits for the judgement of the entry
    /// ([`parse_group_entry`]).
    implied: bool,
}

/// Parses one `cells!` entry value: `None`, `Some(..)` around a leaf or
/// group entry, an instance list, a wrapped leaf, or a group entry.
fn parse_entry_value(
    input: ParseStream<'_>,
    context: StateMacroContext,
    looks_up: bool,
    cell: &Ident,
    faults: &PartFaults,
) -> Result<(Option<ReadWrapper>, StateTerm), SyntaxError> {
    if let Some(range) = parse_option_none(input)? {
        return Ok((None, StateTerm::Absent(range)));
    }
    if starts_option_some(input) {
        input.parse::<Ident>().map_err(SyntaxError::from)?;
        let inner = parse_parenthesized_tokens(input).map_err(SyntaxError::from)?;
        let span = inner.span();
        let (wrapper, value) = structured_with(
            inner,
            move |inner| {
                let parsed = parse_entry_value(inner, context, looks_up, cell, faults)?;
                if !inner.is_empty() {
                    return Err(state_error(
                        "cells",
                        "`Some(..)` holds one cell entry",
                        inner.span(),
                    ));
                }
                Ok(parsed)
            },
            |error| state_error("cells", "malformed `Some(..)` entry", error.span()),
        )?;
        if matches!(
            value,
            StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_)
        ) {
            return Err(state_error(
                "cells",
                "`Some(..)` holds a `Cell(..)` leaf entry or a nested-cell entry",
                span,
            ));
        }
        return Ok((wrapper, StateTerm::Present(Box::new(value))));
    }
    if input.peek(syn::token::Brace) || input.peek(syn::token::Bracket) {
        let group: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        return Ok((
            None,
            StateTerm::Instances(parse_instance_list(&group, context, looks_up, faults)?),
        ));
    }
    if !starts_wrapped_entry(input) {
        let (value, implied) = parse_group_entry(input, context, cell, faults)?;
        let wrapper = implied.map(|span| ReadWrapper {
            path: Path::from(Ident::new("Cell", span)),
            implied: true,
        });
        return Ok((wrapper, value));
    }
    let wrapper: Path = input.parse().map_err(SyntaxError::from)?;
    let Some(last) = plain_path_last(&wrapper) else {
        return Err(state_error(
            "cells",
            "cell wrappers must be plain Rust paths",
            wrapper.span(),
        ));
    };
    let (value_tokens, parentheses) =
        parse_parenthesized_group(input).map_err(SyntaxError::from)?;
    let wrapper_name = last.ident.to_string();
    let value = match wrapper_name.as_str() {
        // `KCell(..)`'s parentheses hold the K sequence, as `k::k![..]`'s
        // brackets do, as the cell's whole content; the wrapper path is a
        // node of its own.
        "KCell" => StateTerm::KSequence(parse_cell_k_sequence(
            value_tokens,
            context,
            Some(parentheses),
        )?),
        "Cell" => {
            let leaf = crate::parse::strip_trailing_comma(value_tokens);
            match named_rest_alone(&leaf, context) {
                Some(rest) => StateTerm::Term(state_term_tokens(rest, context)?),
                None => match kept_rest_term(&leaf, context)? {
                    Some(kept) => StateTerm::Term(kept),
                    None => parse_state_term(leaf, context)?,
                },
            }
        }
        _ => unreachable!("an entry's wrapper is `Cell` or `KCell` ([`starts_wrapped_entry`])"),
    };
    Ok((
        Some(ReadWrapper {
            path: wrapper,
            implied: false,
        }),
        value,
    ))
}

/// A result's brackets `leaf` whose one bare `..` keeps the rest its subject's `..` matched, read
/// as the list notation they write with that rest at the end of their root spine
/// ([`kept_rest_marked`], [`TermExpression::keeping_root_rest`]): a list cell's whole content, or
/// an instance child's, which is a cell as well. `None` for any other leaf.
pub(crate) fn kept_rest_term(
    leaf: &TokenStream,
    context: StateMacroContext,
) -> Result<Option<TermExpression>, SyntaxError> {
    let Some(marked) = kept_rest_marked(leaf, context) else {
        return Ok(None);
    };
    TermExpression::parse_tokens(marked)?
        .keeping_root_rest(KEPT_REST_MARKER)?
        .map(Some)
        .ok_or_else(|| state_error("cells", "malformed list cell brackets", leaf.span()))
}

/// The reference a result's kept `..` is read through ([`kept_rest_marked`]); the term reads
/// it back as the unnamed rest ([`TermExpression::keeping_root_rest`]), so no term holds it.
const KEPT_REST_MARKER: &str = "__krs_kept_rest";

/// A result leaf's brackets, the whole content of a list cell, whose one bare `..` is the cell's
/// unnamed rest, kept (P6, D2): the rest of the list the subject's `..` matched, as a
/// `KCell(..)` entry's `..` keeps its computation's. Among other elements the `..` is written
/// `..marker` for the expression grammar, which reads the rest it ends the brackets with; brackets
/// holding only the `..` (`[..]`) are the rest itself, the marker alone (R2-B: the root is its own
/// spine's end, so the list is the kept rest). The term then reads the marker back as the unnamed
/// rest. A pattern's `..` already is one, the wildcard that ends its brackets. `None` for any
/// other leaf, which is read as written: brackets nested deeper, two rests, and a leaf that
/// writes the reserved marker itself, which binder validation refuses as written. Whether the
/// subject matched a rest for the result to keep is the compiler's to judge, and the entry
/// pairing's, from the tokens as written.
fn kept_rest_marked(leaf: &TokenStream, context: StateMacroContext) -> Option<TokenStream> {
    fn reserved(tokens: TokenStream) -> bool {
        tokens.into_iter().any(|tree| match tree {
            TokenTree::Ident(ident) => ident.to_string().contains(krs_ir::ir::RESERVED_MARKER),
            TokenTree::Group(group) => reserved(group.stream()),
            _ => false,
        })
    }
    if context != StateMacroContext::Expression {
        return None;
    }
    let mut trees = leaf.clone().into_iter();
    let (Some(TokenTree::Group(group)), None) = (trees.next(), trees.next()) else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket || reserved(group.stream()) {
        return None;
    }
    // Each element with the comma that ends it, if any.
    let mut elements = vec![(Vec::new(), None)];
    for tree in group.stream() {
        match &tree {
            TokenTree::Punct(comma) if comma.as_char() == ',' => {
                elements.last_mut().expect("one element").1 = Some(tree);
                elements.push((Vec::new(), None));
            }
            _ => elements.last_mut().expect("one element").0.push(tree),
        }
    }
    let dots = |element: &[TokenTree]| match element {
        [TokenTree::Punct(first), TokenTree::Punct(second)] => {
            first.as_char() == '.'
                && first.spacing() == proc_macro2::Spacing::Joint
                && second.as_char() == '.'
        }
        _ => false,
    };
    let written = elements
        .iter()
        .filter(|(element, _)| !element.is_empty())
        .count();
    if elements.iter().filter(|(element, _)| dots(element)).count() != 1 {
        return None;
    }
    // Brackets holding only the `..`, `[..]`, write no item: the content is the rest itself,
    // the marker alone, which the term reads back as brackets holding the unnamed rest.
    if written == 1 {
        let (element, _) = elements
            .iter()
            .find(|(element, _)| dots(element))
            .expect("one element is the rest");
        let rest = Ident::new(KEPT_REST_MARKER, element[0].span());
        return Some(quote!(#rest));
    }
    let mut marked = TokenStream::new();
    for (element, comma) in elements {
        if dots(&element) {
            let rest = Ident::new(KEPT_REST_MARKER, element[0].span());
            marked.extend(element);
            marked.extend(quote!(#rest));
        } else {
            marked.extend(element);
        }
        marked.extend(comma);
    }
    let mut brackets = proc_macro2::Group::new(Delimiter::Bracket, marked);
    brackets.set_span(group.span());
    Some(TokenTree::Group(brackets).into())
}

/// Parses `None` (optionally `Option::None`) when it is the whole entry value.
fn parse_option_none(input: ParseStream<'_>) -> Result<Option<TokenRange>, SyntaxError> {
    let fork = input.fork();
    let Ok(path) = fork.parse::<Path>() else {
        return Ok(None);
    };
    if !crate::initializer::is_option_variant(&path, "None")
        || !(fork.is_empty() || fork.peek(Token![,]))
    {
        return Ok(None);
    }
    let path: Path = input.parse().map_err(SyntaxError::from)?;
    Ok(Some(TokenRange::for_tokens(&path)?))
}

/// Whether the entry value is `Some(..)`.
fn starts_option_some(input: ParseStream<'_>) -> bool {
    let fork = input.fork();
    fork.parse::<Ident>()
        .is_ok_and(|ident| ident == "Some" && fork.peek(syn::token::Paren))
}

/// Parses the `{ .. }` or `[ .. ]` payload of a collection entry.
fn parse_instance_list(
    group: &proc_macro2::Group,
    context: StateMacroContext,
    looks_up: bool,
    faults: &PartFaults,
) -> Result<InstanceList, SyntaxError> {
    let delimiter = match group.delimiter() {
        Delimiter::Brace => InstanceListDelimiter::Brace,
        Delimiter::Bracket => InstanceListDelimiter::Bracket,
        _ => {
            return Err(state_error(
                "cells",
                "a collection entry is `{ .. }` (Set, Map) or `[ .. ]` (List)",
                group.span(),
            ));
        }
    };
    // A braced list writes a Set collection, which a rule's pattern looks up
    // by an instance as by an element, or a Map collection, whose instances
    // are matched: only the cell's declared type tells them apart, after
    // resolution, so a rule's braced instance reads its cells as a map's key
    // is read. A claim's start state holds its instances as written.
    let keys = looks_up
        && delimiter == InstanceListDelimiter::Brace
        && context == StateMacroContext::Pattern;
    structured_with(
        group.stream(),
        move |input| {
            let mut front = Vec::new();
            let mut back = Vec::new();
            let mut rest = None;
            while !input.is_empty() {
                if starts_instance_rest(input) {
                    if rest.is_some() {
                        return Err(state_error(
                            "cells",
                            "a collection entry has at most one rest",
                            input.span(),
                        ));
                    }
                    rest = Some(parse_instance_list_rest(input, context)?);
                } else if rest.is_some() {
                    if delimiter == InstanceListDelimiter::Brace {
                        return Err(state_error(
                            "cells",
                            "the rest of a Set or Map collection is last",
                            input.span(),
                        ));
                    }
                    back.push(parse_instance_list_item(input, context, keys, faults)?);
                } else {
                    front.push(parse_instance_list_item(input, context, keys, faults)?);
                }
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            Ok(InstanceList::new(
                delimiter,
                front,
                rest.unwrap_or(StateMacroRemainder::Exact),
                back,
            ))
        },
        |error| state_error("cells", "malformed collection entry", error.span()),
    )
}

/// Whether the next list item is a collection rest: `..`, `name @ ..`, or `..name`.
fn starts_instance_rest(input: ParseStream<'_>) -> bool {
    starts_remainder(input)
}

/// Parses a collection rest; a result may write a bare `..` as well as `..name`.
fn parse_instance_list_rest(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<StateMacroRemainder, SyntaxError> {
    if context == StateMacroContext::Expression && input.peek(Token![..]) {
        let fork = input.fork();
        fork.parse::<Token![..]>().map_err(SyntaxError::from)?;
        if !fork.peek(Ident) {
            let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
            return Ok(StateMacroRemainder::Anonymous(TokenRange::for_tokens(
                &dots,
            )?));
        }
    }
    parse_remainder(input, context, "cells")
}

/// Parses one item of an instance list: one name or `_`, the whole instance it stands for
/// ([`InstanceItem::whole`]), or an instance record ([`parse_instance_item`]).
fn parse_instance_list_item(
    input: ParseStream<'_>,
    context: StateMacroContext,
    keys: bool,
    faults: &PartFaults,
) -> Result<InstanceItem, SyntaxError> {
    let fork = input.fork();
    if let Ok(name) = fork.parse::<TokenTree>()
        && matches!(name, TokenTree::Ident(_))
        && (fork.is_empty() || fork.peek(Token![,]))
        && let Some(item) = InstanceItem::whole(&TokenStream::from(name), context)?
    {
        input.parse::<TokenTree>().map_err(SyntaxError::from)?;
        return Ok(item);
    }
    parse_instance_item(input, context, keys, faults)
}

/// Parses one instance record: `[label @] Decl { .. }` or
/// `[label @] k::fragment![Decl { .. }]`; its cells are read as keys when
/// `keys` ([`parse_instance_list`]).
fn parse_instance_item(
    input: ParseStream<'_>,
    context: StateMacroContext,
    keys: bool,
    faults: &PartFaults,
) -> Result<InstanceItem, SyntaxError> {
    let start = input.cursor();
    let label = if input.peek(Ident) && input.peek2(Token![@]) {
        let label: Ident = input.parse().map_err(SyntaxError::from)?;
        input.parse::<Token![@]>().map_err(SyntaxError::from)?;
        if context == StateMacroContext::Expression {
            return Err(state_error(
                "cells",
                "a result instance has no label; write `..label` inside it to update the matched instance",
                label.span(),
            ));
        }
        crate::parse::validate_authored_binder(&label.to_string(), label.span())?;
        Some(label)
    } else {
        None
    };
    let path: Path = input.parse().map_err(SyntaxError::from)?;
    let (owner, body, fragment) = if input.peek(Token![!]) {
        if plain_path_last(&path).is_none_or(|last| last.ident != "fragment") {
            return Err(state_error(
                "cells",
                "a collection instance is a cell record `Decl { .. }` or `k::fragment![Decl { .. }]`",
                path.span(),
            ));
        }
        input.parse::<Token![!]>().map_err(SyntaxError::from)?;
        let group: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        let (owner, body) = structured_with(
            crate::parse::strip_trailing_comma(group.stream()),
            |inner| {
                let owner: Path = inner.parse().map_err(SyntaxError::from)?;
                let body: proc_macro2::Group = inner.parse().map_err(SyntaxError::from)?;
                if !inner.is_empty() || body.delimiter() != Delimiter::Brace {
                    return Err(state_error(
                        "cells",
                        "`k::fragment![..]` holds one cell record `Decl { .. }`",
                        inner.span(),
                    ));
                }
                Ok((owner, body))
            },
            |error| state_error("cells", "malformed fragment! instance", error.span()),
        )?;
        (owner, body, true)
    } else {
        let body: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        if body.delimiter() != Delimiter::Brace {
            return Err(state_error(
                "cells",
                "a collection instance is a cell record `Decl { .. }`",
                body.span(),
            ));
        }
        (path, body, false)
    };
    if !crate::path::is_plain_path(&owner) {
        return Err(state_error(
            "cells",
            "an instance's cell struct is a plain Rust path",
            owner.span(),
        ));
    }
    let (fields, rest) = parse_instance_record(&body, context, (keys, true), faults)?;
    let mut tokens = TokenStream::new();
    let mut cursor = start;
    while cursor != input.cursor() {
        let Some((token, next)) = cursor.token_tree() else {
            break;
        };
        tokens.extend([token]);
        cursor = next;
    }
    Ok(InstanceItem {
        range: TokenRange::for_tokens(&tokens)?,
        label,
        head: Some(Box::new(record_head(&owner, fragment)?)),
        owner: Some(owner),
        fields,
        rest,
        fragment,
        key: None,
    })
}

/// Parses the braced body of an instance record: `child: value` entries, or
/// the shorthand `child` for `child: child`, and a final rest. A child whose value the term
/// reader refuses is left out where `faults` carries it. `keys` reads the children as keys, and
/// `kept` lets a result child's `..` keep the rest its subject's matched: an instance's child
/// keeps it, and a group record's, which a group's term may hold, does not yet.
fn parse_instance_record(
    body: &proc_macro2::Group,
    context: StateMacroContext,
    (keys, kept): (bool, bool),
    faults: &PartFaults,
) -> Result<(Vec<InstanceField>, InstanceRest), SyntaxError> {
    structured_with(
        body.stream(),
        move |input| {
            let mut fields: Vec<InstanceField> = Vec::new();
            let mut rest = InstanceRest::Exact;
            while !input.is_empty() {
                if input.peek(Token![..]) {
                    let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
                    rest = if input.peek(Ident) {
                        let label: Ident = input.parse().map_err(SyntaxError::from)?;
                        if context == StateMacroContext::Pattern {
                            return Err(state_error(
                                "cells",
                                "`..label` updates a matched instance in a result; a pattern instance writes `..`",
                                label.span(),
                            ));
                        }
                        InstanceRest::Update {
                            range: TokenRange::for_tokens(&quote!(#dots #label))?,
                            label,
                        }
                    } else {
                        InstanceRest::Open(TokenRange::for_tokens(&dots)?)
                    };
                    if !input.is_empty() {
                        return Err(state_error(
                            "cells",
                            "an instance record's rest is last",
                            input.span(),
                        ));
                    }
                    break;
                }
                let name: Ident = input.parse().map_err(SyntaxError::from)?;
                if fields.iter().any(|field| field.name == name) {
                    return Err(state_error(
                        "cells",
                        "an instance record names each child once",
                        name.span(),
                    ));
                }
                let mut tokens = TokenStream::new();
                if input.is_empty() || input.peek(Token![,]) {
                    // `balance` is `balance: balance`, Rust's field-init
                    // shorthand: the value is the child name's own token, a
                    // binder in a pattern and the bound variable in a result.
                    tokens.extend([TokenTree::Ident(name.clone())]);
                } else {
                    input.parse::<Token![:]>().map_err(SyntaxError::from)?;
                }
                while !input.is_empty() && !input.peek(Token![,]) {
                    tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
                }
                if tokens.is_empty() {
                    return Err(state_error(
                        "cells",
                        "an instance child needs a value",
                        name.span(),
                    ));
                }
                // A `?` cell's `Some(..)` or `None` in a record the child writes is the same
                // presence inside one instance, which the collector says once the entries are
                // admitted ([`crate::cell_entries::instance_child_presence`]): the child is read
                // without it, as a record at a cell's position is ([`RecordPresences`]).
                let read = RecordPresences::of(&tokens, context)
                    .map_or_else(|| tokens.clone(), |presences| presences.read);
                match parse_instance_child(read, context, (keys, kept)) {
                    Ok(value) => fields.push(InstanceField::new(name, value)),
                    // The term reader read no names of the child: in a pattern its fault is the
                    // record's at once.
                    Err(fault) => faults.carry(fault, false)?,
                }
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            Ok((fields, rest))
        },
        |error| state_error("cells", "malformed instance record", error.span()),
    )
}

/// What the reader knows of the names of the sentence it reads ([`with_declared_binders`]): the
/// term binders its typed parameters declare, and, for a result, the remainders its subject binds.
#[derive(Clone, Debug, Default)]
pub(crate) struct SentenceBinders {
    /// The names the typed parameters declare, the sentence's term binders.
    pub(crate) declared: std::collections::BTreeSet<String>,
    /// The names the subject binds as remainders (`rest @ ..` of a computation, a map, ..).
    pub(crate) remainders: std::collections::BTreeSet<String>,
}

thread_local! {
    /// The binders of the sentence being read ([`with_declared_binders`]); `None` outside a
    /// sentence whose signature the reader sees.
    static SENTENCE_BINDERS: std::cell::RefCell<Option<SentenceBinders>> =
        const { std::cell::RefCell::new(None) };
}

/// Runs `read` with `binders` as what the reader knows of the sentence's names, by which an
/// instance child's named rest reads as a term or as a remainder ([`remainder_sequence`]).
pub(crate) fn with_declared_binders<T>(binders: SentenceBinders, read: impl FnOnce() -> T) -> T {
    /// Restores the outer binders when dropped, so a read that unwinds (a proc-macro server
    /// reuses its threads) leaves no later read with these.
    struct Restore(Option<SentenceBinders>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let outer = self.0.take();
            SENTENCE_BINDERS.with(|binders| *binders.borrow_mut() = outer);
        }
    }
    let _restore = Restore(SENTENCE_BINDERS.with(|outer| outer.replace(Some(binders))));
    read()
}

/// The sequence an instance child's brackets are when their last item is a remainder: in a
/// pattern a rest `[x, rest @ ..]` the signature does not declare, which binds a remainder as a
/// computation cell's `KCell(x, rest @ ..)` does (a declared one is a term binder of its declared
/// sort, as a list cell's `Cell([x, rest @ ..])` is); in a result `[y, ..rest]` where the subject
/// binds `rest` as a remainder, which the result writes back as `KCell(y, ..rest)` does. A result's
/// `..name` of anything else, a declared term, a constant or a name bound nowhere, is the list
/// notation that writes that term, as at the twin cell. The child is a cell, so its kind reads the
/// sequence: a computation's items before its rest, as at the computation cell; a list, whose rest
/// is a term of the list's sort, refuses it. `None` outside a sentence whose signature the reader
/// sees and for any other value.
fn remainder_sequence(
    tokens: &TokenStream,
    context: StateMacroContext,
) -> Result<Option<KSequence>, SyntaxError> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let [TokenTree::Group(group)] = trees.as_slice() else {
        return Ok(None);
    };
    if group.delimiter() != Delimiter::Bracket {
        return Ok(None);
    }
    let items = crate::parse::strip_trailing_comma(group.stream())
        .into_iter()
        .collect::<Vec<_>>();
    let mut chunks = items
        .split(|tree| matches!(tree, TokenTree::Punct(comma) if comma.as_char() == ','))
        .collect::<Vec<_>>();
    let Some(last) = chunks.pop() else {
        return Ok(None);
    };
    let dots = |first: &proc_macro2::Punct, second: &proc_macro2::Punct| {
        first.as_char() == '.'
            && first.spacing() == proc_macro2::Spacing::Joint
            && second.as_char() == '.'
    };
    let rest = match (last, context) {
        (
            [
                TokenTree::Ident(rest),
                TokenTree::Punct(at),
                TokenTree::Punct(first),
                TokenTree::Punct(second),
            ],
            StateMacroContext::Pattern,
        ) if at.as_char() == '@' && dots(first, second) => rest,
        (
            [
                TokenTree::Punct(first),
                TokenTree::Punct(second),
                TokenTree::Ident(rest),
            ],
            StateMacroContext::Expression,
        ) if dots(first, second) => rest,
        _ => return Ok(None),
    };
    let other_rest = chunks.iter().any(|chunk| {
        chunk
            .windows(2)
            .any(|pair| matches!(pair, [TokenTree::Punct(first), TokenTree::Punct(second)] if dots(first, second)))
    });
    let name = syn::ext::IdentExt::unraw(rest).to_string();
    let remainder = SENTENCE_BINDERS.with(|binders| {
        binders
            .borrow()
            .as_ref()
            .is_some_and(|binders| match context {
                StateMacroContext::Pattern => !binders.declared.contains(&name),
                StateMacroContext::Expression => binders.remainders.contains(&name),
            })
    });
    if other_rest || !remainder {
        return Ok(None);
    }
    parse_k_sequence(
        group.stream(),
        context,
        Some(TokenRange::for_tokens(tokens)?),
    )
    .map(Some)
}

/// Parses one instance child value: `k::k![..]`, `map![..]`, a term (a
/// leaf's content or a whole nested cell, which semantic analysis tells
/// apart by the declaration), read as a key when `keys`, or a `?` cell's
/// `Some(..)` around one of those or `None`, read by their spelling as a cell
/// entry's are: the state the collector judges, and refuses as not lowered
/// yet once it admits it ([`INSTANCE_CHILD_MULTIPLICITY`]).
fn parse_instance_child(
    tokens: TokenStream,
    context: StateMacroContext,
    (keys, kept): (bool, bool),
) -> Result<StateTerm, SyntaxError> {
    match PresenceTokens::of(&tokens)? {
        Some(PresenceTokens::Absent(range)) => return Ok(StateTerm::Absent(range)),
        Some(PresenceTokens::Present(inside)) => {
            let span = TokenRange::for_tokens(&tokens)?.first();
            let value = parse_instance_child(inside, context, (keys, kept))?;
            if matches!(value, StateTerm::Present(_) | StateTerm::Absent(_)) {
                return Err(state_error(
                    "cells",
                    "an instance child's `Some(..)` holds the cell's content",
                    span,
                ));
            }
            return Ok(StateTerm::Present(Box::new(value)));
        }
        None => {}
    }
    if let Some((name, payload)) = qualified_macro_payload(&tokens) {
        let invocation = || TokenRange::for_tokens(&tokens).map(Some);
        match name.as_str() {
            "k" => {
                return Ok(StateTerm::KSequence(parse_k_sequence(
                    payload,
                    context,
                    invocation()?,
                )?));
            }
            "map" => {
                return Ok(StateTerm::Map(
                    parse_map(payload, context, invocation()?)?.island_of(macro_path(&tokens)),
                ));
            }
            _ => {}
        }
    }
    if let Some(sequence) = remainder_sequence(&tokens, context)? {
        return Ok(StateTerm::KSequence(sequence));
    }
    // An instance child is a cell, so a result's brackets whose one bare `..` keeps the rest its
    // subject's `..` matched mean what they mean as a list cell's whole content (`Cell([x, ..])`,
    // `Cell([.., x])`): the list notation they write, ending its root spine in that rest. The
    // child's kind reads them: a list's elements, or a computation's items.
    if kept && let Some(kept) = kept_rest_term(&tokens, context)? {
        return Ok(StateTerm::Term(kept));
    }
    Ok(StateTerm::Term(if keys {
        state_key_tokens(tokens, context)?
    } else {
        state_term_tokens(tokens, context)?
    }))
}

/// The path of the macro invocation `path::name!(..)` that `tokens` hold.
fn macro_path(tokens: &TokenStream) -> Option<Path> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let path = trees.get(..trees.len().checked_sub(2)?)?;
    syn::parse2(path.iter().cloned().collect()).ok()
}

/// The last path segment and payload of `path::name!(..)`.
pub(crate) fn qualified_macro_payload(tokens: &TokenStream) -> Option<(String, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let [
        prefix @ ..,
        TokenTree::Ident(name),
        TokenTree::Punct(bang),
        TokenTree::Group(group),
    ] = trees.as_slice()
    else {
        return None;
    };
    if bang.as_char() != '!' {
        return None;
    }
    let (chunks, remainder) = prefix.as_chunks::<3>();
    let qualified = remainder.is_empty()
        && chunks.iter().all(|chunk| {
            matches!(chunk, [TokenTree::Ident(_), TokenTree::Punct(first), TokenTree::Punct(second)]
                if first.as_char() == ':' && second.as_char() == ':')
        });
    qualified.then(|| (name.to_string(), group.stream()))
}

/// Whether the next entry value is a wrapper application `Cell(..)` or `KCell(..)`, as every
/// leaf entry is (or a path application that is no plain path, which is refused as a wrapper);
/// a whole nested-cell entry is not (KF-016), nor is an application of any other plain path
/// (`int::add(a, 1)`, `Cmd::Go()`), which is a term written without a wrapper.
fn starts_wrapped_entry(input: ParseStream<'_>) -> bool {
    let fork = input.fork();
    let Ok(path) = fork.parse::<Path>() else {
        return false;
    };
    fork.peek(syn::token::Paren)
        && plain_path_last(&path)
            .is_none_or(|last| matches!(last.ident.to_string().as_str(), "Cell" | "KCell"))
}

/// The reason given for an entry written as a term without a wrapper (`acc: 0`, `frame: 0`,
/// `acc: int::add(a, 1)`, whose path is no wrapper). The reader does not know which cells are
/// leaves, so the reason is true of either: an entry without a wrapper is a nested cell's, and a
/// leaf's content stands inside its wrapper. It is the entry's whole fault, so it waits for the
/// judgement of the entry against its cell ([`PartFaults`]): on a leaf or the computation the
/// collector answers that the entry lacks its cell's wrapper (`cell-wrapper`), as it answers a
/// binder there (`acc: a`), and on a nested cell, which no wrapper marks, it raises this reason.
const UNWRAPPED_ENTRY: &str = "an entry without a wrapper is a nested cell's: a binder, `_` in a pattern, or `k::fragment![..]`; a leaf cell's content is written inside its wrapper, `Cell(..)`, and the computation's inside `KCell(..)`";

/// The reason given for a whole entry `k::rewrite!(a => b)` whose sides are contents, not entries
/// ([`rewritten_entry`]): a rewrite changes a content where it stands, and a leaf's content
/// stands inside its wrapper (`Cell(k::rewrite!(a => b))`); a nested cell is
/// rewritten child by child, inside its entry.
const REWRITTEN_ENTRY: &str = "a `k::rewrite!` changes a content where it stands, and a leaf cell's content stands inside its wrapper: `Cell(k::rewrite!(a => b))`, and the computation's `KCell(k::rewrite!(a => b), ..)`; a nested cell's entry is a binder, `_`, or `k::fragment![..]`, inside which a child's content is rewritten";

/// Parses a whole nested-cell entry value: a group binder, `_` (patterns
/// only), or a complete `k::fragment!` term (KF-016).
///
/// Any other term, and a `k::rewrite!` of contents, is a content written without its cell's
/// wrapper ([`UNWRAPPED_ENTRY`], [`REWRITTEN_ENTRY`]). Which mistake that is depends on the cell
/// the entry names, which the reader does not know: on a leaf or the computation it is the
/// entry's missing wrapper, on a nested cell a spelling no group entry has. So where its faults
/// wait ([`PartFaults`]) the entry is read as the term it writes, which keeps every name it
/// binds, and its refusal is carried to the judgement of the entry against its cell. Returns the
/// entry's state, and for such a content the span its implied `Cell` wrapper stands at, its first
/// token's.
fn parse_group_entry(
    input: ParseStream<'_>,
    context: StateMacroContext,
    cell: &Ident,
    faults: &PartFaults,
) -> Result<(StateTerm, Option<Span>), SyntaxError> {
    let mut tokens = TokenStream::new();
    while !input.is_empty() && !input.peek(Token![,]) && !starts_remainder(input) {
        tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    let invalid = |span| state_error("cells", UNWRAPPED_ENTRY, span);
    if tokens.is_empty() {
        return Err(invalid(input.span()));
    }
    let span = tokens.span();
    // The implied wrapper stands at the content's first token, a range that every reading of
    // the source gives alike.
    let first = tokens
        .clone()
        .into_iter()
        .next()
        .map_or(span, |tree| tree.span());
    if context == StateMacroContext::Expression
        && let Some(refusal) = pattern_only_entry(&tokens, cell)
    {
        return Err(refusal);
    }
    match rewritten_entry(&tokens) {
        Some(EntryRewrite::Content(refusal)) => {
            let Ok(term) = state_term_tokens(tokens, context) else {
                return Err(refusal);
            };
            faults.carry(refusal, true)?;
            return Ok((StateTerm::Term(term), Some(first)));
        }
        Some(EntryRewrite::Marks(refusal)) => return Err(refusal),
        None => {}
    }
    let fragment = qualified_macro_payload(&tokens).is_some_and(|(name, _)| name == "fragment");
    if let Some(record) = fragment_record(&tokens, context).map_err(|error| {
        crate::list_notation::anonymous_rest_in(
            error,
            crate::list_notation::GROUP_CHILD_ANONYMOUS_REST,
        )
    })? {
        return Ok((StateTerm::Record(Box::new(record)), None));
    }
    let term = state_term_tokens(tokens, context).map_err(|error| match error.kind() {
        // A fragment's child at a configuration position is its cell's entry (ruling R4); a
        // fragment whose children are terms is read as the group's term. A result's anonymous
        // `..` in a child's list keeps no rest, a stated limitation the term reader names; a
        // result's `k::map![k -> v, ..]` is built, so its anonymous `..` names no map the entries
        // are written over, the literal's own refusal whichever reading it has. A map child is
        // read as the child's entry first ([`fragment_record`]).
        SyntaxErrorKind::InvalidListNotation { .. } if fragment => {
            crate::list_notation::anonymous_rest_in(
                error,
                crate::list_notation::GROUP_CHILD_ANONYMOUS_REST,
            )
        }
        SyntaxErrorKind::InvalidExpressionNotation { .. }
            if fragment && context == StateMacroContext::Expression =>
        {
            error
        }
        _ => invalid(span),
    })?;
    match term.tree() {
        TermTree::Reference(path) if path.get_ident().is_some() => {
            Ok((StateTerm::Group(term), None))
        }
        TermTree::Wildcard(_) if context == StateMacroContext::Pattern => {
            Ok((StateTerm::Group(term), None))
        }
        TermTree::Cell(_) => Ok((StateTerm::Group(term), None)),
        _ => {
            faults.carry(invalid(span), true)?;
            Ok((StateTerm::Term(term), Some(first)))
        }
    }
}

/// A `k::rewrite!` written as a cell's whole entry ([`rewritten_entry`]).
enum EntryRewrite {
    /// Its sides are contents, written without their cell's wrapper ([`REWRITTEN_ENTRY`]).
    Content(SyntaxError),
    /// A side writes an entry's mark, a `?` cell's presence or a wrapper.
    Marks(SyntaxError),
}

/// The refusal of a `k::rewrite!` written as a cell's whole entry, `cell: k::rewrite!(a => b)`,
/// whose sides are spelled as entries rather than contents: `None` or `Some(..)`, a `?` cell's
/// presence, or a wrapper `Cell(..)` or `KCell(..)`. A rewrite changes a content where it stands.
/// A side `None` against a side that is not would change whether the cell is present, which no
/// rewrite in place states: a rule states it by its subject and its result. `Some(..)` and a
/// wrapper are no content: they say that the cell is present and which cell holds the content,
/// so they stand outside the rewrite, around the content it changes (`Some(Cell(k::rewrite!(o =>
/// x)))`). Sides of any other spelling rewrite a content written outside its wrapper
/// ([`REWRITTEN_ENTRY`], [`EntryRewrite::Content`]). `None` for an entry that is no
/// `k::rewrite!`.
fn rewritten_entry(tokens: &TokenStream) -> Option<EntryRewrite> {
    let ("rewrite", payload) = qualified_macro_payload(tokens)
        .as_ref()
        .map(|(name, payload)| (name.as_str(), payload.clone()))?
    else {
        return None;
    };
    let (from, to) = crate::term::split_rewrite_arguments(&payload)?;
    let presence = |side: &TokenStream| {
        PresenceTokens::spelled(&side.clone().into_iter().collect::<Vec<_>>())
            .map(|(head, content)| (head.to_string(), content.is_some()))
    };
    let wrapper = |side: &TokenStream| {
        let syn::Expr::Call(call) = syn::parse2::<syn::Expr>(side.clone()).ok()? else {
            return None;
        };
        let syn::Expr::Path(path) = &*call.func else {
            return None;
        };
        let last = plain_path_last(&path.path)?.ident.to_string();
        matches!(last.as_str(), "Cell" | "KCell").then_some(last)
    };
    let absent = |side: &TokenStream| matches!(presence(side), Some((_, false)));
    let reason = match (absent(&from), absent(&to)) {
        (true, false) => {
            "a `k::rewrite!` from `None` changes whether the cell is present, and a rewrite changes a content where it stands, never whether its cell is there: a rule states that change by its subject and its result, `None` in its subject and `Some(Cell(..))` in its result"
        }
        (false, true) => {
            "a `k::rewrite!` to `None` changes whether the cell is present, and a rewrite changes a content where it stands, never whether its cell is there: a rule states that change by its subject and its result, `Some(Cell(..))` in its subject and `None` in its result"
        }
        _ => match [&from, &to]
            .into_iter()
            .find_map(|side| {
                presence(side)
                    .filter(|(_, present)| *present)
                    .map(|(head, _)| head)
                    .or_else(|| wrapper(side))
            })
            .as_deref()
        {
            None => REWRITTEN_ENTRY,
            Some("Some") => {
                "`Some(..)` on a side of a `k::rewrite!` names no content: it says that a `?` cell is present, and a rewrite changes a content where it stands; write `Some(..)` outside the rewrite, around the content it changes: `Some(Cell(k::rewrite!(a => b)))`"
            }
            Some("KCell") => {
                "`KCell(..)` on a side of a `k::rewrite!` names no content: it says which cell holds a content, and a rewrite changes a content where it stands; write `KCell(..)` outside the rewrite, around the content it changes: `KCell(k::rewrite!(a => b), ..)`"
            }
            _ => {
                "`Cell(..)` on a side of a `k::rewrite!` names no content: it says which cell holds a content, and a rewrite changes a content where it stands; write `Cell(..)` outside the rewrite, around the content it changes: `Cell(k::rewrite!(a => b))`"
            }
        },
    };
    let refusal = state_error("cells", reason, tokens.span());
    Some(if reason == REWRITTEN_ENTRY {
        EntryRewrite::Content(refusal)
    } else {
        EntryRewrite::Marks(refusal)
    })
}

/// The group record a whole nested-cell entry `k::fragment![Group { .. }]` is when one of its
/// children is written as that child cell's map entry, `child: k::map![..]` (ruling R4), or as
/// brackets ending in a remainder the signature does not declare ([`remainder_sequence`]): such a
/// child is the child's entry, which no term of a pattern spells, so the record's children are
/// read as an instance's are, each that child cell's entry. `None` for a
/// fragment whose children are all terms, which is read as the group's term, and for an update
/// `Group { .., ..base }`, which builds a term from its base.
fn fragment_record(
    tokens: &TokenStream,
    context: StateMacroContext,
) -> Result<Option<GroupRecord>, SyntaxError> {
    let Some(("fragment", payload)) = qualified_macro_payload(tokens)
        .as_ref()
        .map(|(name, payload)| (name.as_str(), payload.clone()))
    else {
        return Ok(None);
    };
    let trees = crate::parse::strip_trailing_comma(payload)
        .into_iter()
        .collect::<Vec<_>>();
    let Some((TokenTree::Group(body), owner)) = trees.split_last() else {
        return Ok(None);
    };
    if body.delimiter() != Delimiter::Brace {
        return Ok(None);
    }
    let Ok(owner) = syn::parse2::<Path>(owner.iter().cloned().collect()) else {
        return Ok(None);
    };
    let mut maps = false;
    let mut items = vec![Vec::new()];
    for tree in body.stream() {
        match (&tree, items.last_mut()) {
            (TokenTree::Punct(comma), _) if comma.as_char() == ',' => items.push(Vec::new()),
            (_, Some(item)) => item.push(tree),
            (_, None) => {}
        }
    }
    for item in &items {
        match item.as_slice() {
            [TokenTree::Punct(dot), TokenTree::Punct(_), _, ..] if dot.as_char() == '.' => {
                return Ok(None);
            }
            [TokenTree::Ident(_), TokenTree::Punct(colon), value @ ..]
                if colon.as_char() == ':' =>
            {
                let value = value.iter().cloned().collect::<TokenStream>();
                // A computation child's brackets ending in a remainder are that child's entry too
                // ([`remainder_sequence`]), which no term of the group spells.
                maps |= qualified_macro_payload(&value).is_some_and(|(name, _)| name == "map")
                    || remainder_sequence(&value, context).is_ok_and(|sequence| sequence.is_some());
            }
            _ => {}
        }
    }
    if !maps || !crate::path::is_plain_path(&owner) {
        return Ok(None);
    }
    let (fields, rest) = parse_instance_record(body, context, (false, false), &PartFaults::none())?;
    let open = match rest {
        InstanceRest::Exact => None,
        InstanceRest::Open(range) => Some(range),
        InstanceRest::Update { .. } => return Ok(None),
    };
    Ok(Some(GroupRecord::new(
        TokenRange::for_tokens(tokens)?,
        &owner,
        true,
        fields,
        open,
    )?))
}

/// The refusal of a result's whole entry of `cell` that is `_` or `name @ pattern`, which only a
/// pattern can hold: told as every route tells an entry root, naming the cell
/// ([`crate::cell_entries::Refusal::reason`]).
fn pattern_only_entry(tokens: &TokenStream, cell: &Ident) -> Option<SyntaxError> {
    use crate::cell_entries::{EntryKind, Refusal};
    use crate::cell_entry::EntryForm;
    use syn::ext::IdentExt;
    let reason = |refusal: Refusal| {
        refusal.reason(
            EntryForm::Cells,
            &cell.unraw().to_string(),
            &EntryKind::default(),
            None,
        )
    };
    if syn::parse2::<Token![_]>(tokens.clone()).is_ok() {
        return Some(SyntaxError::new(
            SyntaxErrorKind::UnsupportedTermExpression {
                reason: reason(Refusal::WildcardOutsidePattern).into(),
            },
            tokens.span(),
        ));
    }
    let alias = |input: ParseStream<'_>| -> syn::Result<()> {
        input.parse::<Ident>()?;
        input.parse::<Token![@]>()?;
        input.parse::<TokenStream>().map(drop)
    };
    syn::parse::Parser::parse2(alias, tokens.clone())
        .is_ok()
        .then(|| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidPatternAs {
                    reason: reason(Refusal::AliasOutsidePattern),
                },
                tokens.span(),
            )
        })
}

/// The name of a result's `[..name]` written as a leaf's whole content, `Cell([..name])`. A
/// leaf's content is a content root, where `..name` puts the named rest back (P6), so brackets
/// holding nothing else are the list `name` is: `Cell(name)`. Below the root, `[..name]` is a
/// term's notation, which has no element and is refused there.
fn named_rest_alone(tokens: &TokenStream, context: StateMacroContext) -> Option<TokenStream> {
    if context != StateMacroContext::Expression {
        return None;
    }
    let mut trees = tokens.clone().into_iter();
    let (Some(TokenTree::Group(group)), None) = (trees.next(), trees.next()) else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket {
        return None;
    }
    let rest = |input: ParseStream<'_>| -> syn::Result<Ident> {
        input.parse::<Token![..]>()?;
        input.parse::<Ident>()
    };
    syn::parse::Parser::parse2(rest, group.stream())
        .ok()
        .map(|name| quote!(#name))
}

/// Parses a leaf cell's content. `k!` and `map!` are read by their last
/// path segment, so `k::map![..]` is the same map as `map![..]`, as in
/// instance children and initializers; another qualified macro, such as
/// `k::fragment![..]` or a set literal `set![..]`, is an ordinary term.
fn parse_state_term(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<StateTerm, SyntaxError> {
    if let Some((name, payload)) = qualified_macro_payload(&tokens) {
        let invocation = || TokenRange::for_tokens(&tokens).map(Some);
        match name.as_str() {
            "k" => {
                return Ok(StateTerm::KSequence(parse_k_sequence(
                    payload,
                    context,
                    invocation()?,
                )?));
            }
            "map" => {
                return Ok(StateTerm::Map(
                    parse_map(payload, context, invocation()?)?.island_of(macro_path(&tokens)),
                ));
            }
            // A set literal has no reading of a cell's own: it is the term
            // its calls build, or a pattern holds them.
            "set" => {}
            _ if macro_payload(&tokens).is_some() => {
                return Err(state_error(
                    "cells",
                    "cell contents use only `k!` or `map!` state macros",
                    tokens.span(),
                ));
            }
            _ => {}
        }
    }
    Ok(StateTerm::Term(state_term_tokens(tokens, context)?))
}

fn parse_remainder(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
) -> Result<StateMacroRemainder, SyntaxError> {
    parse_remainder_kept(input, context, macro_name, SequenceRoot::Term)
}

/// A remainder, where `root` tells what an expression's anonymous `..` means: the subject's rest,
/// kept, at a `KCell(..)` entry's root ([`parse_cell_k_sequence`]), and nothing elsewhere.
fn parse_remainder_kept(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
    root: SequenceRoot,
) -> Result<StateMacroRemainder, SyntaxError> {
    let remainder = parse_remainder_tokens(input, context, macro_name, root)?;
    if input.peek(Token![|]) {
        // K's #Or combines terms; a remainder is a frame (KF-030).
        return Err(SyntaxError::new(
            crate::SyntaxErrorKind::InvalidPatternOr {
                reason: crate::term::PATTERN_OR_REMAINDER.to_owned(),
            },
            input.span(),
        ));
    }
    Ok(remainder)
}

fn parse_remainder_tokens(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
    root: SequenceRoot,
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
        // An initializer's value is the cell's whole initial content: it has no subject whose
        // rest an anonymous `..` could keep (P5), whatever the cell's kind.
        if root == SequenceRoot::Initializer {
            return Err(crate::parse::unsupported_initializer_body(
                INITIALIZER_REMAINDER,
                dots.span(),
            ));
        }
        if context == StateMacroContext::Expression && root == SequenceRoot::Term {
            if macro_name == "map" {
                return Err(crate::collection_literal::anonymous_map_rest(dots.spans[0]));
            }
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
    // `name @ ..` names the rest a pattern matched; a term built where nothing was matched
    // (a result, an initializer) has none to name, whatever the cell's kind (P4's placement).
    if context == StateMacroContext::Expression {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidPatternAs {
                reason: crate::positions::Class::AliasOutsidePattern
                    .summary()
                    .to_owned(),
            },
            binding.span(),
        ));
    }
    Ok(StateMacroRemainder::Bind {
        range: TokenRange::for_tokens(&quote!(#binding #dots))?,
        binding,
    })
}

/// Whether the next tokens are a remainder: `..`, `name @ ..`, or (in
/// expression position) `..name`. `name @ pattern` with any other pattern is
/// an alias item (KF-029).
fn starts_remainder(input: ParseStream<'_>) -> bool {
    if input.peek(Token![..]) {
        return true;
    }
    if !(input.peek(Ident) && input.peek2(Token![@])) {
        return false;
    }
    let fork = input.fork();
    fork.parse::<Ident>().is_ok() && fork.parse::<Token![@]>().is_ok() && fork.peek(Token![..])
}

/// Parses one state-island item: a pattern payload (PAT-1) in pattern
/// position, an expression otherwise.
fn parse_state_item(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => {
            let start = input.cursor();
            let fork = input.fork();
            let pattern = input
                .call(crate::term::parse_term_pattern)
                .map_err(|error| crate::notation::pattern_parse_error(&fork, error))?;
            let tokens = crate::term::tokens_between(start, input.cursor());
            let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
            TermExpression::from_pattern(pattern, tokens, signs)
        }
        StateMacroContext::Expression => {
            // Full expression syntax, so an item may be a record constructor
            // (`Tag { b: x }`), as any term may.
            let expression = input
                .call(crate::term::parse_term_expression)
                .map_err(SyntaxError::from)?;
            TermExpression::from_expression(expression)
        }
    }
}

/// Parses one complete state-island payload as a term in `context`.
fn state_term_tokens(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => TermExpression::parse_pattern_tokens(tokens),
        StateMacroContext::Expression => TermExpression::parse_tokens(tokens),
    }
}

/// A map item's key: in a pattern, the key a map is looked up by, which a
/// computed term may be ([`TermExpression::parse_key_pattern_tokens`]).
fn state_key_tokens(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => TermExpression::parse_key_pattern_tokens(tokens),
        StateMacroContext::Expression => TermExpression::parse_tokens(tokens),
    }
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
    parse_parenthesized_group(input).map(|(tokens, _)| tokens)
}

/// The contents of a parenthesized group and the range of its delimiters.
fn parse_parenthesized_group(input: ParseStream<'_>) -> syn::Result<(TokenStream, TokenRange)> {
    let content;
    let parentheses = parenthesized!(content in input);
    let range = TokenRange::new(parentheses.span.open(), parentheses.span.close());
    Ok((content.parse()?, range))
}

/// The base and the brackets of `base[key <- value]`. Brackets that end the
/// last entry's value of `k -> v` items (an index, `m[k]`) are no update.
fn split_bracket_update(tokens: &TokenStream) -> Option<(TokenStream, proc_macro2::Group)> {
    let mut trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let TokenTree::Group(group) = trees.pop()? else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket || trees.is_empty() {
        return None;
    }
    let inner = group.stream().into_iter().collect::<Vec<_>>();
    if has_arrow(&trees, '-', '>') && !has_arrow(&inner, '<', '-') {
        return None;
    }
    Some((trees.into_iter().collect(), group))
}

/// Whether `trees` hold the punctuation `first` joined to `second` (`->`,
/// `<-`); `i < -1`, a comparison with a negative operand, holds no `<-`.
fn has_arrow(trees: &[TokenTree], first: char, second: char) -> bool {
    trees.windows(2).any(|window| {
        matches!(&window[0], TokenTree::Punct(value)
            if value.as_char() == first && value.spacing() == proc_macro2::Spacing::Joint)
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == second)
    })
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
        TermExpression::parse_tokens(key)?,
        TermExpression::parse_tokens(value)?,
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

fn state_error(macro_name: &'static str, reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidStateMacro { macro_name, reason },
        span,
    )
}

#[cfg(test)]
mod keyed {
    use super::{
        CellsExpression, InstanceItem, InstanceList, KSequence, KSequenceNotation, MapBody,
        MapExpression, StateTerm,
    };
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SyntaxError, TokenRange};
    use krs_ir::ProvenanceKey;
    use proc_macro2::TokenStream;

    /// Records a shell's payload key with the range it is anchored at: the
    /// payload, or the invocation of an empty one.
    fn push_payload(
        nodes: &mut KeyedNodes,
        key: Option<&ProvenanceKey>,
        tokens: &TokenStream,
        invocation: Option<TokenRange>,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = super::payload_range(tokens, invocation)? {
            nodes.push(key, range);
        } else {
            assert!(key.is_none(), "a payload key without an anchor");
        }
        Ok(())
    }

    impl KSequence {
        /// Records the sequence's keyed nodes: the payload (or the
        /// invocation of an empty one), each item and its nodes, then the
        /// tail (its remainder, or the authored `.K`).
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            push_payload(
                nodes,
                self.payload_key.as_ref(),
                &self.tokens,
                self.invocation,
            )?;
            for item in &self.items {
                item.keyed_nodes(nodes)?;
            }
            if let Some(range) = self.tail.range() {
                nodes.push(self.tail_key.as_ref(), range);
            } else if self.notation == KSequenceNotation::DotK {
                nodes.push_tokens(self.tail_key.as_ref(), &self.tokens)?;
            } else {
                assert!(self.tail_key.is_none(), "a tail key without a tail");
            }
            Ok(())
        }
    }

    impl MapExpression {
        /// Records the map's keyed nodes: the payload (or the invocation of
        /// an empty one), each key and value (or update base, key and value)
        /// and their nodes, then the remainder.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            push_payload(
                nodes,
                self.payload_key.as_ref(),
                &self.tokens,
                self.invocation,
            )?;
            match &self.body {
                MapBody::Empty { .. } => {}
                MapBody::Items { items, remainder } => {
                    for item in items {
                        item.key.keyed_nodes(nodes)?;
                        item.value.keyed_nodes(nodes)?;
                    }
                    if let Some(range) = remainder.range() {
                        nodes.push(self.remainder_key.as_ref(), range);
                    }
                }
                MapBody::Update { base, key, value } => {
                    for term in [base, key, value] {
                        term.keyed_nodes(nodes)?;
                    }
                }
            }
            Ok(())
        }
    }

    impl StateTerm {
        /// Records the keyed nodes of the state: its term, sequence or map,
        /// the state under `Some(..)`, or each instance of a collection.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            match self {
                Self::Term(term) | Self::Group(term) => term.keyed_nodes(nodes),
                Self::KSequence(sequence) => sequence.keyed_nodes(nodes),
                Self::Map(map) => map.keyed_nodes(nodes),
                Self::Present(inner) => inner.keyed_nodes(nodes),
                Self::Absent(_) => Ok(()),
                Self::Instances(list) => list.keyed_nodes(nodes),
                Self::Record(record) => {
                    record.head.keyed_nodes(nodes)?;
                    for field in &record.fields {
                        nodes.push_tokens(field.name_key.as_ref(), &field.name)?;
                        field.value.keyed_nodes(nodes)?;
                    }
                    Ok(())
                }
            }
        }
    }

    impl InstanceItem {
        /// Records the instance's keyed nodes: the instance record, its head, then each
        /// field's name and value.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push(self.key.as_ref(), self.range);
            if let Some(head) = &self.head {
                head.keyed_nodes(nodes)?;
            }
            for field in &self.fields {
                nodes.push_tokens(field.name_key.as_ref(), &field.name)?;
                field.value.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }

    impl InstanceList {
        /// Records the collection's keyed nodes: its instances and its rest.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for item in self.instances() {
                item.keyed_nodes(nodes)?;
            }
            if let Some(range) = self.rest.range() {
                nodes.push(self.rest_key.as_ref(), range);
            }
            Ok(())
        }
    }

    impl CellsExpression {
        /// Records the configuration's keyed nodes: the payload, each
        /// entry's cell name and wrapper, then the remainder. The entries'
        /// values are keyed by the sentence that holds the configuration (a
        /// configuration standing alone does not key them: each value keeps
        /// the keys of its own parse).
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.payload_key.as_ref(), &self.tokens)?;
            for entry in &self.entries {
                nodes.push_tokens(entry.name_key.as_ref(), &entry.name)?;
                if let Some(wrapper) = entry.wrapper() {
                    nodes.push_tokens(entry.wrapper_key.as_ref(), wrapper)?;
                }
            }
            if let Some(range) = self.remainder.range() {
                nodes.push(self.remainder_key.as_ref(), range);
            }
            Ok(())
        }

        /// Records the keyed nodes of the entries' values, which the sentence
        /// that holds the configuration keyed.
        pub(crate) fn keyed_values(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for entry in &self.entries {
                entry.value.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod kept_rest {
    use super::{StateTerm, parse_cells_expression, parse_cells_pattern};
    use crate::{TermNode, TermTree};
    use quote::quote;

    /// The term of the expression's only entry.
    fn result_term(tokens: proc_macro2::TokenStream) -> crate::TermExpression {
        let cells = parse_cells_expression(tokens).expect("the result parses");
        match cells.entries()[0].value() {
            StateTerm::Term(term) => term.clone(),
            StateTerm::Present(inner) => match inner.as_ref() {
                StateTerm::Term(term) => term.clone(),
                other => panic!("not a leaf: {other:?}"),
            },
            other => panic!("not a leaf: {other:?}"),
        }
    }

    /// The tree at the end of the root's spine of list-notation levels.
    fn spine_end(tree: &TermTree) -> &TermTree {
        match tree {
            TermTree::Application(application) => match application.list_rest_argument() {
                Some(at) => spine_end(&application.arguments().positional().expect("levels")[at]),
                None => tree,
            },
            other => other,
        }
    }

    #[test]
    fn a_results_bare_rest_in_a_list_cells_brackets_is_its_unnamed_rest() {
        for tokens in [
            quote!(stack: Cell([y, ..])),
            quote!(stack: Cell([.., y])),
            quote!(stack: Cell([x, .., y])),
            quote!(stack: Some(Cell([y, ..]))),
            // Brackets holding only the rest are the rest: the root is its own spine's end.
            quote!(stack: Cell([..])),
            quote!(stack: Some(Cell([..]))),
        ] {
            let term = result_term(tokens.clone());
            assert!(term.keeps_root_rest(), "{tokens}");
            assert!(
                matches!(spine_end(term.tree()), TermTree::Wildcard(_)),
                "{tokens}: {:?}",
                term.tree()
            );
            assert!(
                !term
                    .nodes()
                    .iter()
                    .any(|node| matches!(node, TermNode::Reference(path) if path.is_ident(super::KEPT_REST_MARKER))),
                "{tokens}"
            );
            assert!(
                !term.spelling().contains(super::KEPT_REST_MARKER),
                "{tokens}: {}",
                term.spelling()
            );
        }
        // The lone rest's source is the brackets as authored.
        assert_eq!(result_term(quote!(stack: Cell([..]))).spelling(), "[..]");
        // A pattern's `..` already is the wildcard that ends its brackets.
        let cells = parse_cells_pattern(quote!(stack: Cell([x, ..]))).expect("the subject parses");
        let StateTerm::Term(term) = cells.entries()[0].value() else {
            panic!("a leaf");
        };
        assert!(!term.keeps_root_rest());
        assert!(matches!(spine_end(term.tree()), TermTree::Wildcard(_)));
    }

    #[test]
    fn a_bare_rest_elsewhere_is_read_as_written() {
        // Two rests and a nested list's rest are refused as the brackets are written.
        for tokens in [
            quote!(stack: Cell([x, .., y, ..])),
            quote!(stack: Cell([[x, ..], y])),
        ] {
            assert!(parse_cells_expression(tokens.clone()).is_err(), "{tokens}");
        }
        // A named rest is the rest it names, the marker's spelling too: an authored name, which
        // the sentence's bindings judge.
        for tokens in [
            quote!(stack: Cell([y, ..rest])),
            quote!(stack: Cell([x, ..__krs_kept_rest])),
        ] {
            let term = result_term(tokens.clone());
            assert!(!term.keeps_root_rest(), "{tokens}");
            assert!(
                !matches!(spine_end(term.tree()), TermTree::Wildcard(_)),
                "{tokens}"
            );
        }
    }
}

#[cfg(test)]
mod presences {
    use super::{
        RecordPresences, StateMacroContext, parse_cells_expression_judged_later,
        parse_cells_pattern_judged_later,
    };
    use quote::quote;

    /// Every `?` child's presence of a record is found, at any depth: a result reads the record
    /// without them, and a pattern reads each as the names it binds.
    #[test]
    fn a_records_presences_are_found_at_any_depth_and_read_by_side() {
        let value = quote!(k::fragment![crate::W {
            wg: k::fragment![crate::Gw {
                wo: Some(x),
                wp: None,
                ..
            }],
            wn: Some(y),
            ..
        }]);
        let pattern = RecordPresences::of(&value, StateMacroContext::Pattern).expect("found");
        assert_eq!(pattern.found.len(), 3);
        assert_eq!(
            pattern.read.to_string(),
            quote!(k::fragment![crate::W {
                wg: k::fragment![crate::Gw { wo: x, wp: _, .. }],
                wn: y,
                ..
            }])
            .to_string()
        );
        let result = RecordPresences::of(&value, StateMacroContext::Expression).expect("found");
        assert_eq!(
            result.read.to_string(),
            quote!(k::fragment![crate::W {
                wg: k::fragment![crate::Gw { .. }],
                ..
            }])
            .to_string()
        );
        assert!(RecordPresences::of(&quote!(Some(x)), StateMacroContext::Pattern).is_none());
        assert!(
            RecordPresences::of(&quote!(crate::G { a: x }), StateMacroContext::Pattern).is_none()
        );
        // A `?` group's present record is at the group's configuration position: the entry's
        // own `Some(..)` stays, its record's children are read as anywhere else.
        let present = quote!(Some(k::fragment![crate::H {
            hc: Some(y),
            hl: None,
            ..
        }]));
        let pattern = RecordPresences::of(&present, StateMacroContext::Pattern).expect("found");
        assert_eq!(pattern.found.len(), 2);
        assert_eq!(
            pattern.read.to_string(),
            quote!(Some(k::fragment![crate::H { hc: y, hl: _, .. }])).to_string()
        );
        let result = RecordPresences::of(&present, StateMacroContext::Expression).expect("found");
        assert_eq!(
            result.read.to_string(),
            quote!(Some(k::fragment![crate::H { .. }])).to_string()
        );
        assert!(
            RecordPresences::of(&quote!(Some(H { hc: y, .. })), StateMacroContext::Pattern)
                .is_none()
        );
    }

    /// A `cells!` entry's presence children wait for the entries' judgement on either side: the
    /// payload keeps the first one's refusal, and a subject keeps the names they bind.
    #[test]
    fn a_cells_entrys_presence_children_wait_on_either_side() {
        let subject = parse_cells_pattern_judged_later(
            quote!(ocell: k::fragment![crate::O { oo: Some(x), op: None, .. }], ..),
        )
        .expect("the subject's presences wait");
        assert!(
            subject
                .misplaced_tail()
                .is_some_and(|refusal| refusal.to_string().contains("field `oo`")),
            "{:?}",
            subject.misplaced_tail()
        );
        let result = parse_cells_expression_judged_later(
            quote!(ocell: k::fragment![crate::O { oo: Some(1), op: None, on: 0 }]),
            None,
        )
        .expect("the result's presences wait");
        assert!(
            result
                .misplaced_tail()
                .is_some_and(|refusal| refusal.to_string().contains("field `oo`"))
        );
    }
}
