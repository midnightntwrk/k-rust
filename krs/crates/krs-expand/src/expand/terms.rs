//! The symbolic term builder shared by rules, claims, and initializers.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use std::collections::HashMap;

use krs_ir::bytes_token;
use krs_ir::wire::{
    ItemSlot, TargetSlot, TypeSlot, WireApplicationReference, WireCellTermField, WireSortReference,
    WireTerm, WireTypeReference,
};
use krs_ir::{BuiltinSort, DescriptorApplicationHeadClass, ProductionFieldId, ProvenanceKey};
use krs_syntax::surface::path_text;
use krs_syntax::{
    ProvenanceRole, TermArguments, TermExpression, TermKeys, TermNode, TermSymbol, TermTree,
    TokenRange,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::{Attribute, Ident, Path};

use super::ledger::KeyLedger;
use super::nonce::rule_application_selector;
use super::tokens::{
    call_site_path, enum_variant_parts, is_bound_ident_path, spelling, variant_marker_function,
    wire_literal,
};

/// Resolved expressions retained by a factory's static host wire.
pub(super) struct WireSlots {
    facade: Path,
    types: SlotTable,
    items: SlotTable,
    targets: SlotTable,
}

#[derive(Default)]
struct SlotTable {
    expressions: Vec<TokenStream>,
    indices: HashMap<String, usize>,
}

impl SlotTable {
    fn insert(&mut self, key: String, expression: TokenStream) -> usize {
        if let Some(index) = self.indices.get(&key) {
            return *index;
        }
        let index = self.expressions.len();
        self.expressions.push(expression);
        self.indices.insert(key, index);
        index
    }
}

impl WireSlots {
    pub(super) fn new(facade: &Path) -> Self {
        Self {
            facade: facade.clone(),
            types: SlotTable::default(),
            items: SlotTable::default(),
            targets: SlotTable::default(),
        }
    }

    pub(super) fn type_slot(&mut self, expression: TokenStream) -> TypeSlot {
        TypeSlot(self.types.insert(expression.to_string(), expression))
    }

    pub(super) fn item_slot(&mut self, expression: &TokenStream) -> ItemSlot {
        ItemSlot(
            self.items
                .insert(expression.to_string(), expression.clone()),
        )
    }

    pub(super) fn nominal_target_slot(&mut self, expression: &TokenStream) -> TargetSlot {
        let facade = &self.facade;
        TargetSlot(self.targets.insert(
            format!("nominal:{expression}"),
            quote!(#facade::__KrsTargetSlot::Nominal(#expression)),
        ))
    }

    fn variant_slot(&mut self, owner: &TokenStream, marker: &TokenStream) -> TargetSlot {
        let facade = &self.facade;
        TargetSlot(self.targets.insert(
            format!("variant:{owner}:{marker}"),
            quote!(#facade::__KrsTargetSlot::Variant { owner: #owner, marker: #marker }),
        ))
    }

    pub(super) fn variant_slot_for_grammar(
        &mut self,
        owner: &TokenStream,
        marker: &TokenStream,
    ) -> TargetSlot {
        self.variant_slot(owner, marker)
    }

    fn target_slot_unique(&mut self, expression: &TokenStream) -> TargetSlot {
        // A lexical witness must remain at every authored occurrence: equal printed tokens may infer different Rust types in different contexts.
        let index = self.targets.expressions.len();
        let facade = &self.facade;
        self.targets
            .expressions
            .push(quote!(#facade::__KrsTargetSlot::Target(#expression)));
        TargetSlot(index)
    }

    pub(super) fn tokens(&self) -> TokenStream {
        let facade = &self.facade;
        let types = &self.types.expressions;
        let items = &self.items.expressions;
        let targets = &self.targets.expressions;
        quote!(#facade::__KrsSlots {
            types: &[#(#types),*],
            items: &[#(#items),*],
            targets: &[#(#targets),*],
        })
    }
}

/// The wire term of `k::rewrite!` (KF-011), whose node holds `node`.
pub(super) fn rewrite_wire(
    node: NodeKeys<'_>,
    from: WireTerm,
    to: Option<Box<WireTerm>>,
) -> crate::Result<WireTerm> {
    Ok(WireTerm::Rewrite {
        key: node.key(ProvenanceRole::RuleLocalRewrite)?,
        from_key: node.key(ProvenanceRole::RuleLocalRewriteFrom)?,
        to_key: node.key(ProvenanceRole::RuleLocalRewriteTo)?,
        from: Box::new(from),
        to,
    })
}

/// One term's tree with the nodes, paths and keys its sentence gave it.
#[derive(Clone, Copy)]
pub(super) struct KeyedTerm<'t> {
    tree: &'t TermTree,
    nodes: &'t [TermNode],
    paths: TermPaths<'t>,
    keys: &'t TermKeys,
}

impl<'t> KeyedTerm<'t> {
    /// A term payload.
    pub(super) fn of(term: &'t TermExpression) -> Self {
        Self {
            tree: term.tree(),
            nodes: term.nodes(),
            paths: TermPaths::Symbols(term.symbols()),
            keys: term.keys(),
        }
    }

    /// A rule subject: its pattern's nodes, paths and keys, and its tree.
    pub(super) fn pattern(pattern: &'t krs_syntax::RulePattern, tree: &'t TermTree) -> Self {
        let paths = match pattern {
            krs_syntax::RulePattern::Native { paths, .. } => TermPaths::Native(paths),
            krs_syntax::RulePattern::TermMacro { term, .. } => TermPaths::Symbols(term.symbols()),
        };
        Self {
            tree,
            nodes: pattern.nodes(),
            paths,
            keys: pattern.keys(),
        }
    }

    pub(super) const fn tree(self) -> &'t TermTree {
        self.tree
    }

    /// Reads the term's keys as expansion reaches its nodes; each key read
    /// is defined, or referred to, in `ledger`.
    pub(super) fn reader(self, ledger: &'t KeyLedger) -> TermKeyReader<'t> {
        let mut record_fields = Vec::new();
        self.tree.record_field_names_preorder(&mut record_fields);
        let mut wildcards = Vec::new();
        self.tree.wildcard_ranges_preorder(&mut wildcards);
        TermKeyReader {
            ledger,
            nodes: self.nodes,
            paths: self.paths,
            record_fields,
            wildcards,
            keys: self.keys,
            path: 0,
            record_field: 0,
            wildcard: 0,
            next: [0; NodeKind::COUNT],
        }
    }
}

/// The paths a term's symbol keys are indexed by.
#[derive(Clone, Copy)]
enum TermPaths<'t> {
    /// A term payload's symbols.
    Symbols(&'t [TermSymbol]),
    /// A native rule pattern's constructor and binding paths.
    Native(&'t [Path]),
}

impl<'t> TermPaths<'t> {
    fn get(self, index: usize) -> Option<&'t Path> {
        match self {
            Self::Symbols(symbols) => symbols.get(index).map(TermSymbol::path),
            Self::Native(paths) => paths.get(index),
        }
    }
}

/// The kinds of [`TermNode`], which a term pushes in its own preorder.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum NodeKind {
    ApplicationHead,
    Reference,
    Literal,
    IdToken,
    BytesToken,
    Anonymous,
    OrBool,
    Lexeme,
    SortTest,
    As,
    Or,
    Matches,
    MatchesWildcard,
    Let,
    LetWildcard,
    Closure,
    Rewrite,
}

impl NodeKind {
    /// The number of kinds: one past the last kind's index.
    const COUNT: usize = Self::Rewrite as usize + 1;

    const fn of(node: &TermNode) -> Self {
        match node {
            TermNode::ApplicationHead(_) => Self::ApplicationHead,
            TermNode::Reference(_) => Self::Reference,
            TermNode::Literal(_) => Self::Literal,
            TermNode::IdToken(_) => Self::IdToken,
            TermNode::BytesToken(_) => Self::BytesToken,
            TermNode::Anonymous { .. } => Self::Anonymous,
            TermNode::OrBool(_) => Self::OrBool,
            TermNode::Lexeme { .. } => Self::Lexeme,
            TermNode::SortTest { .. } => Self::SortTest,
            TermNode::As { .. } => Self::As,
            TermNode::Or(_) => Self::Or,
            TermNode::Matches(_) => Self::Matches,
            TermNode::MatchesWildcard(_) => Self::MatchesWildcard,
            TermNode::Let { .. } => Self::Let,
            TermNode::LetWildcard(_) => Self::LetWildcard,
            TermNode::Closure { .. } => Self::Closure,
            TermNode::Rewrite { .. } => Self::Rewrite,
        }
    }
}

/// Reads the keys of one term's nodes as expansion reaches them. A term
/// pushes its nodes, paths, record field names and wildcards each in its own
/// preorder, and expansion visits the nodes of each kind, and each of the
/// other lists, in that preorder, so the next one of a kind is the one
/// expansion has reached. Each read names the authored node expansion has
/// reached, and the reader checks that the entry it found starts at the
/// same token: a walker that visits nodes in another order fails with an
/// internal error instead of giving a wire node another node's key.
pub(super) struct TermKeyReader<'t> {
    ledger: &'t KeyLedger,
    nodes: &'t [TermNode],
    paths: TermPaths<'t>,
    record_fields: Vec<Ident>,
    wildcards: Vec<TokenRange>,
    keys: &'t TermKeys,
    path: usize,
    record_field: usize,
    wildcard: usize,
    next: [usize; NodeKind::COUNT],
}

impl<'t> TermKeyReader<'t> {
    /// The key of `path`, the next path: an application head's or a
    /// reference's, which the wire node's `path_key` defines.
    pub(super) fn path(&mut self, path: &Path) -> crate::Result<ProvenanceKey> {
        let at = TokenRange::for_tokens(path)?;
        let index = self.next_path(at)?;
        self.ledger
            .define_key(located_key(self.keys.symbol(index), at)?)
    }

    /// Passes `path`, the next path, which a `cells!` term keys not at all.
    pub(super) fn pass_path(&mut self, path: &Path) -> crate::Result<()> {
        self.next_path(TokenRange::for_tokens(path)?).map(drop)
    }

    fn next_path(&mut self, at: TokenRange) -> crate::Result<usize> {
        let index = self.path;
        self.path += 1;
        let found = self.paths.get(index).ok_or_else(|| misread(at))?;
        same_node(TokenRange::for_tokens(found)?, at)?;
        Ok(index)
    }

    /// The key of the record field `name`, the next record field name.
    pub(super) fn record_field(&mut self, name: &Ident) -> crate::Result<ProvenanceKey> {
        let at = TokenRange::for_tokens(name)?;
        let index = self.record_field;
        self.record_field += 1;
        let found = self.record_fields.get(index).ok_or_else(|| misread(at))?;
        same_node(TokenRange::for_tokens(found)?, at)?;
        self.ledger
            .define_key(located_key(self.keys.record_field(index), at)?)
    }

    /// The key of the `_` at `at`, the next `_` of a pattern (not of a
    /// `k::matches!` or `let` pattern, whose wildcards are nodes).
    pub(super) fn wildcard(&mut self, at: TokenRange) -> crate::Result<ProvenanceKey> {
        let index = self.wildcard;
        self.wildcard += 1;
        same_node(*self.wildcards.get(index).ok_or_else(|| misread(at))?, at)?;
        self.ledger
            .define_key(located_key(self.keys.wildcard(index), at)?)
    }

    /// The keys of the node of `kind` at `at`, the next node of `kind`. `at`
    /// is where the node's tokens start: its path, literal, a
    /// `k::anonymous!`'s spelling, a `k::lexeme!`'s text, a `name @ ..`'s
    /// name, or an island's range.
    pub(super) fn node(&mut self, kind: NodeKind, at: TokenRange) -> crate::Result<NodeKeys<'t>> {
        let next = &mut self.next[kind as usize];
        let index = self.nodes[(*next).min(self.nodes.len())..]
            .iter()
            .position(|node| NodeKind::of(node) == kind)
            .map(|offset| *next + offset);
        *next = index.map_or(self.nodes.len(), |index| index + 1);
        let index = index.ok_or_else(|| misread(at))?;
        same_node(self.nodes[index].range()?, at)?;
        Ok(NodeKeys {
            ledger: self.ledger,
            keys: self.keys,
            index,
            at,
        })
    }
}

/// Checks that `found`, the next entry of one of a term's lists, is the
/// authored node at `at` that expansion has reached: two nodes of one list
/// never start at the same token. Spans without a source location compare
/// equal, so the check can miss a misread there but never refuses a read.
fn same_node(found: TokenRange, at: TokenRange) -> crate::Result<()> {
    if found.first().start() == at.first().start() {
        Ok(())
    } else {
        Err(misread(at))
    }
}

/// Expansion reached the node at `at` while the next entry of its list is
/// another node, or none.
fn misread(at: TokenRange) -> ExpandError {
    ExpandError::at_range(
        expand::MISREAD_PROVENANCE_KEY,
        at,
        "expansion reached this node out of the order its sentence keyed the term's nodes in, so the provenance key it would read names another node",
    )
}

/// The key `read` of the node at `at`, which its sentence gave it at parse;
/// a node expansion reaches without one is a KRS bug.
fn located_key(read: Option<&ProvenanceKey>, at: TokenRange) -> crate::Result<ProvenanceKey> {
    read.cloned().ok_or_else(|| {
        ExpandError::at_range(
            expand::MISSING_PROVENANCE_KEY,
            at,
            "this node holds no provenance key from its sentence's parse",
        )
    })
}

/// The keys one term node holds, read by role.
#[derive(Clone, Copy)]
pub(super) struct NodeKeys<'t> {
    ledger: &'t KeyLedger,
    keys: &'t TermKeys,
    index: usize,
    at: TokenRange,
}

impl<'t> NodeKeys<'t> {
    /// The node's key of `role`, which the wire node that denotes the node
    /// (or that part of it) takes as its own.
    pub(super) fn key(self, role: ProvenanceRole) -> crate::Result<ProvenanceKey> {
        self.ledger
            .define_key(located_key(self.keys.node_key(self.index, role), self.at)?)
    }

    /// The node's keys of `role`, in allocation order, each read as the
    /// next is reached: the wire node of each takes it as its own.
    pub(super) fn keys(self, role: ProvenanceRole) -> NodeKeyList<'t> {
        NodeKeyList {
            ledger: self.ledger,
            keys: self
                .keys
                .node_keys(self.index, role)
                .collect::<Vec<_>>()
                .into_iter(),
        }
    }
}

/// The keys of one role that one term node holds, in allocation order.
pub(super) struct NodeKeyList<'t> {
    ledger: &'t KeyLedger,
    keys: std::vec::IntoIter<&'t ProvenanceKey>,
}

impl NodeKeyList<'_> {
    /// The next key, of the part of the node at `at`, which its wire node
    /// takes as its own.
    pub(super) fn next(&mut self, at: TokenRange) -> crate::Result<ProvenanceKey> {
        self.ledger.define_key(located_key(self.keys.next(), at)?)
    }
}

/// A sort reference keyed `node`, the key its node holds (which the caller
/// defined or referred to), resolved through the type-key helper `key`.
pub(super) fn wire_sort_reference(
    slots: &mut WireSlots,
    facade: &Path,
    node: ProvenanceKey,
    key: &Ident,
    authored_path: &str,
) -> WireSortReference {
    WireSortReference {
        key: node,
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#key))),
            authored_path: authored_path.to_owned(),
        },
    }
}

#[derive(Clone, Copy)]
pub(super) enum TermSide {
    Left,
    Right,
    Requires,
    Ensures,
    RuleEnsures,
}

/// A term-node role that a [`TermSide`] maps to its provenance role.
#[derive(Clone, Copy)]
pub(super) enum TermRole {
    ApplicationHead,
    Reference,
    Literal,
}

impl TermSide {
    pub(super) fn role(self, role: TermRole) -> ProvenanceRole {
        use ProvenanceRole as P;
        use TermRole as T;
        match (self, role) {
            (Self::Left, T::ApplicationHead) => P::RuleLeftApplicationHead,
            (Self::Left, T::Reference) => P::RuleLeftReference,
            (Self::Left, T::Literal) => P::RuleLeftLiteral,
            (Self::Right, T::ApplicationHead) => P::RuleRightApplicationHead,
            (Self::Right, T::Reference) => P::RuleRightReference,
            (Self::Right, T::Literal) => P::RuleRightLiteral,
            (Self::Requires, T::ApplicationHead) => P::RuleRequiresApplicationHead,
            (Self::Requires, T::Reference) => P::RuleRequiresReference,
            (Self::Requires, T::Literal) => P::RuleRequiresLiteral,
            (Self::Ensures, T::ApplicationHead) => P::ClaimEnsuresApplicationHead,
            (Self::Ensures, T::Reference) => P::ClaimEnsuresReference,
            (Self::Ensures, T::Literal) => P::ClaimEnsuresLiteral,
            (Self::RuleEnsures, T::ApplicationHead) => P::RuleEnsuresApplicationHead,
            (Self::RuleEnsures, T::Reference) => P::RuleEnsuresReference,
            (Self::RuleEnsures, T::Literal) => P::RuleEnsuresLiteral,
        }
    }
}

#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag selects one independent sentence-kind policy or records one mode or nesting context of the shared term builder."
)]
pub(super) struct TermBuilder<'a> {
    facade: &'a Path,
    /// The ledger of the descriptor whose terms this builder expands.
    pub(super) ledger: &'a KeyLedger,
    pub(super) nonce: u64,
    pub(super) cfg: &'a [Attribute],
    bindings: &'a [Ident],
    pub(super) next_key: usize,
    pub(super) key_functions: Vec<TokenStream>,
    associated_keys: bool,
    claim: bool,
    /// Whether this sentence kind admits turbofish instances (KF-027).
    application_instances: bool,
    /// Whether turbofish arguments use the readable spelling, the sort
    /// (`Choose::<Exp>`), rather than the reference spelling, the sort
    /// marker (`Choose::<dyn ExpSort>`).
    readable_instances: bool,
    /// The local binders (BIND-1) of the `k::matches!` pattern being
    /// expanded, or `None` outside one.
    local_binders: Option<Vec<Ident>>,
    /// The local binders of the `let` pattern being expanded, or `None`
    /// outside one.
    let_pattern_binders: Option<Vec<Ident>>,
    /// The local binders of the enclosing `let` statements and `ml::exists`
    /// closures, innermost last.
    let_scopes: Vec<Vec<Ident>>,
    lexical_rule_head: bool,
    /// The `use` items of a `k::equations!` table or a readable block: rustc
    /// resolves every one-segment path through them, as the author's Rust
    /// would with those items in scope. An import supplies only the names it
    /// imports, so `Frame { .. }` names a variant when an imported enum has
    /// one and the `#[k::cell]` struct otherwise (KF-016, KF-023), a crate
    /// function no import supplies resolves in the enclosing module, an
    /// explicit import shadows a glob, and a name two globs supply is
    /// rustc's ambiguity error where it is used.
    lexical_imports: Option<&'a [syn::ItemUse]>,
    pub(super) tooling_binding_references: Vec<Path>,
    /// Whether `k::rewrite!` is admitted: the subject of a single-body rule
    /// (KF-011).
    allow_rewrite: bool,
    /// Whether a `k::rewrite!` is being expanded.
    in_rewrite: bool,
}

impl<'a> TermBuilder<'a> {
    pub(super) fn new(
        facade: &'a Path,
        ledger: &'a KeyLedger,
        nonce: u64,
        cfg: &'a [Attribute],
        bindings: &'a [Ident],
    ) -> Self {
        Self {
            facade,
            ledger,
            nonce,
            cfg,
            bindings,
            next_key: 0,
            key_functions: Vec::new(),
            associated_keys: false,
            claim: false,
            application_instances: true,
            readable_instances: false,
            local_binders: None,
            let_pattern_binders: None,
            let_scopes: Vec::new(),
            lexical_rule_head: false,
            lexical_imports: None,
            tooling_binding_references: Vec::new(),
            allow_rewrite: false,
            in_rewrite: false,
        }
    }

    /// Admits `k::rewrite!` (KF-011) in the terms expanded next: `true` for
    /// the subject of a single-body rule.
    pub(super) fn set_rewrites(&mut self, allowed: bool) {
        self.allow_rewrite = allowed;
    }

    /// Starts one `k::rewrite!` (K's local `=>`, KF-011) on `side`;
    /// [`Self::leave_rewrite`] ends it.
    pub(super) fn enter_rewrite(
        &mut self,
        range: krs_syntax::TokenRange,
        left_side: bool,
    ) -> crate::Result<()> {
        if !self.allow_rewrite
            || !left_side
            || self.in_rewrite
            || self.in_matches_pattern()
            || self.in_let_pattern()
        {
            return Err(ExpandError::new(
                expand::LOCAL_REWRITE_OUTSIDE_SUBJECT,
                range.first(),
                "`k::rewrite!` (K's local =>) marks what changes inside the subject of a single-body `#[k::rule]` fn (one that returns `()`), or rewrites the hole of a `#[k::context]` fn; it cannot appear in a result, a condition, a pattern island, another rewrite, or another sentence",
            ));
        }
        self.in_rewrite = true;
        Ok(())
    }

    /// Ends the `k::rewrite!` [`Self::enter_rewrite`] started.
    pub(super) fn leave_rewrite(&mut self) {
        self.in_rewrite = false;
    }

    /// Expands `k::rewrite!(from => to)` (K's local `=>`, KF-011): the left
    /// side, then the right side, both keyed as the subject's.
    fn expand_rewrite(
        &mut self,
        range: krs_syntax::TokenRange,
        from: &TermTree,
        to: Option<&TermTree>,
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let node = keys.node(NodeKind::Rewrite, range)?;
        self.enter_rewrite(range, matches!(side, TermSide::Left))?;
        let from = self.expand_node(from, keys, side, slots);
        let to = match (from.is_ok(), to) {
            (true, Some(to)) => {
                Some(self.expand_node(to, keys, side, slots).map(Box::new)).transpose()
            }
            _ => Ok(None),
        };
        self.leave_rewrite();
        rewrite_wire(node, from?, to?)
    }

    pub(super) fn with_associated_keys(mut self) -> Self {
        self.associated_keys = true;
        self
    }

    pub(super) fn for_claim(mut self) -> Self {
        self.claim = true;
        self
    }

    /// Rejects turbofish instances on application heads (KF-027): an
    /// initializer builds a concrete value, whose syntax numbers no instance.
    pub(super) const fn without_application_instances(mut self) -> Self {
        self.application_instances = false;
        self
    }

    /// Expands turbofish arguments in the readable spelling, the sort
    /// (`Choose::<Exp>`), for a readable `k::rules!` clause; the reference
    /// spelling is the sort marker (`Choose::<dyn ExpSort>`).
    pub(super) const fn with_readable_instances(mut self) -> Self {
        self.readable_instances = true;
        self
    }

    /// Resolves every one-segment path through rustc with `imports` in
    /// scope (a `k::equations!` table or a readable block's `use` items).
    pub(super) const fn with_lexical_imports(
        mut self,
        imports: Option<&'a [syn::ItemUse]>,
    ) -> Self {
        self.lexical_imports = imports;
        self
    }

    pub(super) fn with_lexical_rule_head(mut self, enabled: bool) -> Self {
        self.lexical_rule_head = enabled;
        self
    }

    /// Whether `path` is a local binder of the `k::matches!` or `let`
    /// pattern being expanded, or of an enclosing `let` statement.
    fn is_local_binder(&self, path: &Path) -> bool {
        self.local_binders
            .iter()
            .chain(&self.let_pattern_binders)
            .chain(&self.let_scopes)
            .any(|binders| is_bound_ident_path(path, binders))
    }

    /// The names in scope at the current term: the sentence's bindings and
    /// the enclosing local binders.
    fn names_in_scope(&self) -> impl Iterator<Item = &Ident> {
        self.bindings.iter().chain(
            self.local_binders
                .iter()
                .chain(&self.let_pattern_binders)
                .chain(&self.let_scopes)
                .flatten(),
        )
    }

    /// Whether a `let` pattern is being expanded.
    const fn in_let_pattern(&self) -> bool {
        self.let_pattern_binders.is_some()
    }

    /// Expands one `let pattern = value;` statement and the rest of its
    /// block (K's `#let`, KF-032): the pattern, whose wildcards and local
    /// binders are admitted, then the value, then the body, in which the
    /// pattern's names are local binders.
    #[expect(
        clippy::too_many_arguments,
        reason = "One `let` statement has five parts besides the builder state."
    )]
    fn expand_let(
        &mut self,
        range: krs_syntax::TokenRange,
        pattern: &TermTree,
        sort: Option<&Path>,
        value: &TermTree,
        body: &TermTree,
        binders: &[Ident],
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let node = keys.node(NodeKind::Let, range)?;
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "a `let` block (K's #let) is a term; it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        // upstream k/claim-let-and-matches-unresolved (k-rust/claim-let-and-matches:
        // reviewed, not a request, since k-rust agrees with K).
        if self.claim {
            return Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "`let` blocks are not supported in claims: Java K's kprove and the native prover both reject K's #let in a claim; bind the value in the claim's subject instead",
            ));
        }
        let sort = sort
            .map(|sort| self.local_sort_reference(node.key(ProvenanceRole::LetSort)?, sort, slots))
            .transpose()?;
        self.let_pattern_binders = Some(binders.to_vec());
        let pattern = self.expand_node(pattern, keys, side, slots);
        self.let_pattern_binders = None;
        let pattern = pattern?;
        let value = self.expand_node(value, keys, side, slots)?;
        self.let_scopes.push(binders.to_vec());
        let body = self.expand_node(body, keys, side, slots);
        self.let_scopes.pop();
        Ok(WireTerm::Let {
            key: node.key(ProvenanceRole::Let)?,
            pattern: Box::new(pattern),
            sort,
            value: Box::new(value),
            body: Box::new(body?),
        })
    }

    /// The rustc-resolved sort of `let name: Sort = value;` or of the binder
    /// of `ml::exists(|name: Sort| ..)`, keyed `key`.
    fn local_sort_reference(
        &mut self,
        key: ProvenanceKey,
        sort: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<krs_ir::wire::WireSortReference> {
        let generated = call_site_path(sort)?;
        let key_fn = format_ident!("__krs_let_sort_{:016x}_{}", self.nonce, self.next_key);
        self.next_key += 1;
        let cfg = self.cfg;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        Ok(krs_ir::wire::WireSortReference {
            key,
            target: krs_ir::wire::WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                authored_path: spelling(sort),
            },
        })
    }

    /// Expands the closure `|binder: Sort| body` of an `ml::exists`
    /// (KF-039): its binder is local to the body, like a `let` binder.
    #[expect(
        clippy::too_many_arguments,
        reason = "One closure has three parts besides the builder state."
    )]
    fn expand_closure(
        &mut self,
        range: krs_syntax::TokenRange,
        binder: &Ident,
        sort: &Path,
        body: &TermTree,
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let node = keys.node(NodeKind::Closure, range)?;
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::ML_PLACEMENT,
                range.first(),
                "an `ml::exists` closure is a predicate (K's #Exists); it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        let sort =
            self.local_sort_reference(node.key(ProvenanceRole::MlBinderSort)?, sort, slots)?;
        self.let_scopes.push(vec![binder.clone()]);
        let body = self.expand_node(body, keys, side, slots);
        self.let_scopes.pop();
        Ok(WireTerm::Closure {
            key: node.key(ProvenanceRole::MlConnective)?,
            binder_key: node.key(ProvenanceRole::MlBinder)?,
            name: binder.unraw().to_string(),
            sort,
            body: Box::new(body?),
        })
    }

    /// Whether a `k::matches!` pattern is being expanded.
    const fn in_matches_pattern(&self) -> bool {
        self.local_binders.is_some()
    }

    /// Expands `k::matches!(subject, pattern)` (K's `:=K`, KF-031): the
    /// subject on `side`, then the pattern, whose wildcards, aliases,
    /// alternatives, and local binders are admitted.
    #[expect(
        clippy::too_many_arguments,
        reason = "One `k::matches!` has three parts besides the builder state."
    )]
    fn expand_matches(
        &mut self,
        range: krs_syntax::TokenRange,
        subject: &TermTree,
        pattern: &TermTree,
        binders: &[Ident],
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let node = keys.node(NodeKind::Matches, range)?;
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is a Bool test (K's :=K); it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        // upstream k/claim-let-and-matches-unresolved (k-rust/claim-let-and-matches:
        // reviewed, not a request, since k-rust agrees with K).
        if self.claim {
            return Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is not supported in claims: Java K's kprove and the native prover both reject K's :=K in a claim; match the shape in the claim's subject instead",
            ));
        }
        let subject = self.expand_node(subject, keys, side, slots)?;
        self.local_binders = Some(binders.to_vec());
        let pattern = self.expand_node(pattern, keys, side, slots);
        self.local_binders = None;
        Ok(WireTerm::Matches {
            key: node.key(ProvenanceRole::Matches)?,
            subject: Box::new(subject),
            pattern: Box::new(pattern?),
        })
    }

    /// Builds the literal term tree while retaining Rust-resolved heads in
    /// slots; each wire node takes the key its sentence gave the node.
    pub(super) fn expand_wire(
        &mut self,
        term: KeyedTerm<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        self.expand_node(term.tree(), &mut term.reader(self.ledger), side, slots)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive transport for the closed structured-term grammar."
    )]
    fn expand_node(
        &mut self,
        tree: &TermTree,
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        match tree {
            TermTree::Application(application) => {
                let path_key = keys.path(application.head())?;
                let node = keys.node(
                    NodeKind::ApplicationHead,
                    TokenRange::for_tokens(application.head())?,
                )?;
                let key = node.key(side.role(TermRole::ApplicationHead))?;
                let lexical = if self.lexical_imports.is_some() {
                    !application.is_notation()
                        && application.head().leading_colon.is_none()
                        && application.head().segments.len() == 1
                } else {
                    self.take_lexical_rule_head(application.head())
                };
                let authored_path = spelling(application.head());
                let target = if lexical {
                    let expression =
                        self.lexical_rule_application_target(&turbofish_path(application));
                    slots.target_slot_unique(&expression)
                } else {
                    self.application_wire_slot(
                        application.head(),
                        application.is_notation(),
                        slots,
                    )?
                };
                let instance = self.application_instance_wire(application, node, slots)?;
                let arguments = match application.arguments() {
                    TermArguments::Positional(values) => {
                        let mut arguments = Vec::new();
                        for value in values {
                            arguments.push(Box::new(self.expand_node(value, keys, side, slots)?));
                        }
                        krs_ir::Arguments::Positional(arguments)
                    }
                    TermArguments::Named(values) => {
                        let mut arguments = Vec::new();
                        for argument in values {
                            let field = ProductionFieldId::new(argument.name().to_string())
                                .expect("Rust field identifiers are valid production fields");
                            arguments.push(krs_ir::NamedTermArgument {
                                key: keys.record_field(argument.name())?,
                                field,
                                value: Box::new(self.expand_node(
                                    argument.value(),
                                    keys,
                                    side,
                                    slots,
                                )?),
                            });
                        }
                        krs_ir::Arguments::named(arguments)
                    }
                };
                let update = self.expand_record_update(application.update(), keys, side, slots)?;
                Ok(WireTerm::Application {
                    instance,
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: WireApplicationReference {
                        key,
                        target,
                        authored_path,
                    },
                    path_key,
                    arguments,
                    update,
                    open: application.is_open(),
                })
            }
            TermTree::Reference(path) => {
                let lexical = self.take_lexical_rule_head(path);
                let path_key = keys.path(path)?;
                let key = keys
                    .node(NodeKind::Reference, TokenRange::for_tokens(path)?)?
                    .key(side.role(TermRole::Reference))?;
                if self.is_local_binder(path) {
                    // A local binder has no Rust binding for tooling to use.
                    Ok(WireTerm::Variable {
                        key,
                        path_key,
                        name: binder_spelling(path),
                    })
                } else if is_bound_ident_path(path, self.bindings) {
                    self.tooling_binding_references.push(path.clone());
                    Ok(WireTerm::Variable {
                        key,
                        path_key,
                        name: binder_spelling(path),
                    })
                } else if let Some(name) = snake_case_bare_name(path) {
                    // A bare snake-case name is a binder by KRS's spelling
                    // rule, never a Rust item, so an unbound one is a free
                    // variable of the sentence, not a path for rustc.
                    Err(ExpandError::new(
                        expand::UNBOUND_NAME,
                        syn::spanned::Spanned::span(path),
                        format!(
                            "`{name}` is not bound in this sentence: a bare snake-case name is a binder, and only the pattern (or a `let`, `#[k::exists]`, or `#[k::fresh]`) introduces one{}",
                            did_you_mean(&name, self.names_in_scope())
                        ),
                    ))
                } else {
                    let authored_path = spelling(path);
                    let target = if lexical {
                        let expression = self.lexical_rule_application_target(path);
                        slots.target_slot_unique(&expression)
                    } else {
                        self.application_wire_slot(path, false, slots)?
                    };
                    Ok(WireTerm::Application {
                        instance: Vec::new(),
                        head_class: DescriptorApplicationHeadClass::BareReference,
                        reference: WireApplicationReference {
                            key,
                            target,
                            authored_path,
                        },
                        path_key,
                        arguments: krs_ir::Arguments::default(),
                        update: None,
                        open: false,
                    })
                }
            }
            TermTree::Literal(literal) => Ok(WireTerm::Literal {
                key: keys
                    .node(NodeKind::Literal, literal.range()?)?
                    .key(side.role(TermRole::Literal))?,
                literal: wire_literal(literal),
            }),
            TermTree::Wildcard(range) if self.in_let_pattern() => {
                let node = keys.node(NodeKind::LetWildcard, *range)?;
                Ok(WireTerm::Wildcard {
                    key: node.key(ProvenanceRole::LetWildcard)?,
                })
            }
            TermTree::Wildcard(range) if self.in_matches_pattern() => {
                let node = keys.node(NodeKind::MatchesWildcard, *range)?;
                Ok(WireTerm::Wildcard {
                    key: node.key(ProvenanceRole::MatchesWildcard)?,
                })
            }
            TermTree::Wildcard(range) => {
                // A result wildcard parses only for a desugar clause that
                // lists `_` in `unbound_variables` (KF-046).
                if !matches!(side, TermSide::Left | TermSide::Right) {
                    return Err(ExpandError::at_range(
                        expand::RULE_RESULT_WILDCARD,
                        *range,
                        "KRS rule results cannot contain wildcards",
                    ));
                }
                Ok(WireTerm::Wildcard {
                    key: keys.wildcard(*range)?,
                })
            }
            TermTree::IdToken { literal } => Ok(WireTerm::BuiltinToken {
                key: keys
                    .node(NodeKind::IdToken, TokenRange::for_tokens(literal)?)?
                    .key(ProvenanceRole::ClaimIdToken)?,
                sort: BuiltinSort::Id,
                value: literal.value(),
            }),
            TermTree::BytesToken { literal } => Ok(WireTerm::BuiltinToken {
                key: keys
                    .node(NodeKind::BytesToken, TokenRange::for_tokens(literal)?)?
                    .key(ProvenanceRole::ClaimBytesToken)?,
                sort: BuiltinSort::Bytes,
                value: bytes_token::encode(&literal.value()),
            }),
            // A readable claim's subject may hold `k::anonymous!`, as a
            // `cells!` claim's does.
            TermTree::Anonymous {
                sort,
                spelling: display_literal,
            } if self.claim && matches!(side, TermSide::Left) => {
                let node = keys.node(
                    NodeKind::Anonymous,
                    TokenRange::for_tokens(display_literal)?,
                )?;
                let key = node.key(ProvenanceRole::ClaimAnonymous)?;
                let sort_key = node.key(ProvenanceRole::ClaimAnonymousSort)?;
                // The `spelling` field is the spelling node, whose key the
                // anonymous term's ordinal pairs it with.
                node.key(ProvenanceRole::ClaimAnonymousSpelling)?;
                let path = call_site_path(sort)?;
                let key_fn = format_ident!(
                    "__krs_claim_anonymous_sort_{:016x}_{}",
                    self.nonce,
                    self.next_key,
                );
                self.next_key += 1;
                let cfg = self.cfg;
                self.key_functions.push(quote! {
                    #(#cfg)*
                    #[doc(hidden)]
                    fn #key_fn() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#path>()
                    }
                });
                let facade = self.facade;
                Ok(WireTerm::Anonymous {
                    key,
                    sort: WireSortReference {
                        key: sort_key,
                        target: WireTypeReference {
                            slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_fn))),
                            authored_path: spelling(sort),
                        },
                    },
                    spelling: display_literal.value(),
                })
            }
            TermTree::Anonymous { spelling, .. } => Err(ExpandError::new(
                expand::CLAIM_SUBJECT_ONLY_TERM,
                spelling.span(),
                "anonymous! is valid only in a claim subject",
            )),
            TermTree::Lexeme { sort, text } => {
                let node = keys.node(NodeKind::Lexeme, TokenRange::for_tokens(text)?)?;
                self.lexeme_wire(sort, text, node, slots)
            }
            TermTree::SortTest {
                range,
                kind,
                sort,
                operand,
            } => {
                let node = keys.node(NodeKind::SortTest, *range)?;
                let (key, sort) = self.sort_test_reference(sort, node, slots)?;
                Ok(WireTerm::SortTest {
                    key,
                    kind: *kind,
                    sort,
                    operand: Box::new(self.expand_node(operand, keys, side, slots)?),
                })
            }
            TermTree::As { binding, .. }
                if self.in_matches_pattern() && matches!(side, TermSide::Right) =>
            {
                Err(ExpandError::new(
                    expand::PATTERN_AS_OUTSIDE_LHS,
                    binding.span(),
                    format!(
                        "`{binding} @ pattern` in a `k::matches!` pattern is allowed only in requires and ensures conditions: K rejects #as in a rule's right-hand side"
                    ),
                ))
            }
            TermTree::As { binding, pattern } => {
                if !matches!(side, TermSide::Left) && !self.in_matches_pattern() {
                    return Err(ExpandError::new(
                        expand::PATTERN_AS_OUTSIDE_LHS,
                        binding.span(),
                        format!(
                            "`{binding} @ pattern` binds only on a left-hand side (K's #as is LHS-only)"
                        ),
                    ));
                }
                let node = keys.node(NodeKind::As, TokenRange::for_tokens(binding)?)?;
                let (key, binding_key) = self.take_pattern_as(binding, node)?;
                Ok(WireTerm::As {
                    key,
                    binding_key,
                    name: binding.unraw().to_string(),
                    pattern: Box::new(self.expand_node(pattern, keys, side, slots)?),
                })
            }
            TermTree::Or {
                range,
                alternatives,
            } => {
                if !matches!(side, TermSide::Left) && !self.in_matches_pattern() {
                    return Err(ExpandError::new(
                        expand::PATTERN_OR_OUTSIDE_LHS,
                        range.first(),
                        "`A | B` alternatives occur only on a left-hand side (K's #Or); for Bool disjunction use `||`, bool::or, or k::or_bool!",
                    ));
                }
                let node = keys.node(NodeKind::Or, *range)?;
                let key = Self::take_pattern_or(node)?;
                Ok(WireTerm::Or {
                    key,
                    alternatives: alternatives.try_map_ref(|alternative| {
                        self.expand_node(alternative, keys, side, slots)
                    })?,
                })
            }
            TermTree::Matches {
                range,
                subject,
                pattern,
                binders,
            } => self.expand_matches(*range, subject, pattern, binders, keys, side, slots),
            TermTree::Rewrite {
                range, from, to, ..
            } => self.expand_rewrite(*range, from, to.as_deref(), keys, side, slots),
            TermTree::Let {
                range,
                pattern,
                sort,
                value,
                body,
                binders,
            } => self.expand_let(
                *range,
                pattern,
                sort.as_ref(),
                value,
                body,
                binders,
                keys,
                side,
                slots,
            ),
            TermTree::Closure {
                range,
                binder,
                sort,
                body,
            } => self.expand_closure(*range, binder, sort, body, keys, side, slots),
            TermTree::OrBool { range, arguments } => {
                if !self.claim {
                    return Err(ExpandError::at_range(
                        expand::CLAIM_ONLY_TERM,
                        *range,
                        "or_bool! is currently claim-only",
                    ));
                }
                let key = keys
                    .node(NodeKind::OrBool, *range)?
                    .key(ProvenanceRole::ClaimOrBool)?;
                let arguments = arguments
                    .try_map_ref(|argument| self.expand_node(argument, keys, side, slots))?;
                Ok(WireTerm::OrBool { key, arguments })
            }
            TermTree::Cell(cell) => {
                // The cell's declaration reference is its path, which
                // carries no key of its own on the wire.
                keys.path(cell.owner())?;
                let key = keys
                    .node(
                        NodeKind::ApplicationHead,
                        TokenRange::for_tokens(cell.owner())?,
                    )?
                    .key(side.role(TermRole::ApplicationHead))?;
                let declaration = self.cell_declaration_reference(cell.owner(), slots)?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let name = ProductionFieldId::new(field.name().to_string())
                        .expect("Rust fields are valid cell-field identities");
                    fields.push(WireCellTermField {
                        key: keys.record_field(field.name())?,
                        field: name,
                        value: Box::new(self.expand_node(field.value(), keys, side, slots)?),
                    });
                }
                let update = self.expand_record_update(cell.update(), keys, side, slots)?;
                Ok(WireTerm::Cell {
                    key,
                    declaration,
                    fields,
                    open: cell.is_open(),
                    update,
                })
            }
        }
    }

    /// Expands the base `t` of a record update `Ctor { f: e, ..t }` (F5),
    /// after the record's fields, as a reference to the binder `t`. A name
    /// that binds nothing would resolve as a constructor, which has no
    /// fields to take, so it is rejected here.
    fn expand_record_update(
        &mut self,
        base: Option<&TermTree>,
        keys: &mut TermKeyReader<'_>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<Option<Box<WireTerm>>> {
        let Some(base) = base else {
            return Ok(None);
        };
        if let TermTree::Reference(path) = base
            && !self.is_local_binder(path)
            && !is_bound_ident_path(path, self.bindings)
        {
            return Err(ExpandError::new(
                expand::INVALID_RECORD_UPDATE,
                syn::spanned::Spanned::span(path),
                format!(
                    "`..{}` takes the other fields from a record the left-hand side matched, but `{}` is not a binder of this rule; bind the record with `{} @ Ctor {{ .. }}`",
                    spelling(path),
                    spelling(path),
                    spelling(path)
                ),
            ));
        }
        Ok(Some(Box::new(self.expand_node(base, keys, side, slots)?)))
    }

    /// The shell and alias keys of one `name @ pattern` (K's `#as`); a
    /// binding of the sentence is a reference tooling sees.
    pub(super) fn take_pattern_as(
        &mut self,
        binding: &Ident,
        node: NodeKeys<'_>,
    ) -> crate::Result<(ProvenanceKey, ProvenanceKey)> {
        if self.bindings.contains(binding) && !self.in_matches_pattern() {
            self.tooling_binding_references
                .push(Path::from(binding.clone()));
        }
        Ok((
            node.key(ProvenanceRole::PatternAs)?,
            node.key(ProvenanceRole::PatternAsBinding)?,
        ))
    }

    /// The shell key of one `A | B` or-pattern (K's `#Or`).
    pub(super) fn take_pattern_or(node: NodeKeys<'_>) -> crate::Result<ProvenanceKey> {
        node.key(ProvenanceRole::PatternOr)
    }

    /// Lowers `k::lexeme!(Sort, "text")` to a token term whose sort rustc
    /// resolves through a type key.
    pub(super) fn lexeme_wire(
        &mut self,
        sort: &Path,
        text: &syn::LitStr,
        node: NodeKeys<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let generated = call_site_path(sort)?;
        let key_fn = format_ident!("__krs_lexeme_sort_{:016x}_{}", self.nonce, self.next_key);
        self.next_key += 1;
        let cfg = self.cfg;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        Ok(WireTerm::Lexeme {
            key: node.key(ProvenanceRole::LexemeText)?,
            sort: krs_ir::wire::WireSortReference {
                key: node.key(ProvenanceRole::LexemeSort)?,
                target: krs_ir::wire::WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                    authored_path: spelling(sort),
                },
            },
            text: text.value(),
        })
    }

    /// The shell key of one `k::is!` or `k::project!` term, and its sort
    /// path lowered to a sort whose identity rustc resolves through a type
    /// key.
    pub(super) fn sort_test_reference(
        &mut self,
        sort: &Path,
        node: NodeKeys<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<(krs_ir::ProvenanceKey, krs_ir::wire::WireSortReference)> {
        let generated = call_site_path(sort)?;
        let key_fn = format_ident!("__krs_sort_test_sort_{:016x}_{}", self.nonce, self.next_key);
        self.next_key += 1;
        let cfg = self.cfg;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        Ok((
            node.key(ProvenanceRole::SortTest)?,
            krs_ir::wire::WireSortReference {
                key: node.key(ProvenanceRole::SortTestSort)?,
                target: krs_ir::wire::WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                    authored_path: spelling(sort),
                },
            },
        ))
    }

    pub(super) fn cell_declaration_reference(
        &mut self,
        authored: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTypeReference> {
        let generated = call_site_path(authored)?;
        let key_fn = format_ident!("__krs_rule_cell_{:016x}_{}", self.nonce, self.next_key);
        self.next_key += 1;
        let cfg = self.cfg;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        Ok(WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
            authored_path: spelling(authored),
        })
    }

    /// The target slot of an application head; `notation` marks the head of
    /// a call that notation denotes, the path of a builtin operation.
    pub(super) fn application_wire_slot(
        &mut self,
        authored: &Path,
        notation: bool,
        slots: &mut WireSlots,
    ) -> crate::Result<TargetSlot> {
        check_ml_item(authored)?;
        let (owner, variant) = if notation {
            // Notation names the facade's builtin operation, which resolves
            // whether or not the author imported its module.
            let facade = self.facade;
            (syn::parse_quote!(#facade::builtin::#authored), None)
        } else if let Some((owner, variant)) = enum_variant_parts(authored) {
            (owner, Some(variant))
        } else {
            (authored.clone(), None)
        };

        // The type-key helper and authored Rust path remain visible to rustc.
        // Its resolved key enters the runtime payload slot.
        let key_fn = format_ident!(
            "__krs_rule_application_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let cfg = self.cfg;
        // A table's `use` items are in scope for its rows, so a qualified
        // path whose first segment one of them introduces, such as
        // `Info::StructType` under `use MirTypeInfo as Info;`, resolves
        // through them as in the author's Rust.
        let imports = self.lexical_import_items();
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                #imports
                ::core::any::TypeId::of::<#owner>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        let owner_key = quote!(#facade::HostTypeKey(#key_reference));
        Ok(if let Some(variant) = variant {
            let marker = variant_marker_function(&variant);
            let marker_key = if imports.is_empty() {
                quote!(#facade::HostTypeKey(#owner::#marker))
            } else {
                quote!(#facade::HostTypeKey({ #imports #owner::#marker }))
            };
            slots.variant_slot(&owner_key, &marker_key)
        } else {
            slots.nominal_target_slot(&owner_key)
        })
    }

    /// Lowers the turbofish of a parametric production head (KF-027) to one
    /// sort reference per marker, keyed `application_instance` across the
    /// sentence. A plain marker path is keyed by its own type (`Int`, or a
    /// readable sort alias); a `dyn ExpSort` marker by `Term<dyn ExpSort>`,
    /// the type of the sort's B2 alias. A generated check makes rustc resolve
    /// `Choose<k::builtin::Int>` itself, so an unknown marker or a wrong arity
    /// is a rustc error at the authored turbofish.
    pub(super) fn application_instance_wire(
        &mut self,
        application: &krs_syntax::TermApplication,
        node: NodeKeys<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<Vec<krs_ir::wire::WireSortReference>> {
        let mut instance_keys = node.keys(ProvenanceRole::ApplicationInstance);
        let instance = application.instance();
        let Some(first) = instance.first() else {
            return Ok(Vec::new());
        };
        if !self.application_instances {
            return Err(ExpandError::new(
                expand::TURBOFISH_PLACEMENT,
                syn::spanned::Spanned::span(first.ty()),
                "a turbofish instance is written only in a rule, equation, simplification, alias, desugar, or claim, not in an initializer",
            ));
        }
        let cfg = self.cfg;
        let facade = self.facade;
        let owner = application.head();
        let types = instance.iter().map(krs_syntax::TermSort::ty);
        let check_fn = format_ident!(
            "__krs_rule_instance_check_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            #[allow(dead_code)]
            fn #check_fn() {
                let _: ::core::marker::PhantomData<#owner<#(#types),*>>;
            }
        });
        let mut references = Vec::with_capacity(instance.len());
        for (index, sort) in instance.iter().enumerate() {
            if self.readable_instances && sort.is_dynamic() {
                return Err(readable_marker_error(application, index));
            }
            if !self.readable_instances && !sort.is_dynamic() {
                self.reference_marker_check(application, index);
            }
            let generated = call_site_path(sort.sort())?;
            let generated = if sort.is_dynamic() {
                quote!(#facade::Term<dyn #generated>)
            } else {
                quote!(#generated)
            };
            let key_fn = format_ident!("__krs_rule_instance_{:016x}_{}", self.nonce, self.next_key);
            self.next_key += 1;
            self.key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#generated>()
                }
            });
            let key_reference = if self.associated_keys {
                quote!(Self::#key_fn)
            } else {
                quote!(#key_fn)
            };
            references.push(krs_ir::wire::WireSortReference {
                key: instance_keys.next(TokenRange::for_tokens(sort.ty())?)?,
                target: krs_ir::wire::WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                    authored_path: quote::ToTokens::to_token_stream(sort.ty()).to_string(),
                },
            });
        }
        Ok(references)
    }

    /// Makes rustc reject a reference-layer turbofish argument that is a
    /// sort's `Term<..>` alias (`Choose::<Exp>`, which rustc reads as
    /// `Term<Term<..>>` fields) rather than its sort marker
    /// (`Choose::<dyn ExpSort>`), with a did-you-mean (KF-027). A builtin
    /// marker or a closed sort's own type passes.
    fn reference_marker_check(&mut self, application: &krs_syntax::TermApplication, index: usize) {
        let sort = &application.instance()[index];
        let alias = path_text(sort.sort());
        let marker = format!("dyn {alias}Sort");
        let suggestion = turbofish_text(application, index, &marker);
        let message = format!(
            "a turbofish in reference code names the sort marker, the type inside `k::Term<..>`, not the alias `{alias}`: write `{suggestion}`"
        );
        let label = format!("`{alias}` is a `k::Term<..>` alias; did you mean `{marker}`?");
        let cfg = self.cfg;
        let facade = self.facade;
        let ty = sort.ty();
        let check_fn = format_ident!(
            "__krs_rule_instance_marker_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let span = syn::spanned::Spanned::span(ty);
        let call = quote::quote_spanned! {span=>
            __krs_require_sort_marker(
                (&&#facade::__KrsTurbofishProbe::<#ty>::new()).__krs_turbofish_kind(),
            )
        };
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            #[allow(dead_code)]
            fn #check_fn() {
                #[diagnostic::on_unimplemented(message = #message, label = #label)]
                trait __KrsTurbofishSortMarker {}
                impl __KrsTurbofishSortMarker for #facade::__KrsTurbofishMarker {}
                fn __krs_require_sort_marker<T: __KrsTurbofishSortMarker>(_: T) {}
                #[allow(unused_imports)]
                use #facade::{__KrsTurbofishAliasKind as _, __KrsTurbofishMarkerKind as _};
                #call;
            }
        });
    }

    /// The `use` items of a `k::equations!` table, to open a block or fn
    /// body that resolves a row's paths; empty outside a table.
    fn lexical_import_items(&self) -> TokenStream {
        let items = self
            .lexical_imports
            .unwrap_or_default()
            .iter()
            .map(|item| quote!(#[allow(unused_imports, clippy::enum_glob_use)] #item));
        quote!(#(#items)*)
    }

    fn take_lexical_rule_head(&mut self, path: &Path) -> bool {
        if self.lexical_imports.is_some() {
            return path.leading_colon.is_none() && path.segments.len() == 1;
        }
        let enabled = ::core::mem::take(&mut self.lexical_rule_head);
        enabled && path.leading_colon.is_none() && path.segments.len() == 1
    }

    fn lexical_rule_application_target(&self, authored: &Path) -> TokenStream {
        let path = authored.clone();
        let ident = authored
            .segments
            .first()
            .expect("one-segment lexical paths have one identifier");
        let selector = rule_application_selector(&ident.ident);
        let authored_spelling = spelling(authored);
        // `A { .. }` matches a unit, tuple, or record constructor alike, so
        // `A()` names a unit variant as `Register::A()` does. A bare `A`,
        // such as a named constant, is written the same way: in a Rust
        // pattern a bare name that resolves to nothing would bind, while
        // `A { .. }` makes rustc report the unresolved name.
        let pattern = quote!(#path { .. });
        let facade = self.facade;
        // The path is resolved with the block's or table's `use` items in
        // scope, so `Frame` names the variant when an imported enum has one
        // and the item in scope otherwise, as in the author's Rust.
        let imports = self.lexical_import_items();
        quote! {{
            #imports
            let __krs_rule_application_witness: ::core::option::Option<_> =
                ::core::option::Option::None;
            if let ::core::option::Option::Some(#pattern) =
                &__krs_rule_application_witness
            {}
            #facade::__krs_resolve_rule_application::<_, #selector>(
                &__krs_rule_application_witness,
                #authored_spelling,
            )
        }}
    }
}

/// Rejects a sort marker (`dyn ExpSort`) as a turbofish argument of a
/// readable clause, which names the sort itself (`Choose::<Exp>`, KF-027).
fn readable_marker_error(application: &krs_syntax::TermApplication, index: usize) -> ExpandError {
    let sort = &application.instance()[index];
    let marker = format!("dyn {}", path_text(sort.sort()));
    let mut alias = sort.sort().clone();
    let stripped = alias.segments.last_mut().and_then(|last| {
        let name = last.ident.to_string();
        let stem = name.strip_suffix("Sort").filter(|stem| !stem.is_empty())?;
        last.ident = Ident::new(stem, last.ident.span());
        Some(())
    });
    let message = if stripped.is_some() {
        let suggestion = turbofish_text(application, index, &path_text(&alias));
        format!(
            "a readable clause names the sort in a turbofish, not its marker `{marker}`: write `{suggestion}`; `krs expand` renders the marker"
        )
    } else {
        format!(
            "a readable clause names the sort in a turbofish, not the sort marker `{marker}`: write the sort's name, such as `Choose::<Exp>`; `krs expand` renders the marker"
        )
    };
    ExpandError::new(
        expand::TURBOFISH_SPELLING,
        syn::spanned::Spanned::span(sort.ty()),
        message,
    )
}

/// The text of `application`'s head and turbofish with the argument at
/// `index` replaced by `replacement`, for a did-you-mean.
fn turbofish_text(
    application: &krs_syntax::TermApplication,
    index: usize,
    replacement: &str,
) -> String {
    let arguments = application
        .instance()
        .iter()
        .enumerate()
        .map(|(position, sort)| {
            if position == index {
                replacement.to_owned()
            } else if sort.is_dynamic() {
                format!("dyn {}", path_text(sort.sort()))
            } else {
                path_text(sort.sort())
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}::<{arguments}>", path_text(application.head()))
}

/// The head of `application` with its turbofish restored, for a readable
/// rule head whose owning type rustc infers from a witness pattern (KF-027).
fn turbofish_path(application: &krs_syntax::TermApplication) -> Path {
    let mut path = application.head().clone();
    if application.instance().is_empty() {
        return path;
    }
    let types = application.instance().iter().map(krs_syntax::TermSort::ty);
    if let Some(last) = path.segments.last_mut() {
        last.arguments = syn::PathArguments::AngleBracketed(syn::parse_quote!(::<#(#types),*>));
    }
    path
}

/// The `k::ml` connectives (KF-039), the closed set an `ml::` path names.
const ML_CONNECTIVES: [&str; 9] = [
    "top", "bottom", "not", "and", "or", "implies", "equals", "ceil", "exists",
];

/// Rejects a term head `ml::name` outside the closed set of matching-logic
/// connectives, suggesting the closest one. Only a lowercase last segment
/// after a `ml` segment is checked: object constructors are types, and the
/// connectives are the only lowercase `ml` items.
fn check_ml_item(path: &Path) -> crate::Result<()> {
    let mut segments = path.segments.iter().rev();
    let (Some(last), Some(module)) = (segments.next(), segments.next()) else {
        return Ok(());
    };
    let name = last.ident.to_string();
    if module.ident != "ml"
        || !name.starts_with(|first: char| first.is_ascii_lowercase())
        || ML_CONNECTIVES.contains(&name.as_str())
    {
        return Ok(());
    }
    let closest = ML_CONNECTIVES
        .iter()
        .min_by_key(|candidate| edit_distance(&name, candidate))
        .filter(|candidate| edit_distance(&name, candidate) <= name.len().max(2) / 2)
        .map(|candidate| format!(" Did you mean `ml::{candidate}`?"))
        .unwrap_or_default();
    Err(ExpandError::new(
        expand::UNKNOWN_ML_ITEM,
        last.ident.span(),
        format!(
            "`ml::{name}` is not a matching-logic connective.{closest} The connectives are ml::{}.",
            ML_CONNECTIVES.join(", ml::")
        ),
    ))
}

/// The name of a bare snake-case path: one unqualified segment without
/// arguments whose first character after any leading underscores is
/// lowercase (`zz`, `_tmp`, `r#type`). KRS binders are spelled this way and
/// Rust items are not, so outside a pattern such a name uses a binder.
pub(super) fn snake_case_bare_name(path: &Path) -> Option<String> {
    let name = path.get_ident()?.unraw().to_string();
    name.trim_start_matches('_')
        .starts_with(|first: char| first.is_lowercase())
        .then_some(name)
}

/// "; did you mean `x`?" for the in-scope name closest to `name`, within an
/// edit distance (a swap of two adjacent letters counting as one edit) of a
/// third of its length, at least one, or nothing.
pub(super) fn did_you_mean<'a>(name: &str, candidates: impl Iterator<Item = &'a Ident>) -> String {
    let bound = (name.len() / 3).max(1);
    candidates
        .map(|candidate| candidate.unraw().to_string())
        .filter(|candidate| candidate != name)
        .map(|candidate| (transposition_distance(name, &candidate), candidate))
        .filter(|(distance, _)| *distance <= bound)
        .min()
        .map(|(_, candidate)| format!("; did you mean `{candidate}`?"))
        .unwrap_or_default()
}

/// The edit distance between two ASCII identifiers that counts insertions,
/// deletions, substitutions, and swaps of two adjacent letters (the
/// restricted Damerau-Levenshtein distance), so `valeu` is one edit from
/// `value`.
fn transposition_distance(left: &str, right: &str) -> usize {
    let (left, right) = (left.as_bytes(), right.as_bytes());
    let mut rows = vec![(0..=right.len()).collect::<Vec<_>>()];
    for (row, left_byte) in left.iter().enumerate() {
        let mut current = vec![row + 1];
        for (column, right_byte) in right.iter().enumerate() {
            let previous = &rows[row];
            let mut distance = (previous[column] + usize::from(left_byte != right_byte))
                .min(previous[column + 1] + 1)
                .min(current[column] + 1);
            if row > 0
                && column > 0
                && *left_byte == right[column - 1]
                && left[row - 1] == *right_byte
            {
                distance = distance.min(rows[row - 1][column - 1] + 1);
            }
            current.push(distance);
        }
        rows.push(current);
    }
    rows[left.len()][right.len()]
}

/// The Levenshtein distance between two ASCII identifiers.
fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.as_bytes();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (row, left_byte) in left.bytes().enumerate() {
        let mut current = vec![row + 1];
        for (column, right_byte) in right.iter().enumerate() {
            let substitution = previous[column] + usize::from(left_byte != *right_byte);
            current.push(
                substitution
                    .min(previous[column + 1] + 1)
                    .min(current[column] + 1),
            );
        }
        previous = current;
    }
    previous[right.len()]
}

/// A binder's name as a rule binding: its identifier without `r#`, as Rust
/// names it, so `r#type` and `type` are one binding.
pub(super) fn binder_spelling(path: &Path) -> String {
    match path.get_ident() {
        Some(ident) => ident.unraw().to_string(),
        None => spelling(path),
    }
}

/// Where [`production_sort_arguments`] emits each element type's `TypeId`
/// helper and wire reference.
pub(super) struct SortArgumentSink<'a> {
    pub(super) facade: &'a syn::Path,
    /// The helper names' prefix; each helper is `{prefix}_{ordinal}`.
    pub(super) prefix: String,
    pub(super) cfg: &'a [syn::Attribute],
    pub(super) helpers: &'a mut Vec<TokenStream>,
    pub(super) slots: &'a mut WireSlots,
    /// The ledger of the descriptor whose production this is.
    pub(super) ledger: &'a KeyLedger,
    /// The number of the next helper.
    pub(super) ordinal: u32,
}

/// The wire tree of a production's typed collection element types (a
/// field's or a function result's): one reference per element type, keyed
/// by its path, with one `TypeId` helper per element type numbered in
/// preorder.
pub(super) fn production_sort_arguments(
    arguments: &[krs_syntax::SortArgument],
    sink: &mut SortArgumentSink<'_>,
) -> crate::Result<Vec<krs_ir::wire::WireConstructorSortArgument>> {
    let mut output = Vec::with_capacity(arguments.len());
    for argument in arguments {
        let facade = sink.facade;
        let cfg = sink.cfg;
        let generated = super::tokens::call_site_path(&argument.path)?;
        let ty = super::tokens::sort_type_tokens(facade, &generated, argument.dynamic);
        let key = quote::format_ident!("{}_{}", sink.prefix, sink.ordinal);
        sink.helpers.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        let sort = krs_ir::wire::WireSortReference {
            key: sink.ledger.define(argument.key())?,
            target: krs_ir::wire::WireTypeReference {
                slot: sink.slots.type_slot(quote!(#facade::HostTypeKey(#key))),
                authored_path: super::tokens::spelling(&argument.path),
            },
        };
        sink.ordinal = sink.ordinal.checked_add(1).ok_or_else(|| {
            crate::ExpandError::new(
                krs_diagnostic::codes::expand::DESCRIPTOR_CAPACITY,
                syn::spanned::Spanned::span(&argument.path),
                "too many collection element types",
            )
        })?;
        output.push(krs_ir::wire::WireConstructorSortArgument {
            sort,
            arguments: production_sort_arguments(&argument.arguments, sink)?,
        });
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::{KeyedTerm, NodeKind};
    use crate::expand::ledger::KeyLedger;
    use krs_diagnostic::codes::expand;
    use krs_syntax::{TermArguments, TermExpression, TermTree, TokenRange};

    fn term(source: &str) -> TermExpression {
        TermExpression::from_expression(syn::parse_str(source).unwrap()).unwrap()
    }

    fn at(tokens: &impl quote::ToTokens) -> TokenRange {
        TokenRange::for_tokens(tokens).unwrap()
    }

    fn code(error: &crate::ExpandError) -> krs_diagnostic::Code {
        error.diagnostics().next().unwrap().code.clone()
    }

    /// A walker that expands `k::matches!(f(x), g(y))`'s pattern before its
    /// subject reaches `g` while the next application head the sentence
    /// keyed is `f`: the read fails instead of giving `g` the key anchored
    /// at `f`. In the keyed order, the same reads pass.
    #[test]
    fn a_permuted_read_names_another_node_and_fails() {
        let term = term("k::matches!(f(x), g(y))");
        let ledger = KeyLedger::new(&term.provenance().unwrap(), &[]);
        let TermTree::Matches {
            range,
            subject,
            pattern,
            ..
        } = term.tree()
        else {
            panic!("a `k::matches!` term");
        };
        let (TermTree::Application(f), TermTree::Application(g)) = (&**subject, &**pattern) else {
            panic!("two applications");
        };

        let mut keys = KeyedTerm::of(&term).reader(&ledger);
        let misread = keys
            .node(NodeKind::ApplicationHead, at(g.head()))
            .err()
            .expect("`g` is not the next application head");
        assert_eq!(code(&misread), expand::MISREAD_PROVENANCE_KEY);
        let mut keys = KeyedTerm::of(&term).reader(&ledger);
        let misread = keys.pass_path(g.head()).unwrap_err();
        assert_eq!(code(&misread), expand::MISREAD_PROVENANCE_KEY);

        let mut keys = KeyedTerm::of(&term).reader(&ledger);
        assert!(keys.node(NodeKind::Matches, *range).is_ok());
        for application in [f, g] {
            assert!(keys.pass_path(application.head()).is_ok());
            assert!(
                keys.node(NodeKind::ApplicationHead, at(application.head()))
                    .is_ok()
            );
            let TermArguments::Positional(arguments) = application.arguments() else {
                panic!("positional arguments");
            };
            let TermTree::Reference(argument) = &arguments[0] else {
                panic!("a reference");
            };
            assert!(keys.pass_path(argument).is_ok());
        }
        // Every node of the kind has been read.
        let misread = keys
            .node(NodeKind::ApplicationHead, at(g.head()))
            .err()
            .expect("no application head is left");
        assert_eq!(code(&misread), expand::MISREAD_PROVENANCE_KEY);
    }

    /// Record field names are read in the order the sentence keyed them.
    #[test]
    fn a_permuted_record_field_read_fails() {
        let term = term("F { a: x, b: y }");
        let ledger = KeyLedger::new(&term.provenance().unwrap(), &[]);
        let TermTree::Application(record) = term.tree() else {
            panic!("a record");
        };
        let TermArguments::Named(fields) = record.arguments() else {
            panic!("named fields");
        };
        let mut keys = KeyedTerm::of(&term).reader(&ledger);
        let misread = keys.record_field(fields[1].name()).unwrap_err();
        assert_eq!(code(&misread), expand::MISREAD_PROVENANCE_KEY);
    }
}
