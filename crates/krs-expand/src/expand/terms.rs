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
use krs_syntax::{ProvenanceRole, TermArguments, TermTree};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Attribute, Ident, Path};

use super::nonce::rule_application_selector;
use super::tokens::{
    call_site_path, enum_variant_parts, is_bound_ident_path, spelling, take_counter,
    variant_marker_function, wire_literal,
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

/// The wire term of `k::rewrite!` number `ordinal` (KF-011).
pub(super) fn rewrite_wire(ordinal: u32, from: WireTerm, to: Option<Box<WireTerm>>) -> WireTerm {
    WireTerm::Rewrite {
        key: wire_key(ProvenanceRole::RuleLocalRewrite, ordinal),
        from_key: wire_key(ProvenanceRole::RuleLocalRewriteFrom, ordinal),
        to_key: wire_key(ProvenanceRole::RuleLocalRewriteTo, ordinal),
        from: Box::new(from),
        to,
    }
}

pub(super) fn wire_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    ProvenanceKey::new(role, ordinal)
}

pub(super) fn wire_sort_reference(
    slots: &mut WireSlots,
    facade: &Path,
    role: ProvenanceRole,
    ordinal: u32,
    key: &Ident,
    authored_path: &str,
) -> WireSortReference {
    WireSortReference {
        key: wire_key(role, ordinal),
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
    Path,
    ApplicationHead,
    Reference,
    Literal,
    RecordFieldName,
    Wildcard,
}

impl TermSide {
    pub(super) fn role(self, role: TermRole) -> ProvenanceRole {
        use ProvenanceRole as P;
        use TermRole as T;
        match (self, role) {
            (Self::Left, T::Path) => P::RuleLeftPath,
            (Self::Left, T::ApplicationHead) => P::RuleLeftApplicationHead,
            (Self::Left, T::Reference) => P::RuleLeftReference,
            (Self::Left, T::Literal) => P::RuleLeftLiteral,
            (Self::Left, T::RecordFieldName) => P::RuleLeftRecordFieldName,
            (Self::Left, T::Wildcard) => P::RuleLeftWildcard,
            (Self::Right, T::Path) => P::RuleRightPath,
            (Self::Right, T::ApplicationHead) => P::RuleRightApplicationHead,
            (Self::Right, T::Reference) => P::RuleRightReference,
            (Self::Right, T::Literal) => P::RuleRightLiteral,
            (Self::Right, T::Wildcard) => P::RuleRightWildcard,
            (Self::Right, T::RecordFieldName) => P::RuleRightRecordFieldName,
            (Self::Requires, T::Path) => P::RuleRequiresPath,
            (Self::Requires, T::ApplicationHead) => P::RuleRequiresApplicationHead,
            (Self::Requires, T::Reference) => P::RuleRequiresReference,
            (Self::Requires, T::Literal | T::Wildcard) => P::RuleRequiresLiteral,
            (Self::Requires, T::RecordFieldName) => P::RuleRequiresRecordFieldName,
            (Self::Ensures, T::Path) => P::ClaimEnsuresPath,
            (Self::Ensures, T::ApplicationHead) => P::ClaimEnsuresApplicationHead,
            (Self::Ensures, T::Reference) => P::ClaimEnsuresReference,
            (Self::Ensures, T::Literal | T::Wildcard) => P::ClaimEnsuresLiteral,
            (Self::Ensures, T::RecordFieldName) => P::ClaimEnsuresRecordFieldName,
            (Self::RuleEnsures, T::Path) => P::RuleEnsuresPath,
            (Self::RuleEnsures, T::ApplicationHead) => P::RuleEnsuresApplicationHead,
            (Self::RuleEnsures, T::Reference) => P::RuleEnsuresReference,
            (Self::RuleEnsures, T::Literal | T::Wildcard) => P::RuleEnsuresLiteral,
            (Self::RuleEnsures, T::RecordFieldName) => P::RuleEnsuresRecordFieldName,
        }
    }
}

#[derive(Default)]
struct TermCounters {
    path: u32,
    application: u32,
    reference: u32,
    literal: u32,
    field: u32,
    wildcard: u32,
}

#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag selects one independent sentence-kind policy or records one mode or nesting context of the shared term builder."
)]
pub(super) struct TermBuilder<'a> {
    facade: &'a Path,
    pub(super) nonce: u64,
    pub(super) cfg: &'a [Attribute],
    bindings: &'a [Ident],
    counters: TermCounters,
    pub(super) next_key: usize,
    pub(super) key_functions: Vec<TokenStream>,
    associated_keys: bool,
    claim: bool,
    pub(super) id_token_ordinal: u32,
    pub(super) bytes_token_ordinal: u32,
    pub(super) or_bool_ordinal: u32,
    /// Side-neutral: lexemes are numbered once across a whole sentence, so
    /// [`Self::reset_side`] keeps it and chained builders copy it forward.
    pub(super) lexeme_ordinal: u32,
    /// Side-neutral like [`Self::lexeme_ordinal`]: `k::is!` and
    /// `k::project!` terms are numbered once across a whole sentence.
    pub(super) sort_test_ordinal: u32,
    /// `name @ pattern` ordinals, numbered once across a sentence's
    /// left-hand side (the only side that may alias).
    pub(super) pattern_as_ordinal: u32,
    /// `A | B` ordinals, numbered once across a sentence's left-hand side
    /// and its `k::matches!` patterns.
    pub(super) pattern_or_ordinal: u32,
    /// `k::matches!` ordinals, side-neutral like [`Self::lexeme_ordinal`].
    pub(super) matches_ordinal: u32,
    /// Turbofish sort-marker ordinals, side-neutral like sort tests (KF-027).
    pub(super) application_instance_ordinal: u32,
    /// Whether this sentence kind admits turbofish instances (KF-027).
    application_instances: bool,
    /// Ordinals of the `_` in `k::matches!` patterns, side-neutral.
    pub(super) matches_wildcard_ordinal: u32,
    /// The local binders (BIND-1) of the `k::matches!` pattern being
    /// expanded, or `None` outside one.
    local_binders: Option<Vec<Ident>>,
    /// `let` statement ordinals, side-neutral (KF-032).
    pub(super) let_ordinal: u32,
    /// Ordinals of the `_` in `let` patterns, side-neutral.
    pub(super) let_wildcard_ordinal: u32,
    /// The local binders of the `let` pattern being expanded, or `None`
    /// outside one.
    let_pattern_binders: Option<Vec<Ident>>,
    /// The local binders of the enclosing `let` statements and `ml::exists`
    /// closures, innermost last.
    let_scopes: Vec<Vec<Ident>>,
    /// `ml::exists` closure ordinals, side-neutral (KF-039).
    pub(super) ml_binder_ordinal: u32,
    enum_glob: Option<&'a Path>,
    enum_variant: Option<&'a Ident>,
    lexical_rule_head: bool,
    pub(super) tooling_binding_references: Vec<Path>,
    /// Whether `k::rewrite!` is admitted: the subject of a single-body rule
    /// (KF-011).
    allow_rewrite: bool,
    /// Whether a `k::rewrite!` is being expanded.
    in_rewrite: bool,
    /// `k::rewrite!` ordinals, side-neutral.
    pub(super) rewrite_ordinal: u32,
}

impl<'a> TermBuilder<'a> {
    pub(super) fn new(
        facade: &'a Path,
        nonce: u64,
        cfg: &'a [Attribute],
        bindings: &'a [Ident],
    ) -> Self {
        Self {
            facade,
            nonce,
            cfg,
            bindings,
            counters: TermCounters::default(),
            next_key: 0,
            key_functions: Vec::new(),
            associated_keys: false,
            claim: false,
            id_token_ordinal: 0,
            bytes_token_ordinal: 0,
            or_bool_ordinal: 0,
            lexeme_ordinal: 0,
            sort_test_ordinal: 0,
            pattern_as_ordinal: 0,
            pattern_or_ordinal: 0,
            matches_ordinal: 0,
            application_instance_ordinal: 0,
            application_instances: true,
            matches_wildcard_ordinal: 0,
            local_binders: None,
            let_ordinal: 0,
            let_wildcard_ordinal: 0,
            let_pattern_binders: None,
            let_scopes: Vec::new(),
            ml_binder_ordinal: 0,
            enum_glob: None,
            enum_variant: None,
            lexical_rule_head: false,
            tooling_binding_references: Vec::new(),
            allow_rewrite: false,
            in_rewrite: false,
            rewrite_ordinal: 0,
        }
    }

    /// Admits `k::rewrite!` (KF-011) in the terms expanded next: `true` for
    /// the subject of a single-body rule.
    pub(super) fn set_rewrites(&mut self, allowed: bool) {
        self.allow_rewrite = allowed;
    }

    /// Starts one `k::rewrite!` (K's local `=>`, KF-011) on `side` and
    /// returns its ordinal; [`Self::leave_rewrite`] ends it.
    pub(super) fn enter_rewrite(
        &mut self,
        range: krs_syntax::TokenRange,
        left_side: bool,
    ) -> crate::Result<u32> {
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
        let ordinal = self.rewrite_ordinal;
        self.rewrite_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                range.first(),
                "too many `k::rewrite!` islands in one sentence",
            )
        })?;
        self.in_rewrite = true;
        Ok(ordinal)
    }

    /// Ends the `k::rewrite!` [`Self::enter_rewrite`] started.
    pub(super) fn leave_rewrite(&mut self) {
        self.in_rewrite = false;
    }

    /// Expands `k::rewrite!(from => to)` (K's local `=>`, KF-011): the left
    /// side, then the right side, both numbered with the subject's ordinals.
    fn expand_rewrite(
        &mut self,
        range: krs_syntax::TokenRange,
        from: &TermTree,
        to: Option<&TermTree>,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let ordinal = self.enter_rewrite(range, matches!(side, TermSide::Left))?;
        let from = self.expand_wire(from, side, slots);
        let to = match (from.is_ok(), to) {
            (true, Some(to)) => Some(self.expand_wire(to, side, slots).map(Box::new)).transpose(),
            _ => Ok(None),
        };
        self.leave_rewrite();
        Ok(rewrite_wire(ordinal, from?, to?))
    }

    pub(super) fn with_associated_keys(mut self) -> Self {
        self.associated_keys = true;
        self
    }

    pub(super) fn for_claim(mut self) -> Self {
        self.claim = true;
        self
    }

    pub(super) fn with_enum_glob(mut self, owner: Option<&'a Path>) -> Self {
        self.enum_glob = owner;
        self
    }

    pub(super) fn with_enum_import(
        mut self,
        owner: Option<&'a Path>,
        variant: Option<&'a Ident>,
    ) -> Self {
        self.enum_glob = owner;
        self.enum_variant = variant;
        self
    }

    /// Rejects turbofish instances on application heads (KF-027): an
    /// initializer builds a concrete value, whose syntax numbers no instance.
    pub(super) const fn without_application_instances(mut self) -> Self {
        self.application_instances = false;
        self
    }

    pub(super) fn with_lexical_rule_head(mut self, enabled: bool) -> Self {
        self.lexical_rule_head = enabled;
        self
    }

    /// The per-side ordinals of this side so far, as `[application,
    /// reference, literal, record field, wildcard]`, for a `cells!` pattern
    /// that continues the side (an equation's function context, KF-025).
    pub(super) const fn side_ordinals(&self) -> [u32; 5] {
        [
            self.counters.application,
            self.counters.reference,
            self.counters.literal,
            self.counters.field,
            self.counters.wildcard,
        ]
    }

    pub(super) fn reset_side(&mut self) {
        self.counters = TermCounters::default();
    }

    /// Continues the sentence-wide (side-neutral) ordinals of `previous`, a
    /// builder of an earlier side of the same sentence.
    pub(super) fn continue_ordinals(&mut self, previous: &TermBuilder<'_>) {
        self.lexeme_ordinal = previous.lexeme_ordinal;
        self.sort_test_ordinal = previous.sort_test_ordinal;
        self.application_instance_ordinal = previous.application_instance_ordinal;
        self.pattern_as_ordinal = previous.pattern_as_ordinal;
        self.pattern_or_ordinal = previous.pattern_or_ordinal;
        self.matches_ordinal = previous.matches_ordinal;
        self.matches_wildcard_ordinal = previous.matches_wildcard_ordinal;
        self.let_ordinal = previous.let_ordinal;
        self.let_wildcard_ordinal = previous.let_wildcard_ordinal;
        self.ml_binder_ordinal = previous.ml_binder_ordinal;
        self.rewrite_ordinal = previous.rewrite_ordinal;
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
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "a `let` block (K's #let) is a term; it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        if self.claim {
            return Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "`let` blocks are not supported in claims: the pinned native prover cannot resolve K's #let in a claim; bind the value in the claim's subject instead",
            ));
        }
        let ordinal = self.let_ordinal;
        self.let_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                range.first(),
                "too many `let` statements in one sentence",
            )
        })?;
        let sort = sort
            .map(|sort| self.local_sort_reference(ProvenanceRole::LetSort, ordinal, sort, slots))
            .transpose()?;
        self.let_pattern_binders = Some(binders.to_vec());
        let pattern = self.expand_wire(pattern, side, slots);
        self.let_pattern_binders = None;
        let pattern = pattern?;
        let value = self.expand_wire(value, side, slots)?;
        self.let_scopes.push(binders.to_vec());
        let body = self.expand_wire(body, side, slots);
        self.let_scopes.pop();
        Ok(WireTerm::Let {
            key: wire_key(ProvenanceRole::Let, ordinal),
            pattern: Box::new(pattern),
            sort,
            value: Box::new(value),
            body: Box::new(body?),
        })
    }

    /// The rustc-resolved sort of `let name: Sort = value;` or of the binder
    /// of `ml::exists(|name: Sort| ..)`, keyed `role`.
    fn local_sort_reference(
        &mut self,
        role: ProvenanceRole,
        ordinal: u32,
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
            key: wire_key(role, ordinal),
            target: krs_ir::wire::WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                authored_path: spelling(sort),
            },
        })
    }

    /// Expands the closure `|binder: Sort| body` of an `ml::exists`
    /// (KF-039): its binder is local to the body, like a `let` binder.
    fn expand_closure(
        &mut self,
        range: krs_syntax::TokenRange,
        binder: &Ident,
        sort: &Path,
        body: &TermTree,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::ML_PLACEMENT,
                range.first(),
                "an `ml::exists` closure is a predicate (K's #Exists); it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        let ordinal = self.ml_binder_ordinal;
        self.ml_binder_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                range.first(),
                "too many `ml::exists` closures in one sentence",
            )
        })?;
        let sort = self.local_sort_reference(ProvenanceRole::MlBinderSort, ordinal, sort, slots)?;
        self.let_scopes.push(vec![binder.clone()]);
        let body = self.expand_wire(body, side, slots);
        self.let_scopes.pop();
        Ok(WireTerm::Closure {
            key: wire_key(ProvenanceRole::MlConnective, ordinal),
            binder_key: wire_key(ProvenanceRole::MlBinder, ordinal),
            name: binder.to_string(),
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
    fn expand_matches(
        &mut self,
        range: krs_syntax::TokenRange,
        subject: &TermTree,
        pattern: &TermTree,
        binders: &[Ident],
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        if matches!(side, TermSide::Left) || self.in_matches_pattern() || self.in_let_pattern() {
            return Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is a Bool test (K's :=K); it cannot appear on a left-hand side or inside a pattern",
            ));
        }
        if self.claim {
            return Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is not supported in claims: the pinned native prover cannot resolve K's :=K in a claim; match the shape in the claim's subject instead",
            ));
        }
        let ordinal = self.matches_ordinal;
        self.matches_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                range.first(),
                "too many `k::matches!` terms in one sentence",
            )
        })?;
        let subject = self.expand_wire(subject, side, slots)?;
        self.local_binders = Some(binders.to_vec());
        let pattern = self.expand_wire(pattern, side, slots);
        self.local_binders = None;
        Ok(WireTerm::Matches {
            key: wire_key(ProvenanceRole::Matches, ordinal),
            subject: Box::new(subject),
            pattern: Box::new(pattern?),
        })
    }

    /// Builds the literal term tree while retaining Rust-resolved heads in slots.
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive transport for the closed structured-term grammar."
    )]
    pub(super) fn expand_wire(
        &mut self,
        tree: &TermTree,
        side: TermSide,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        match tree {
            TermTree::Application(application) => {
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let path_key = wire_key(side.role(TermRole::Path), path_ordinal);
                let key = wire_key(side.role(TermRole::ApplicationHead), application_ordinal);
                let lexical = self.take_lexical_rule_head(application.head());
                let authored_path = if lexical {
                    spelling(application.head())
                } else {
                    self.application_authored_path(application.head())
                };
                let target = if lexical {
                    let expression = self.lexical_rule_application_target(
                        &turbofish_path(application),
                        Some(application.arguments()),
                    );
                    slots.target_slot_unique(&expression)
                } else {
                    self.application_wire_slot(application.head(), slots)?
                };
                let instance = self.application_instance_wire(application, slots)?;
                let arguments = match application.arguments() {
                    TermArguments::Positional(values) => {
                        let mut arguments = Vec::new();
                        for value in values {
                            arguments.push(Box::new(self.expand_wire(value, side, slots)?));
                        }
                        krs_ir::Arguments::Positional(arguments)
                    }
                    TermArguments::Named(values) => {
                        let mut arguments = Vec::new();
                        for argument in values {
                            let ordinal = take_counter(&mut self.counters.field)?;
                            let field = ProductionFieldId::new(argument.name().to_string())
                                .expect("Rust field identifiers are valid production fields");
                            arguments.push(krs_ir::NamedTermArgument {
                                key: wire_key(side.role(TermRole::RecordFieldName), ordinal),
                                field,
                                value: Box::new(self.expand_wire(argument.value(), side, slots)?),
                            });
                        }
                        krs_ir::Arguments::named(arguments)
                    }
                };
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
                })
            }
            TermTree::Reference(path) => {
                let lexical = self.take_lexical_rule_head(path);
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let reference_ordinal = take_counter(&mut self.counters.reference)?;
                let path_key = wire_key(side.role(TermRole::Path), path_ordinal);
                let key = wire_key(side.role(TermRole::Reference), reference_ordinal);
                if self.is_local_binder(path) {
                    // A local binder has no Rust binding for tooling to use.
                    Ok(WireTerm::Variable {
                        key,
                        path_key,
                        name: spelling(path),
                    })
                } else if is_bound_ident_path(path, self.bindings) {
                    self.tooling_binding_references.push(path.clone());
                    Ok(WireTerm::Variable {
                        key,
                        path_key,
                        name: spelling(path),
                    })
                } else {
                    let authored_path = if lexical {
                        spelling(path)
                    } else {
                        self.application_authored_path(path)
                    };
                    let target = if lexical {
                        let expression = self.lexical_rule_application_target(path, None);
                        slots.target_slot_unique(&expression)
                    } else {
                        self.application_wire_slot(path, slots)?
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
                    })
                }
            }
            TermTree::Literal(literal) => {
                let ordinal = take_counter(&mut self.counters.literal)?;
                let literal = wire_literal(literal);
                Ok(WireTerm::Literal {
                    key: wire_key(side.role(TermRole::Literal), ordinal),
                    literal,
                })
            }
            TermTree::Wildcard(range) if self.in_let_pattern() => {
                let ordinal = self.let_wildcard_ordinal;
                self.let_wildcard_ordinal = ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        range.first(),
                        "too many `_` in `let` patterns in one sentence",
                    )
                })?;
                Ok(WireTerm::Wildcard {
                    key: wire_key(ProvenanceRole::LetWildcard, ordinal),
                })
            }
            TermTree::Wildcard(range) if self.in_matches_pattern() => {
                let ordinal = self.matches_wildcard_ordinal;
                self.matches_wildcard_ordinal = ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        range.first(),
                        "too many `_` in `k::matches!` patterns in one sentence",
                    )
                })?;
                Ok(WireTerm::Wildcard {
                    key: wire_key(ProvenanceRole::MatchesWildcard, ordinal),
                })
            }
            TermTree::Wildcard(_) => {
                // A result wildcard parses only for a desugar clause that
                // lists `_` in `unbound_variables` (KF-046).
                if !matches!(side, TermSide::Left | TermSide::Right) {
                    return Err(ExpandError::new(
                        expand::RULE_RESULT_WILDCARD,
                        Span::call_site(),
                        "KRS rule results cannot contain wildcards",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.wildcard)?;
                Ok(WireTerm::Wildcard {
                    key: wire_key(side.role(TermRole::Wildcard), ordinal),
                })
            }
            TermTree::IdToken { literal } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        literal.span(),
                        "id! is currently claim-only",
                    ));
                }
                let ordinal = self.id_token_ordinal;
                self.id_token_ordinal += 1;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimIdToken, ordinal),
                    sort: BuiltinSort::Id,
                    value: literal.value(),
                })
            }
            TermTree::BytesToken { literal } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        literal.span(),
                        "bytes! is currently claim-only",
                    ));
                }
                let ordinal = self.bytes_token_ordinal;
                self.bytes_token_ordinal += 1;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimBytesToken, ordinal),
                    sort: BuiltinSort::Bytes,
                    value: bytes_token::encode(&literal.value()),
                })
            }
            TermTree::Anonymous { spelling, .. } => Err(ExpandError::new(
                expand::CLAIM_SUBJECT_ONLY_TERM,
                spelling.span(),
                "anonymous! is valid only in a claim subject",
            )),
            TermTree::Lexeme { sort, text } => self.lexeme_wire(sort, text, slots),
            TermTree::SortTest {
                range,
                kind,
                sort,
                operand,
            } => {
                let (key, sort) = self.sort_test_reference(*range, sort, slots)?;
                Ok(WireTerm::SortTest {
                    key,
                    kind: *kind,
                    sort,
                    operand: Box::new(self.expand_wire(operand, side, slots)?),
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
                let (key, binding_key) = self.take_pattern_as(binding)?;
                Ok(WireTerm::As {
                    key,
                    binding_key,
                    name: binding.to_string(),
                    pattern: Box::new(self.expand_wire(pattern, side, slots)?),
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
                        "`A | B` alternatives occur only on a left-hand side (K's #Or); for Bool disjunction use bool::or or k::or_bool!",
                    ));
                }
                let key = self.take_pattern_or(range.first())?;
                Ok(WireTerm::Or {
                    key,
                    alternatives: alternatives
                        .try_map_ref(|alternative| self.expand_wire(alternative, side, slots))?,
                })
            }
            TermTree::Matches {
                range,
                subject,
                pattern,
                binders,
            } => self.expand_matches(*range, subject, pattern, binders, side, slots),
            TermTree::Rewrite {
                range, from, to, ..
            } => self.expand_rewrite(*range, from, to.as_deref(), side, slots),
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
                side,
                slots,
            ),
            TermTree::Closure {
                range,
                binder,
                sort,
                body,
            } => self.expand_closure(*range, binder, sort, body, side, slots),
            TermTree::OrBool { arguments, .. } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        Span::call_site(),
                        "or_bool! is currently claim-only",
                    ));
                }
                let ordinal = self.or_bool_ordinal;
                self.or_bool_ordinal += 1;
                let arguments =
                    arguments.try_map_ref(|argument| self.expand_wire(argument, side, slots))?;
                Ok(WireTerm::OrBool {
                    key: wire_key(ProvenanceRole::ClaimOrBool, ordinal),
                    arguments,
                })
            }
            TermTree::Cell(cell) => {
                let _path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let key = wire_key(side.role(TermRole::ApplicationHead), application_ordinal);
                let declaration = self.cell_declaration_reference(cell.owner(), slots)?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let ordinal = take_counter(&mut self.counters.field)?;
                    let name = ProductionFieldId::new(field.name().to_string())
                        .expect("Rust fields are valid cell-field identities");
                    fields.push(WireCellTermField {
                        key: wire_key(side.role(TermRole::RecordFieldName), ordinal),
                        field: name,
                        value: Box::new(self.expand_wire(field.value(), side, slots)?),
                    });
                }
                Ok(WireTerm::Cell {
                    key,
                    declaration,
                    fields,
                })
            }
        }
    }

    /// Numbers one `name @ pattern` (K's `#as`) in left-hand-side preorder
    /// and returns its shell and alias keys.
    pub(super) fn take_pattern_as(
        &mut self,
        binding: &Ident,
    ) -> crate::Result<(ProvenanceKey, ProvenanceKey)> {
        let ordinal = self.pattern_as_ordinal;
        self.pattern_as_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                binding.span(),
                "too many `name @ pattern` aliases in one sentence",
            )
        })?;
        if self.bindings.contains(binding) && !self.in_matches_pattern() {
            self.tooling_binding_references
                .push(Path::from(binding.clone()));
        }
        Ok((
            wire_key(ProvenanceRole::PatternAs, ordinal),
            wire_key(ProvenanceRole::PatternAsBinding, ordinal),
        ))
    }

    /// Numbers one `A | B` or-pattern (K's `#Or`) in left-hand-side preorder
    /// and returns its shell key.
    pub(super) fn take_pattern_or(&mut self, span: Span) -> crate::Result<ProvenanceKey> {
        let ordinal = self.pattern_or_ordinal;
        self.pattern_or_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                span,
                "too many `A | B` or-patterns in one sentence",
            )
        })?;
        Ok(wire_key(ProvenanceRole::PatternOr, ordinal))
    }

    /// Lowers `k::lexeme!(Sort, "text")` to a token term whose sort rustc
    /// resolves through a type key.
    pub(super) fn lexeme_wire(
        &mut self,
        sort: &Path,
        text: &syn::LitStr,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let ordinal = self.lexeme_ordinal;
        self.lexeme_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                text.span(),
                "too many lexeme! terms in one sentence",
            )
        })?;
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
            key: wire_key(ProvenanceRole::LexemeText, ordinal),
            sort: krs_ir::wire::WireSortReference {
                key: wire_key(ProvenanceRole::LexemeSort, ordinal),
                target: krs_ir::wire::WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                    authored_path: spelling(sort),
                },
            },
            text: text.value(),
        })
    }

    /// Numbers one `k::is!` or `k::project!` term and lowers its sort path to
    /// a sort whose identity rustc resolves through a type key.
    pub(super) fn sort_test_reference(
        &mut self,
        range: krs_syntax::TokenRange,
        sort: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<(krs_ir::ProvenanceKey, krs_ir::wire::WireSortReference)> {
        let ordinal = self.sort_test_ordinal;
        self.sort_test_ordinal = ordinal.checked_add(1).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                range.first(),
                "too many is! and project! terms in one sentence",
            )
        })?;
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
            wire_key(ProvenanceRole::SortTest, ordinal),
            krs_ir::wire::WireSortReference {
                key: wire_key(ProvenanceRole::SortTestSort, ordinal),
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

    pub(super) fn application_wire_slot(
        &mut self,
        authored: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<TargetSlot> {
        check_ml_item(authored)?;
        let (owner, variant) = if authored.leading_colon.is_none()
            && authored.segments.len() == 1
            && let Some(imported_owner) = self.enum_glob
            && let Some(imported_variant) = authored.segments.first()
            && self
                .enum_variant
                .is_none_or(|variant| variant == &imported_variant.ident)
        {
            (
                call_site_path(imported_owner)?,
                Some(imported_variant.ident.clone()),
            )
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
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
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
            let marker_key = quote!(#facade::HostTypeKey(#owner::#marker));
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
        slots: &mut WireSlots,
    ) -> crate::Result<Vec<krs_ir::wire::WireSortReference>> {
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
        for sort in instance {
            let ordinal = self.application_instance_ordinal;
            self.application_instance_ordinal = ordinal.checked_add(1).ok_or_else(|| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    syn::spanned::Spanned::span(sort.ty()),
                    "too many turbofish instances in one sentence",
                )
            })?;
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
                key: wire_key(ProvenanceRole::ApplicationInstance, ordinal),
                target: krs_ir::wire::WireTypeReference {
                    slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_reference))),
                    authored_path: quote::ToTokens::to_token_stream(sort.ty()).to_string(),
                },
            });
        }
        Ok(references)
    }

    pub(super) fn application_authored_path(&self, path: &Path) -> String {
        if path.leading_colon.is_none()
            && path.segments.len() == 1
            && let Some(owner) = self.enum_glob
            && let Some(variant) = path.segments.first()
            && self
                .enum_variant
                .is_none_or(|imported| imported == &variant.ident)
        {
            return format!("{}::{}", spelling(owner), variant.ident);
        }
        spelling(path)
    }

    fn take_lexical_rule_head(&mut self, path: &Path) -> bool {
        let enabled = ::core::mem::take(&mut self.lexical_rule_head);
        enabled && path.leading_colon.is_none() && path.segments.len() == 1
    }

    fn lexical_rule_application_target(
        &self,
        authored: &Path,
        arguments: Option<&TermArguments>,
    ) -> TokenStream {
        let path = authored.clone();
        let ident = authored
            .segments
            .first()
            .expect("one-segment lexical paths have one identifier");
        let selector = rule_application_selector(&ident.ident);
        let authored_spelling = spelling(authored);
        let pattern = match arguments {
            Some(TermArguments::Positional(values)) if values.is_empty() => quote!(#path(..)),
            Some(TermArguments::Positional(_) | TermArguments::Named(_)) => quote!(#path { .. }),
            None => quote!(#path),
        };
        let facade = self.facade;
        quote! {{
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
