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
            (Self::Right, T::Literal | T::Wildcard) => P::RuleRightLiteral,
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
    enum_glob: Option<&'a Path>,
    enum_variant: Option<&'a Ident>,
    lexical_rule_head: bool,
    pub(super) tooling_binding_references: Vec<Path>,
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
            enum_glob: None,
            enum_variant: None,
            lexical_rule_head: false,
            tooling_binding_references: Vec::new(),
        }
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

    pub(super) fn with_lexical_rule_head(mut self, enabled: bool) -> Self {
        self.lexical_rule_head = enabled;
        self
    }

    pub(super) fn reset_side(&mut self) {
        self.counters = TermCounters::default();
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
                        application.head(),
                        Some(application.arguments()),
                    );
                    slots.target_slot_unique(&expression)
                } else {
                    self.application_wire_slot(application.head(), slots)?
                };
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
                if is_bound_ident_path(path, self.bindings) {
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
            TermTree::Wildcard(_) => {
                if !matches!(side, TermSide::Left) {
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
