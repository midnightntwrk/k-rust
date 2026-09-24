//! The symbolic term builder shared by rules, claims, and initializers.

use krs_syntax::{ProvenanceRole, TermArguments, TermLiteral, TermTree};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Attribute, Ident, Path};

use super::nonce::rule_application_selector;
use super::tokens::{
    bytes_token_value, call_site_path, enum_variant_parts, is_bound_ident_path, provenance_key,
    spelling, take_counter, variant_marker_function,
};

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

    #[allow(clippy::too_many_lines)]
    pub(super) fn expand(&mut self, tree: &TermTree, side: TermSide) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let reference_key = provenance_key(
                    facade,
                    side.role(TermRole::ApplicationHead),
                    application_ordinal,
                );
                let target = if self.take_lexical_rule_head(application.head()) {
                    self.lexical_rule_application_target(
                        application.head(),
                        Some(application.arguments()),
                    )
                } else {
                    self.application_target(application.head())?
                };
                let mut arguments = Vec::new();
                match application.arguments() {
                    TermArguments::Positional(values) => {
                        for value in values {
                            let value = self.expand(value, side)?;
                            arguments.push(quote! {
                                #facade::HostTermArgument::Positional {
                                    value: ::std::boxed::Box::new(#value),
                                }
                            });
                        }
                    }
                    TermArguments::Named(values) => {
                        for argument in values {
                            let field_ordinal = take_counter(&mut self.counters.field)?;
                            let field_key = provenance_key(
                                facade,
                                side.role(TermRole::RecordFieldName),
                                field_ordinal,
                            );
                            let field = argument.name().to_string();
                            let value = self.expand(argument.value(), side)?;
                            arguments.push(quote! {
                                #facade::HostTermArgument::Named {
                                    key: #field_key,
                                    field: #facade::ProductionFieldId::new(#field)
                                        .expect("Rust field identifiers are valid production fields"),
                                    value: ::std::boxed::Box::new(#value),
                                }
                            });
                        }
                    }
                }
                Ok(quote! {
                    #facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::Applied,
                        reference: #facade::HostApplicationReference {
                            key: #reference_key,
                            target: #target,
                        },
                        path_key: #path_key,
                        arguments: ::std::vec![#(#arguments),*],
                    }
                })
            }
            TermTree::Reference(path) => {
                let lexical_rule_head = self.take_lexical_rule_head(path);
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let reference_ordinal = take_counter(&mut self.counters.reference)?;
                let path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let key = provenance_key(facade, side.role(TermRole::Reference), reference_ordinal);
                if is_bound_ident_path(path, self.bindings) {
                    self.tooling_binding_references.push(path.clone());
                    let name = spelling(path);
                    Ok(quote! {
                        #facade::HostTerm::Variable {
                            key: #key,
                            path_key: #path_key,
                            name: #name.to_owned(),
                        }
                    })
                } else {
                    let target = if lexical_rule_head {
                        self.lexical_rule_application_target(path, None)
                    } else {
                        self.application_target(path)?
                    };
                    Ok(quote! {
                        #facade::HostTerm::Application {
                            head_class: #facade::DescriptorApplicationHeadClass::BareReference,
                            reference: #facade::HostApplicationReference {
                                key: #key,
                                target: #target,
                            },
                            path_key: #path_key,
                            arguments: ::std::vec![],
                        }
                    })
                }
            }
            TermTree::Literal(literal) => {
                let ordinal = take_counter(&mut self.counters.literal)?;
                let key = provenance_key(facade, side.role(TermRole::Literal), ordinal);
                let literal = match literal {
                    TermLiteral::Integer(value) => {
                        let value = value.base10_digits().replace('_', "");
                        quote!(#facade::DescriptorLiteral::Int(#value.to_owned()))
                    }
                    TermLiteral::Boolean(value) => {
                        let value = value.value;
                        quote!(#facade::DescriptorLiteral::Bool(#value))
                    }
                };
                Ok(quote!(#facade::HostTerm::Literal { key: #key, literal: #literal }))
            }
            TermTree::Wildcard(_) => {
                if !matches!(side, TermSide::Left) {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "KRS rule results cannot contain wildcards",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.wildcard)?;
                let key = provenance_key(facade, side.role(TermRole::Wildcard), ordinal);
                Ok(quote!(#facade::HostTerm::Wildcard { key: #key }))
            }
            TermTree::IdToken { literal } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        literal.span(),
                        "id! is currently claim-only",
                    ));
                }
                let ordinal = self.id_token_ordinal;
                self.id_token_ordinal += 1;
                let key = provenance_key(facade, ProvenanceRole::ClaimIdToken, ordinal);
                let value = literal.value();
                Ok(
                    quote!(#facade::HostTerm::BuiltinToken { key: #key, sort: #facade::BuiltinSort::Id, value: #value.to_owned() }),
                )
            }
            TermTree::BytesToken { literal } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        literal.span(),
                        "bytes! is currently claim-only",
                    ));
                }
                let ordinal = self.bytes_token_ordinal;
                self.bytes_token_ordinal += 1;
                let key = provenance_key(facade, ProvenanceRole::ClaimBytesToken, ordinal);
                let value = bytes_token_value(literal);
                Ok(
                    quote!(#facade::HostTerm::BuiltinToken { key: #key, sort: #facade::BuiltinSort::Bytes, value: #value.to_owned() }),
                )
            }
            TermTree::Anonymous { spelling, .. } => Err(syn::Error::new(
                spelling.span(),
                "anonymous! is valid only in a claim subject",
            )),
            TermTree::OrBool { arguments, .. } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "or_bool! is currently claim-only",
                    ));
                }
                let ordinal = self.or_bool_ordinal;
                self.or_bool_ordinal += 1;
                let key = provenance_key(facade, ProvenanceRole::ClaimOrBool, ordinal);
                let values = arguments
                    .iter()
                    .map(|argument| self.expand(argument, side))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote!(#facade::HostTerm::OrBool { key: #key, arguments: vec![#(#values),*] }))
            }
            TermTree::Cell(cell) => {
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let _path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let key = provenance_key(
                    facade,
                    side.role(TermRole::ApplicationHead),
                    application_ordinal,
                );
                let declaration = self.cell_declaration_target(cell.owner())?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let ordinal = take_counter(&mut self.counters.field)?;
                    let field_key =
                        provenance_key(facade, side.role(TermRole::RecordFieldName), ordinal);
                    let name = field.name().to_string();
                    let value = self.expand(field.value(), side)?;
                    fields.push(quote!(#facade::HostCellTermField {
                        key: #field_key,
                        field: #facade::ProductionFieldId::new(#name)
                            .expect("Rust fields are valid cell-field identities"),
                        value: ::std::boxed::Box::new(#value),
                    }));
                }
                Ok(quote!(#facade::HostTerm::Cell {
                    key: #key, declaration: #declaration,
                    fields: ::std::vec![#(#fields),*],
                }))
            }
        }
    }

    pub(super) fn cell_declaration_target(&mut self, authored: &Path) -> syn::Result<TokenStream> {
        let generated = call_site_path(authored)?;
        let authored_spelling = spelling(authored);
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
        Ok(quote!(#facade::HostTypeReference {
            key: #facade::HostTypeKey(#key_reference),
            authored_path: #authored_spelling.to_owned(),
        }))
    }

    pub(super) fn application_target(&mut self, authored: &Path) -> syn::Result<TokenStream> {
        if authored.leading_colon.is_none()
            && authored.segments.len() == 1
            && let Some(owner) = self.enum_glob
        {
            let variant = authored
                .segments
                .first()
                .expect("one-segment paths have one identifier")
                .ident
                .clone();
            if self
                .enum_variant
                .is_none_or(|imported| imported == &variant)
            {
                return self.enum_variant_target(owner, &variant);
            }
        }
        // Resolve the descriptor witness from the authored path itself so
        // qualified calls retain definition, hover, completion, and rename
        // mapping through the proc-macro expansion.
        let generated = authored;
        let authored_spelling = spelling(authored);
        let key_fn = format_ident!(
            "__krs_rule_application_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let facade = self.facade;
        let cfg = self.cfg;
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        if let Some((owner, variant)) = enum_variant_parts(generated) {
            let owner_spelling = spelling(&owner);
            let marker = variant_marker_function(&variant);
            self.key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#owner>()
                }
            });
            Ok(quote! {
                #facade::HostApplicationTarget::EnumVariant(
                    #facade::HostEnumVariantReference::new(
                        #facade::HostTypeReference {
                            key: #facade::HostTypeKey(#key_reference),
                            authored_path: #owner_spelling.to_owned(),
                        },
                        #facade::HostTypeKey(#owner::#marker),
                        #authored_spelling,
                    )
                    .expect("qualified enum variants retain their owning enum path"),
                )
            })
        } else {
            self.key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#generated>()
                }
            });
            Ok(quote! {
                #facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
                    key: #facade::HostTypeKey(#key_reference),
                    authored_path: #authored_spelling.to_owned(),
                })
            })
        }
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

    fn enum_variant_target(
        &mut self,
        authored_owner: &Path,
        variant: &Ident,
    ) -> syn::Result<TokenStream> {
        let owner = call_site_path(authored_owner)?;
        let owner_spelling = spelling(authored_owner);
        let authored_spelling = format!("{owner_spelling}::{variant}");
        let marker = variant_marker_function(variant);
        let key_fn = format_ident!(
            "__krs_rule_application_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let facade = self.facade;
        let cfg = self.cfg;
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#owner>()
            }
        });
        Ok(quote! {
            #facade::HostApplicationTarget::EnumVariant(
                #facade::HostEnumVariantReference::new(
                    #facade::HostTypeReference {
                        key: #facade::HostTypeKey(#key_reference),
                        authored_path: #owner_spelling.to_owned(),
                    },
                    #facade::HostTypeKey(#owner::#marker),
                    #authored_spelling,
                )
                .expect("block-local enum imports retain their owning enum path"),
            )
        })
    }
}
