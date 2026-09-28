//! Configuration initializers: `#[k::init]`.

use krs_syntax::KrsSyntax;
use krs_syntax::{
    FixedCellInitializer, InitializerCellContent, KSequence, KSequenceNotation, MapBody,
    MapExpression, ProvenanceRole, StateTerm, TermArguments, TermExpression, TermTree, role_tokens,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, FnArg, Ident, Path, parse_quote};

use super::configuration::cell_marker_function;
use super::island_checks::initializer_state_island_import_checks;
use super::nonce::expansion_nonce;
use super::terms::TermBuilder;
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, k_notation, literal_tokens,
    map_has_role, option_key, provenance_key, sequence_has_role, sort_type_tokens, spelling,
    take_counter,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[allow(clippy::too_many_lines)]
pub(crate) fn init(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_variable_main_role = ProvenanceRole::ConfigurationVariableMain;
    let configuration_variable_role = ProvenanceRole::ConfigurationVariable;
    let configuration_variable_name_role = ProvenanceRole::ConfigurationVariableName;
    let configuration_variable_type_role = ProvenanceRole::ConfigurationVariableType;
    let initializer_declaration_role = ProvenanceRole::InitializerDeclaration;
    let initializer_result_type_role = ProvenanceRole::InitializerResultType;
    let initializer_body_role = ProvenanceRole::InitializerBody;
    krs_syntax::InitAttribute::parse_tokens(attributes)?;
    let initializer = krs_syntax::InitializerFunction::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let configuration_variable_main_role = role_tokens(configuration_variable_main_role, &facade);
    let configuration_variable_role = role_tokens(configuration_variable_role, &facade);
    let configuration_variable_name_role = role_tokens(configuration_variable_name_role, &facade);
    let configuration_variable_type_role = role_tokens(configuration_variable_type_role, &facade);
    let initializer_declaration_role = role_tokens(initializer_declaration_role, &facade);
    let initializer_result_type_role = role_tokens(initializer_result_type_role, &facade);
    let initializer_body_role = role_tokens(initializer_body_role, &facade);
    let anchors = initializer.provenance()?;
    let fallback = krs_syntax::TokenRange::for_tokens(initializer.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);

    let bindings = initializer
        .variables()
        .iter()
        .map(|variable| variable.binding().clone())
        .collect::<Vec<_>>();
    let cfg = call_site_cfg_attributes(&initializer.item().attrs)?;
    let nonce = expansion_nonce(env, "initializer", &initializer.item().sig.ident, fallback);
    let mut builder = InitializerBuilder::new(&facade, nonce, &cfg, &bindings);
    let mut variables = Vec::new();
    for (index, variable) in initializer.variables().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(variable.binding().span(), "too many variables"))?;
        let sort_path = call_site_path(variable.sort())?;
        let sort_type = variable.optional_term_sort().map_or_else(
            || quote!(#sort_path),
            |term_sort| sort_type_tokens(&sort_path, term_sort.is_dynamic()),
        );
        let sort_key = format_ident!("__krs_initializer_variable_{nonce:016x}_{index}");
        builder.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #sort_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#sort_type>()
            }
        });
        let binding = variable.binding().to_string();
        let external_name = variable.attribute().name().value();
        let main_key = if variable.attribute().is_main() {
            quote!(::core::option::Option::Some(
                #facade::ProvenanceKey::new(#configuration_variable_main_role, #ordinal)
            ))
        } else {
            quote!(::core::option::Option::None)
        };
        let authored = spelling(variable.sort());
        variables.push(quote! {
            #facade::HostConfigurationVariable {
                binding_key: #facade::ProvenanceKey::new(#configuration_variable_role, #ordinal),
                binding: #binding.to_owned(),
                external_name_key: #facade::ProvenanceKey::new(
                    #configuration_variable_name_role, #ordinal,
                ),
                external_name: #external_name.to_owned(),
                sort: #facade::HostSortReference {
                    key: #facade::ProvenanceKey::new(
                        #configuration_variable_type_role, #ordinal,
                    ),
                    target: #facade::HostTypeReference {
                        key: #facade::HostTypeKey(Self::#sort_key),
                        authored_path: #authored.to_owned(),
                    },
                },
                main_key: #main_key,
            }
        });
    }
    let cells = builder.expand_cells(initializer.cells(), &quote!(Self))?;
    let island_import_checks = initializer_state_island_import_checks(initializer.cells());
    builder
        .key_functions
        .append(&mut builder.terms.key_functions);
    let key_functions = builder.key_functions;

    // The shared parser has validated every parameter attribute as the sole
    // `config_var` helper. The outer proc macro consumes it so stable rustc
    // sees an ordinary associated method signature.
    let mut method = initializer.item().clone();
    for input in &mut method.sig.inputs {
        if let FnArg::Typed(parameter) = input {
            parameter.attrs.clear();
        }
    }
    inject_inferred_initializer_wrappers(&mut method, &initializer, &facade)?;
    method.attrs.push(parse_quote!(
        #[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
    ));

    Ok(quote! {
        #method

        #(#key_functions)*

        #[doc(hidden)]
        pub(crate) fn __krs_initializer_payload() -> (
            #facade::HostConfigurationInitializer,
            #facade::HostProvenance,
        ) {
            let _krs_path_check = || {
                #(#island_import_checks)*
            };
            fn __krs_type_key<T: ?Sized + 'static>() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<T>()
            }
            let initializer = #facade::HostConfigurationInitializer {
                key: #facade::ProvenanceKey::new(#initializer_declaration_role, 0),
                owner_key: #facade::ProvenanceKey::new(#initializer_result_type_role, 0),
                owner: #facade::HostTypeKey(__krs_type_key::<Self>),
                variables: ::std::vec![#(#variables),*],
                body_key: #facade::ProvenanceKey::new(#initializer_body_role, 0),
                cells: ::std::vec![#(#cells),*],
            };
            (initializer, #provenance)
        }
    })
}

fn inject_inferred_initializer_wrappers(
    method: &mut syn::ImplItemFn,
    initializer: &krs_syntax::InitializerFunction,
    facade: &Path,
) -> syn::Result<()> {
    let [syn::Stmt::Expr(syn::Expr::Struct(body), None)] = method.block.stmts.as_mut_slice() else {
        return Err(syn::Error::new(
            method.block.span(),
            "a fixed initializer must contain exactly one struct expression",
        ));
    };
    inject_initializer_cell_list(body, initializer.cells(), facade)
}

fn inject_initializer_cell_list(
    body: &mut syn::ExprStruct,
    cells: &[FixedCellInitializer],
    facade: &Path,
) -> syn::Result<()> {
    for cell in cells {
        let Some(field) = body
            .fields
            .iter_mut()
            .find(|field| matches!(&field.member, syn::Member::Named(name) if name == cell.name()))
        else {
            return Err(syn::Error::new(
                cell.name().span(),
                "initializer field disappeared during wrapper injection",
            ));
        };
        qualify_initializer_state_macro(&mut field.expr, facade)?;
        match cell.content() {
            InitializerCellContent::Leaf {
                computation,
                inferred_constructor: true,
                ..
            } => {
                let value = field.expr.clone();
                field.expr = if *computation {
                    parse_quote!(#facade::configuration::KCell::new(#value))
                } else {
                    parse_quote!(#facade::configuration::Cell::new(#value))
                };
                field.colon_token = Some(syn::token::Colon::default());
            }
            InitializerCellContent::Leaf {
                inferred_constructor: false,
                ..
            } => {}
            InitializerCellContent::Nested { children, .. } => {
                let syn::Expr::Struct(nested) = &mut field.expr else {
                    return Err(syn::Error::new(
                        field.expr.span(),
                        "a nested fixed-cell initializer must be a struct expression",
                    ));
                };
                inject_initializer_cell_list(nested, children, facade)?;
            }
        }
    }
    Ok(())
}

fn qualify_initializer_state_macro(expression: &mut syn::Expr, facade: &Path) -> syn::Result<()> {
    let macro_expression = match expression {
        syn::Expr::Macro(expression) => Some(expression),
        syn::Expr::Call(call) => call.args.first_mut().and_then(|argument| match argument {
            syn::Expr::Macro(expression) => Some(expression),
            _ => None,
        }),
        _ => None,
    };
    let Some(expression) = macro_expression else {
        return Ok(());
    };
    if expression.mac.path.leading_colon.is_some() || expression.mac.path.segments.len() != 1 {
        return Ok(());
    }
    let name = expression.mac.path.segments[0].ident.clone();
    if !matches!(name.to_string().as_str(), "k" | "map") {
        return Ok(());
    }
    expression.mac.path = syn::parse2(quote!(#facade::#name))?;
    Ok(())
}

#[derive(Default)]
struct InitializerCounters {
    cell: u32,
    constructor: u32,
    term: u32,
    term_path: u32,
    k_payload: u32,
    k_item: u32,
    k_tail: u32,
    map_payload: u32,
    map_key: u32,
    map_value: u32,
    map_update_base: u32,
}

struct InitializerBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    counters: InitializerCounters,
    terms: TermBuilder<'a>,
    key_functions: Vec<TokenStream>,
}

impl<'a> InitializerBuilder<'a> {
    fn new(facade: &'a Path, nonce: u64, cfg: &'a [Attribute], bindings: &'a [Ident]) -> Self {
        Self {
            facade,
            bindings,
            counters: InitializerCounters::default(),
            terms: TermBuilder::new(facade, nonce, cfg, bindings).with_associated_keys(),
            key_functions: Vec::new(),
        }
    }

    fn expand_cells(
        &mut self,
        cells: &[FixedCellInitializer],
        owner: &TokenStream,
    ) -> syn::Result<Vec<TokenStream>> {
        let initializer_field_role = ProvenanceRole::InitializerField;
        let initializer_cell_constructor_role = ProvenanceRole::InitializerCellConstructor;
        let initializer_nested_constructor_role = ProvenanceRole::InitializerNestedConstructor;
        let initializer_cell_role = ProvenanceRole::InitializerCell;
        let facade = self.facade;
        let initializer_field_role = role_tokens(initializer_field_role, facade);
        let initializer_cell_constructor_role =
            role_tokens(initializer_cell_constructor_role, facade);
        let initializer_nested_constructor_role =
            role_tokens(initializer_nested_constructor_role, facade);
        let initializer_cell_role = role_tokens(initializer_cell_role, facade);
        let mut output = Vec::new();
        for cell in cells {
            let cell_ordinal = take_counter(&mut self.counters.cell)?;
            let constructor_ordinal = take_counter(&mut self.counters.constructor)?;
            let marker = cell_marker_function(cell.name());
            let field = quote! {
                #facade::HostCellReference {
                    key: #facade::ProvenanceKey::new(#initializer_field_role, #cell_ordinal),
                    cell: #facade::HostCellIdentity {
                        owner: #facade::HostTypeKey(__krs_type_key::<#owner>),
                        field: #facade::HostTypeKey(#owner::#marker),
                    },
                }
            };
            let content = match cell.content() {
                InitializerCellContent::Leaf {
                    constructor,
                    value,
                    computation,
                    ..
                } => {
                    if *computation != matches!(value, StateTerm::KSequence(_)) {
                        return Err(syn::Error::new(
                            constructor.span(),
                            "cell wrapper and initializer state family disagree",
                        ));
                    }
                    let wrapper = if *computation {
                        quote!(#facade::CellWrapper::KCell)
                    } else {
                        quote!(#facade::CellWrapper::Cell)
                    };
                    let value = self.expand_state(value)?;
                    quote! {
                        #facade::ProtocolInitializerCellContent::Leaf {
                            constructor_key: #facade::ProvenanceKey::new(
                                #initializer_cell_constructor_role, #constructor_ordinal,
                            ),
                            wrapper: #wrapper,
                            value: #value,
                        }
                    }
                }
                InitializerCellContent::Nested {
                    constructor,
                    children,
                } => {
                    let path = call_site_path(constructor)?;
                    let authored = spelling(constructor);
                    let declaration = quote! {
                        #facade::HostCellDeclarationReference {
                            key: #facade::ProvenanceKey::new(
                                #initializer_nested_constructor_role, #constructor_ordinal,
                            ),
                            declaration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(__krs_type_key::<#path>),
                                authored_path: #authored.to_owned(),
                            },
                        }
                    };
                    let children = self.expand_cells(children, &quote!(#path))?;
                    quote! {
                        #facade::ProtocolInitializerCellContent::Nested {
                            declaration: #declaration,
                            children: ::std::vec![#(#children),*],
                        }
                    }
                }
            };
            let facade = self.facade;
            output.push(quote! {
                #facade::HostInitializerCell {
                    key: #facade::ProvenanceKey::new(#initializer_cell_role, #cell_ordinal),
                    field: #field,
                    content: #content,
                }
            });
        }
        Ok(output)
    }

    fn expand_state(&mut self, state: &StateTerm) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match state {
            StateTerm::Term(term) => {
                let term = self.expand_term(term, None)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::Term(#term)))
            }
            StateTerm::KSequence(sequence) => {
                let sequence = self.expand_k(sequence)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::KSequence(#sequence)))
            }
            StateTerm::Map(map) => {
                let map = self.expand_map(map)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::Map(#map)))
            }
        }
    }

    fn expand_k(&mut self, sequence: &KSequence) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if sequence_has_role(sequence, ProvenanceRole::KSequencePayload)? {
            let ordinal = take_counter(&mut self.counters.k_payload)?;
            option_key(facade, ProvenanceRole::KSequencePayload, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            option_key(facade, ProvenanceRole::KSequenceTail, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let notation = k_notation(facade, sequence.notation());
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            let structural = provenance_key(facade, ProvenanceRole::KSequenceItem, ordinal);
            let value = self.expand_term(item, Some(structural.clone()))?;
            items.push(quote! {
                #facade::ProtocolKSequenceItem { key: #structural, value: #value }
            });
        }
        Ok(quote! {
            #facade::ProtocolKSequence {
                payload_key: #payload_key,
                dot_k_key: #dot_k_key,
                notation: #notation,
                items: ::std::vec![#(#items),*],
            }
        })
    }

    fn expand_map(&mut self, map: &MapExpression) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if map_has_role(map, ProvenanceRole::MapPayload)? {
            let ordinal = take_counter(&mut self.counters.map_payload)?;
            option_key(facade, ProvenanceRole::MapPayload, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => quote! {
                #facade::ProtocolMapBody::Empty { explicit_dot: #explicit_dot }
            },
            MapBody::Items { items, .. } => {
                let mut output = Vec::new();
                for item in items {
                    let key_ordinal = take_counter(&mut self.counters.map_key)?;
                    let value_ordinal = take_counter(&mut self.counters.map_value)?;
                    let key_key = provenance_key(facade, ProvenanceRole::MapKey, key_ordinal);
                    let value_key = provenance_key(facade, ProvenanceRole::MapValue, value_ordinal);
                    let key = self.expand_term(item.key(), Some(key_key.clone()))?;
                    let value = self.expand_term(item.value(), Some(value_key.clone()))?;
                    output.push(quote! {
                        #facade::ProtocolMapItem {
                            key_key: #key_key, key: #key,
                            value_key: #value_key, value: #value,
                        }
                    });
                }
                quote!(#facade::ProtocolMapBody::Items { items: ::std::vec![#(#output),*] })
            }
            MapBody::Update { base, key, value } => {
                let base_ordinal = take_counter(&mut self.counters.map_update_base)?;
                let key_ordinal = take_counter(&mut self.counters.map_key)?;
                let value_ordinal = take_counter(&mut self.counters.map_value)?;
                let base_key = provenance_key(facade, ProvenanceRole::MapUpdateBase, base_ordinal);
                let key_key = provenance_key(facade, ProvenanceRole::MapKey, key_ordinal);
                let value_key = provenance_key(facade, ProvenanceRole::MapValue, value_ordinal);
                let base = self.expand_term(base, Some(base_key.clone()))?;
                let key = self.expand_term(key, Some(key_key.clone()))?;
                let value = self.expand_term(value, Some(value_key.clone()))?;
                quote! {
                    #facade::ProtocolMapBody::Update {
                        base_key: #base_key, base: #base,
                        key_key: #key_key, key: #key,
                        value_key: #value_key, value: #value,
                    }
                }
            }
        };
        Ok(quote!(#facade::ProtocolMap { payload_key: #payload_key, body: #body }))
    }

    fn expand_term(
        &mut self,
        term: &TermExpression,
        structural_key: Option<TokenStream>,
    ) -> syn::Result<TokenStream> {
        let ordinal = take_counter(&mut self.counters.term)?;
        let key = provenance_key(self.facade, ProvenanceRole::InitializerTerm, ordinal);
        let structural = structural_key.unwrap_or_else(|| key.clone());
        let term = self.expand_term_tree(term.tree(), &structural)?;
        let facade = self.facade;
        Ok(quote!(#facade::ProtocolInitializerTerm { key: #key, term: #term }))
    }

    fn expand_term_tree(
        &mut self,
        tree: &TermTree,
        structural_key: &TokenStream,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = provenance_key(facade, ProvenanceRole::InitializerTermPath, ordinal);
                let target = self.terms.application_target(application.head())?;
                let TermArguments::Positional(values) = application.arguments() else {
                    return Err(syn::Error::new(
                        application.head().span(),
                        "initializer terms cannot use named record arguments",
                    ));
                };
                let arguments = values
                    .iter()
                    .map(|value| {
                        self.expand_term_tree(value, structural_key).map(|value| {
                            quote! {
                                #facade::HostTermArgument::Positional {
                                    value: ::std::boxed::Box::new(#value),
                                }
                            }
                        })
                    })
                    .collect::<syn::Result<Vec<_>>>()?;
                Ok(quote! {
                    #facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::Applied,
                        reference: #facade::HostApplicationReference { key: #key, target: #target },
                        path_key: #key,
                        arguments: ::std::vec![#(#arguments),*],
                    }
                })
            }
            TermTree::Reference(path) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = provenance_key(facade, ProvenanceRole::InitializerTermPath, ordinal);
                let name = spelling(path);
                if is_bound_ident_path(path, self.bindings) {
                    Ok(quote!(#facade::HostTerm::Variable {
                        key: #key, path_key: #key, name: #name.to_owned(),
                    }))
                } else {
                    let target = self.terms.application_target(path)?;
                    Ok(quote!(#facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::BareReference,
                        reference: #facade::HostApplicationReference { key: #key, target: #target },
                        path_key: #key,
                        arguments: ::std::vec![],
                    }))
                }
            }
            TermTree::Literal(literal) => {
                let literal = literal_tokens(facade, literal);
                Ok(quote!(#facade::HostTerm::Literal { key: #structural_key, literal: #literal }))
            }
            TermTree::Wildcard(_) => Err(syn::Error::new(
                Span::call_site(),
                "initializer terms cannot contain wildcards",
            )),
            TermTree::IdToken { .. }
            | TermTree::BytesToken { .. }
            | TermTree::Anonymous { .. }
            | TermTree::OrBool { .. } => Err(syn::Error::new(
                Span::call_site(),
                "claim-only terms cannot occur in initializers",
            )),
            TermTree::Cell(cell) => Err(syn::Error::new(
                cell.owner().span(),
                "fragment! is not an initializer term; construct nested initializer cells directly",
            )),
        }
    }
}
