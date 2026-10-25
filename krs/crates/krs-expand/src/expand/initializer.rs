//! Configuration initializers: `#[k::init]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::bytes_token;
use krs_ir::wire::{
    WireApplicationReference, WireCellDeclarationReference, WireCellIdentity, WireCellReference,
    WireConfigurationInitializer, WireConfigurationVariable, WireInitializerCell,
    WireSortReference, WireTerm, WireTypeReference,
};
use krs_ir::{
    BuiltinSort, CellWrapper, DescriptorApplicationHeadClass, DescriptorKSequenceNotation,
    ProductionFieldId, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
    ProtocolInitializerTerm, ProtocolKSequence, ProtocolKSequenceItem, ProtocolMap,
    ProtocolMapBody, ProtocolMapItem, ProvenanceKey,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{
    FixedCellInitializer, InitializerCellContent, KSequence, KSequenceNotation, MapBody,
    MapExpression, ProvenanceRole, StateTerm, TermArguments, TermExpression, TermNode, TermTree,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, FnArg, Ident, Path, parse_quote};

use super::configuration::{
    SortArgumentContext, cell_marker_function, configuration_sort_arguments,
};
use super::island_checks::initializer_state_island_import_checks;
use super::nonce::expansion_nonce;
use super::terms::{TermBuilder, WireSlots, wire_key};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, sort_type_tokens, spelling,
    take_counter, wire_literal,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn init(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let stand_in = initializer_stand_in(env, &item);
    init_inner(env, attributes, item).map_err(|error| error.with_stand_in(stand_in))
}

/// The payload function a failed `#[k::init]` leaves in place of its expansion.
/// The configuration's descriptor factory names `__krs_initializer_payload`, so
/// without it rustc would add an error about a generated name to the KRS
/// diagnostics. It has the success path's signature and the method's `#[cfg]`
/// attributes, and it never runs: the diagnostics' `compile_error!` stops the build.
/// The author's method is not re-emitted, since rustc would then check the body
/// KRS just rejected.
fn initializer_stand_in(env: &dyn MacroEnvironment, item: &TokenStream) -> TokenStream {
    let Ok(facade) = env.facade_path() else {
        return TokenStream::new();
    };
    let cfg = syn::parse2::<syn::ImplItemFn>(item.clone())
        .ok()
        .and_then(|method| call_site_cfg_attributes(&method.attrs).ok())
        .unwrap_or_default();
    quote! {
        #(#cfg)*
        #[doc(hidden)]
        pub(crate) fn __krs_initializer_payload() -> ::core::result::Result<(
            &'static str,
            #facade::__KrsSlots<'static>,
            #facade::HostProvenance,
        ), #facade::HostProvenanceError> {
            ::core::unreachable!("a failed `#[k::init]` expansion has no payload")
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "Initializer metadata and the replacement method are emitted together."
)]
fn init_inner(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
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
    let self_type = Ident::new("Self", Span::call_site());
    let arguments_key = format_ident!("initializer_variable_{nonce:016x}");
    let mut argument_ordinal = 0;
    for (index, variable) in initializer.variables().iter().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                variable.binding().span(),
                "too many variables",
            )
        })?;
        let sort_path = call_site_path(variable.sort())?;
        let sort_type = variable.optional_term_sort().map_or_else(
            || quote!(#sort_path),
            |term_sort| sort_type_tokens(&facade, &sort_path, term_sort.is_dynamic()),
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
        let main_key = variable
            .attribute()
            .is_main()
            .then_some(wire_key(configuration_variable_main_role, ordinal));
        let authored = spelling(variable.sort());
        let arguments = configuration_sort_arguments(
            variable.arguments(),
            &mut SortArgumentContext {
                facade: &facade,
                owner: &self_type,
                owner_key: &arguments_key,
                cfg: &cfg,
                role: ProvenanceRole::ConfigurationVariableTypeArgument,
                helpers: &mut builder.key_functions,
                slots: &mut builder.slots,
                ordinal: &mut argument_ordinal,
            },
        )?;
        variables.push(WireConfigurationVariable {
            binding_key: wire_key(configuration_variable_role, ordinal),
            binding,
            external_name_key: wire_key(configuration_variable_name_role, ordinal),
            external_name,
            sort: WireSortReference {
                key: wire_key(configuration_variable_type_role, ordinal),
                target: WireTypeReference {
                    slot: builder
                        .slots
                        .type_slot(quote!(#facade::HostTypeKey(Self::#sort_key))),
                    authored_path: authored,
                },
            },
            arguments,
            main_key,
        });
    }
    let cells = builder.expand_cells(initializer.cells(), &quote!(Self))?;
    let island_import_checks = initializer_state_island_import_checks(initializer.cells());
    builder
        .key_functions
        .append(&mut builder.terms.key_functions);
    let wire = WireConfigurationInitializer {
        key: wire_key(initializer_declaration_role, 0),
        owner_key: wire_key(initializer_result_type_role, 0),
        owner: WireTypeReference {
            slot: builder
                .slots
                .type_slot(quote!(#facade::HostTypeKey(__krs_type_key::<Self>))),
            authored_path: "Self".to_owned(),
        },
        variables,
        body_key: wire_key(initializer_body_role, 0),
        cells,
    };
    let wire = serde_json::to_string(&wire).expect("initializer wire is serializable");
    let slots = builder.slots.tokens();
    let key_functions = builder.key_functions;

    // The shared parser has validated every parameter attribute as the sole `config_var` helper.
    // The outer proc macro consumes it so stable rustc sees an ordinary associated method signature.
    let mut method = initializer.item().clone();
    for input in &mut method.sig.inputs {
        if let FnArg::Typed(parameter) = input {
            parameter.attrs.clear();
        }
    }
    inject_inferred_initializer_wrappers(&mut method, &initializer, &facade, &bindings)?;
    method.attrs.push(parse_quote!(
        #[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
    ));

    Ok(quote! {
        #method

        #(#key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        pub(crate) fn __krs_initializer_payload() -> ::core::result::Result<(
            &'static str,
            #facade::__KrsSlots<'static>,
            #facade::HostProvenance,
        ), #facade::HostProvenanceError> {
            let _krs_path_check = || {
                #(#island_import_checks)*
            };
            fn __krs_type_key<T: ?Sized + 'static>() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<T>()
            }
            ::core::result::Result::Ok((#wire, #slots, #provenance))
        }
    })
}

fn inject_inferred_initializer_wrappers(
    method: &mut syn::ImplItemFn,
    initializer: &krs_syntax::InitializerFunction,
    facade: &Path,
    bindings: &[Ident],
) -> crate::Result<()> {
    let [syn::Stmt::Expr(syn::Expr::Struct(body), None)] = method.block.stmts.as_mut_slice() else {
        return Err(ExpandError::new(
            expand::INITIALIZER_BODY_SHAPE,
            method.block.span(),
            "a fixed initializer must contain exactly one struct expression",
        ));
    };
    inject_initializer_cell_list(body, initializer.cells(), facade, bindings)
}

fn inject_initializer_cell_list(
    body: &mut syn::ExprStruct,
    cells: &[FixedCellInitializer],
    facade: &Path,
    bindings: &[Ident],
) -> crate::Result<()> {
    for cell in cells {
        let Some(field) = body
            .fields
            .iter_mut()
            .find(|field| matches!(&field.member, syn::Member::Named(name) if name == cell.name()))
        else {
            return Err(ExpandError::new(
                expand::MISSING_CHECKED_FIELD,
                cell.name().span(),
                "initializer field disappeared during wrapper injection",
            ));
        };
        // `Some(template)` of an optional cell: the template takes the wrapper
        // (KF-023, R7).
        let expression = if cell.is_optional() {
            match &mut field.expr {
                syn::Expr::Call(call) if call.args.len() == 1 => {
                    call.args.first_mut().expect("`Some(..)` has one argument")
                }
                other => {
                    return Err(ExpandError::new(
                        expand::INITIALIZER_CELL_SHAPE,
                        other.span(),
                        "an optional cell's initializer is `Some(template)`",
                    ));
                }
            }
        } else {
            &mut field.expr
        };
        let has_colon = field.colon_token.is_some();
        inject_initializer_value(expression, cell, facade, bindings)?;
        if !has_colon {
            field.colon_token = Some(syn::token::Colon::default());
        }
    }
    Ok(())
}

fn inject_initializer_value(
    expression: &mut syn::Expr,
    cell: &FixedCellInitializer,
    facade: &Path,
    bindings: &[Ident],
) -> crate::Result<()> {
    match cell.content() {
        InitializerCellContent::Leaf {
            value,
            computation,
            inferred_constructor: true,
            ..
        } => {
            let value = initializer_value_stand_in(expression, value, facade, bindings);
            *expression = if *computation {
                parse_quote!(#facade::configuration::KCell::new(#value))
            } else {
                parse_quote!(#facade::configuration::Cell::new(#value))
            };
        }
        InitializerCellContent::Leaf {
            value,
            inferred_constructor: false,
            ..
        } => {
            if let syn::Expr::Call(call) = expression
                && let Some(argument) = call.args.first_mut()
            {
                *argument = initializer_value_stand_in(argument, value, facade, bindings);
            }
        }
        InitializerCellContent::Nested { children, .. } => {
            let syn::Expr::Struct(nested) = expression else {
                return Err(ExpandError::new(
                    expand::INITIALIZER_CELL_SHAPE,
                    expression.span(),
                    "a nested fixed-cell initializer must be a struct expression",
                ));
            };
            inject_initializer_cell_list(nested, children, facade, bindings)?;
        }
    }
    Ok(())
}

/// What rustc sees of a leaf cell's value in the re-emitted method.
///
/// A configuration variable that is the cell's whole content stays, so rustc
/// checks that its Rust type is the cell's. Any other value is a KRS term
/// (a literal, constructor, function application, `k!`, `map!`), whose names
/// the payload's slots resolve and whose sorts KRS checks; as a Rust
/// expression it is not checkable (a struct variant cannot be called, a KRS
/// function is a Rust struct), so it becomes `__term()`, preceded by a use of
/// each configuration variable it names, at the authored token: the term the
/// payload carries uses them.
fn initializer_value_stand_in(
    expression: &syn::Expr,
    value: &StateTerm,
    facade: &Path,
    bindings: &[Ident],
) -> syn::Expr {
    if let StateTerm::Term(term) = value
        && let TermTree::Reference(path) = term.tree()
        && is_bound_ident_path(path, bindings)
    {
        return expression.clone();
    }
    let uses = value
        .terms()
        .into_iter()
        .flat_map(TermExpression::nodes)
        .filter_map(|node| match node {
            TermNode::Reference(path) if is_bound_ident_path(path, bindings) => Some(path),
            _ => None,
        })
        .collect::<Vec<_>>();
    if uses.is_empty() {
        parse_quote!(#facade::configuration::__term())
    } else {
        parse_quote!({
            #(let _ = &#uses;)*
            #facade::configuration::__term()
        })
    }
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
    id_token: u32,
    bytes_token: u32,
    record_field: u32,
}

struct InitializerBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    counters: InitializerCounters,
    terms: TermBuilder<'a>,
    key_functions: Vec<TokenStream>,
    slots: WireSlots,
}

impl<'a> InitializerBuilder<'a> {
    fn new(facade: &'a Path, nonce: u64, cfg: &'a [Attribute], bindings: &'a [Ident]) -> Self {
        Self {
            facade,
            bindings,
            counters: InitializerCounters::default(),
            terms: TermBuilder::new(facade, nonce, cfg, bindings)
                .with_associated_keys()
                .without_application_instances(),
            key_functions: Vec::new(),
            slots: WireSlots::new(facade),
        }
    }

    fn expand_cells(
        &mut self,
        cells: &[FixedCellInitializer],
        owner: &TokenStream,
    ) -> crate::Result<Vec<WireInitializerCell>> {
        let initializer_field_role = ProvenanceRole::InitializerField;
        let initializer_cell_constructor_role = ProvenanceRole::InitializerCellConstructor;
        let initializer_nested_constructor_role = ProvenanceRole::InitializerNestedConstructor;
        let initializer_cell_role = ProvenanceRole::InitializerCell;
        let facade = self.facade;
        let mut output = Vec::new();
        for cell in cells {
            let cell_ordinal = take_counter(&mut self.counters.cell)?;
            let constructor_ordinal = take_counter(&mut self.counters.constructor)?;
            let marker = cell_marker_function(cell.name());
            let field = WireCellReference {
                key: wire_key(initializer_field_role, cell_ordinal),
                cell: WireCellIdentity {
                    owner: self
                        .slots
                        .type_slot(quote!(#facade::HostTypeKey(__krs_type_key::<#owner>))),
                    field: self
                        .slots
                        .type_slot(quote!(#facade::HostTypeKey(#owner::#marker))),
                },
            };
            let content = match cell.content() {
                InitializerCellContent::Leaf {
                    constructor,
                    value,
                    computation,
                    ..
                } => {
                    if *computation != matches!(value, StateTerm::KSequence(_)) {
                        return Err(ExpandError::new(
                            expand::CELL_STATE_FAMILY_MISMATCH,
                            constructor.span(),
                            "cell wrapper and initializer state family disagree",
                        ));
                    }
                    let wrapper = if *computation {
                        CellWrapper::KCell
                    } else {
                        CellWrapper::Cell
                    };
                    let value = self.expand_state(value)?;
                    ProtocolInitializerCellContent::Leaf {
                        constructor_key: wire_key(
                            initializer_cell_constructor_role,
                            constructor_ordinal,
                        ),
                        wrapper,
                        value,
                    }
                }
                InitializerCellContent::Nested {
                    constructor,
                    children,
                } => {
                    let path = call_site_path(constructor)?;
                    let authored = spelling(constructor);
                    let declaration = WireCellDeclarationReference {
                        key: wire_key(initializer_nested_constructor_role, constructor_ordinal),
                        declaration: WireTypeReference {
                            slot: self
                                .slots
                                .type_slot(quote!(#facade::HostTypeKey(__krs_type_key::<#path>))),
                            authored_path: authored,
                        },
                    };
                    let children = self.expand_cells(children, &quote!(#path))?;
                    ProtocolInitializerCellContent::Nested {
                        declaration,
                        children,
                    }
                }
            };
            output.push(WireInitializerCell {
                key: wire_key(initializer_cell_role, cell_ordinal),
                field,
                content,
            });
        }
        Ok(output)
    }

    fn expand_state(
        &mut self,
        state: &StateTerm,
    ) -> crate::Result<ProtocolInitializerStateTerm<WireTerm>> {
        match state {
            StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_) => {
                unreachable!("initializers hold templates only")
            }
            StateTerm::Term(term) | StateTerm::Group(term) => {
                let term = self.expand_term(term, None)?;
                Ok(ProtocolInitializerStateTerm::Term(term))
            }
            StateTerm::KSequence(sequence) => {
                let sequence = self.expand_k(sequence)?;
                Ok(ProtocolInitializerStateTerm::KSequence(sequence))
            }
            StateTerm::Map(map) => {
                let map = self.expand_map(map)?;
                Ok(ProtocolInitializerStateTerm::Map(map))
            }
        }
    }

    fn expand_k(&mut self, sequence: &KSequence) -> crate::Result<ProtocolKSequence<WireTerm>> {
        let payload_key = if sequence.payload_key().is_some() {
            let ordinal = take_counter(&mut self.counters.k_payload)?;
            Some(wire_key(ProvenanceRole::KSequencePayload, ordinal))
        } else {
            None
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            Some(wire_key(ProvenanceRole::KSequenceTail, ordinal))
        } else {
            None
        };
        let notation = match sequence.notation() {
            KSequenceNotation::Comma => DescriptorKSequenceNotation::Comma,
            KSequenceNotation::Operator => DescriptorKSequenceNotation::Operator,
            KSequenceNotation::DotK => DescriptorKSequenceNotation::DotK,
        };
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            let structural = wire_key(ProvenanceRole::KSequenceItem, ordinal);
            let value = self.expand_term(item, Some(structural.clone()))?;
            items.push(ProtocolKSequenceItem {
                key: structural,
                value,
            });
        }
        Ok(ProtocolKSequence {
            payload_key,
            dot_k_key,
            notation,
            items,
        })
    }

    fn expand_map(&mut self, map: &MapExpression) -> crate::Result<ProtocolMap<WireTerm>> {
        let payload_key = if map.payload_key().is_some() {
            let ordinal = take_counter(&mut self.counters.map_payload)?;
            Some(wire_key(ProvenanceRole::MapPayload, ordinal))
        } else {
            None
        };
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => ProtocolMapBody::Empty {
                explicit_dot: *explicit_dot,
            },
            MapBody::Items { items, .. } => {
                let mut output = Vec::new();
                for item in items {
                    let key_ordinal = take_counter(&mut self.counters.map_key)?;
                    let value_ordinal = take_counter(&mut self.counters.map_value)?;
                    let key_key = wire_key(ProvenanceRole::MapKey, key_ordinal);
                    let value_key = wire_key(ProvenanceRole::MapValue, value_ordinal);
                    let key = self.expand_term(item.key(), Some(key_key.clone()))?;
                    let value = self.expand_term(item.value(), Some(value_key.clone()))?;
                    output.push(ProtocolMapItem {
                        key_key,
                        key,
                        value_key,
                        value,
                    });
                }
                ProtocolMapBody::Items { items: output }
            }
            MapBody::Update { base, key, value } => {
                let base_ordinal = take_counter(&mut self.counters.map_update_base)?;
                let key_ordinal = take_counter(&mut self.counters.map_key)?;
                let value_ordinal = take_counter(&mut self.counters.map_value)?;
                let base_key = wire_key(ProvenanceRole::MapUpdateBase, base_ordinal);
                let key_key = wire_key(ProvenanceRole::MapKey, key_ordinal);
                let value_key = wire_key(ProvenanceRole::MapValue, value_ordinal);
                let base = self.expand_term(base, Some(base_key.clone()))?;
                let key = self.expand_term(key, Some(key_key.clone()))?;
                let value = self.expand_term(value, Some(value_key.clone()))?;
                ProtocolMapBody::Update {
                    base_key,
                    base,
                    key_key,
                    key,
                    value_key,
                    value,
                }
            }
        };
        Ok(ProtocolMap { payload_key, body })
    }

    fn expand_term(
        &mut self,
        term: &TermExpression,
        structural_key: Option<ProvenanceKey>,
    ) -> crate::Result<ProtocolInitializerTerm<WireTerm>> {
        let ordinal = take_counter(&mut self.counters.term)?;
        let key = wire_key(ProvenanceRole::InitializerTerm, ordinal);
        let structural = structural_key.unwrap_or_else(|| key.clone());
        let term = self.expand_term_tree(term.tree(), structural)?;
        Ok(ProtocolInitializerTerm { key, term })
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One exhaustive match over the closed term-tree sum."
    )]
    fn expand_term_tree(
        &mut self,
        tree: &TermTree,
        structural_key: ProvenanceKey,
    ) -> crate::Result<WireTerm> {
        match tree {
            TermTree::Application(application) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = wire_key(ProvenanceRole::InitializerTermPath, ordinal);
                let target = self.terms.application_wire_slot(
                    application.head(),
                    application.is_notation(),
                    &mut self.slots,
                )?;
                let authored_path = spelling(application.head());
                // An initializer admits no turbofish (KF-027); this rejects one.
                self.terms
                    .application_instance_wire(application, &mut self.slots)?;
                if application.update().is_some() || application.is_open() {
                    return Err(ExpandError::new(
                        expand::INITIALIZER_RECORD_UPDATE,
                        application.head().span(),
                        "an initializer term names every field of a record: `..base` takes fields from a matched record and `..` leaves them open, and an initializer matches nothing",
                    ));
                }
                let arguments = match application.arguments() {
                    TermArguments::Positional(values) => krs_ir::Arguments::Positional(
                        values
                            .iter()
                            .map(|value| {
                                self.expand_term_tree(value, structural_key.clone())
                                    .map(Box::new)
                            })
                            .collect::<crate::Result<Vec<_>>>()?,
                    ),
                    // A record constructor denotes the same application as
                    // its positional form, with each field named.
                    TermArguments::Named(values) => {
                        let mut arguments = Vec::with_capacity(values.len());
                        for argument in values {
                            let ordinal = take_counter(&mut self.counters.record_field)?;
                            let field = ProductionFieldId::new(argument.name().to_string())
                                .expect("Rust field identifiers are valid production fields");
                            arguments.push(krs_ir::NamedTermArgument {
                                key: wire_key(ProvenanceRole::InitializerRecordFieldName, ordinal),
                                field,
                                value: Box::new(
                                    self.expand_term_tree(
                                        argument.value(),
                                        structural_key.clone(),
                                    )?,
                                ),
                            });
                        }
                        krs_ir::Arguments::named(arguments)
                    }
                };
                Ok(WireTerm::Application {
                    instance: Vec::new(),
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: WireApplicationReference {
                        key: key.clone(),
                        target,
                        authored_path,
                    },
                    path_key: key,
                    arguments,
                    update: None,
                    open: false,
                })
            }
            TermTree::Reference(path) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = wire_key(ProvenanceRole::InitializerTermPath, ordinal);
                let name = spelling(path);
                if is_bound_ident_path(path, self.bindings) {
                    Ok(WireTerm::Variable {
                        key: key.clone(),
                        path_key: key,
                        name,
                    })
                } else if let Some(name) = super::terms::snake_case_bare_name(path) {
                    // An initializer's bare snake-case names are its
                    // parameters, by KRS's spelling rule never Rust items.
                    Err(ExpandError::new(
                        expand::UNBOUND_NAME,
                        syn::spanned::Spanned::span(path),
                        format!(
                            "`{name}` is not a parameter of this initializer: a bare snake-case name in an initializer term is one of its parameters{}",
                            super::terms::did_you_mean(&name, self.bindings.iter())
                        ),
                    ))
                } else {
                    let target = self
                        .terms
                        .application_wire_slot(path, false, &mut self.slots)?;
                    let authored_path = spelling(path);
                    Ok(WireTerm::Application {
                        instance: Vec::new(),
                        head_class: DescriptorApplicationHeadClass::BareReference,
                        reference: WireApplicationReference {
                            key: key.clone(),
                            target,
                            authored_path,
                        },
                        path_key: key,
                        arguments: krs_ir::Arguments::default(),
                        update: None,
                        open: false,
                    })
                }
            }
            TermTree::Literal(literal) => {
                let literal = wire_literal(literal);
                Ok(WireTerm::Literal {
                    key: structural_key,
                    literal,
                })
            }
            TermTree::Wildcard(range) => Err(ExpandError::at_range(
                expand::INITIALIZER_WILDCARD,
                *range,
                "initializer terms cannot contain wildcards",
            )),
            // A builtin literal is one constant of its sort, in an initializer as anywhere.
            TermTree::IdToken { literal } => {
                let ordinal = take_counter(&mut self.counters.id_token)?;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimIdToken, ordinal),
                    sort: BuiltinSort::Id,
                    value: literal.value(),
                })
            }
            TermTree::BytesToken { literal } => {
                let ordinal = take_counter(&mut self.counters.bytes_token)?;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimBytesToken, ordinal),
                    sort: BuiltinSort::Bytes,
                    value: bytes_token::encode(&literal.value()),
                })
            }
            TermTree::Anonymous { spelling, .. } => Err(ExpandError::new(
                expand::CLAIM_ONLY_TERM,
                spelling.span(),
                "`k::anonymous!` is a claim's symbolic value; an initializer builds the initial configuration from constants and configuration variables",
            )),
            TermTree::OrBool { range, .. } => Err(ExpandError::new(
                expand::CLAIM_ONLY_TERM,
                range.first(),
                "`k::or_bool!` joins a claim's symbolic conditions; an initializer holds no condition",
            )),
            TermTree::Cell(cell) => Err(ExpandError::new(
                expand::INITIALIZER_FRAGMENT,
                cell.owner().span(),
                "fragment! is not an initializer term; construct nested initializer cells directly",
            )),
            TermTree::Lexeme { sort, text } => self.terms.lexeme_wire(sort, text, &mut self.slots),
            TermTree::SortTest { range, .. } => Err(ExpandError::new(
                expand::CLAIM_ONLY_TERM,
                range.first(),
                "is! and project! are rule and claim terms; initializers cannot contain them",
            )),
            TermTree::As { binding, .. } => Err(ExpandError::new(
                expand::PATTERN_AS_OUTSIDE_LHS,
                binding.span(),
                "`name @ pattern` binds only on a left-hand side; initializers cannot contain it",
            )),
            TermTree::Or { range, .. } => Err(ExpandError::new(
                expand::PATTERN_OR_OUTSIDE_LHS,
                range.first(),
                "`A | B` alternatives occur only on a left-hand side; initializers cannot contain them",
            )),
            TermTree::Matches { range, .. } => Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is a rule and claim condition; initializers cannot contain it",
            )),
            TermTree::Let { range, .. } => Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "`let` blocks (K's #let) are rule terms; initializers cannot contain them",
            )),
            TermTree::Closure { range, .. } => Err(ExpandError::new(
                expand::ML_PLACEMENT,
                range.first(),
                "an `ml::exists` closure is a predicate; initializers cannot contain it",
            )),
            TermTree::Rewrite { range, .. } => Err(ExpandError::new(
                expand::LOCAL_REWRITE_OUTSIDE_SUBJECT,
                range.first(),
                "`k::rewrite!` (K's local =>) marks a change in a single-body rule's subject; initializers cannot contain it",
            )),
        }
    }
}
