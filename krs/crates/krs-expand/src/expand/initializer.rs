//! Configuration initializers: `#[k::init]`.

use crate::ExpandError;
use krs_diagnostic::codes::{self, expand};
use krs_ir::wire::{
    WireCellDeclarationReference, WireCellIdentity, WireCellReference,
    WireConfigurationInitializer, WireConfigurationVariable, WireInitializerCell,
    WireSortReference, WireTerm, WireTypeReference,
};
use krs_ir::{
    CellWrapper, DescriptorKSequenceNotation, ProtocolInitializerCellContent,
    ProtocolInitializerStateTerm, ProtocolInitializerTerm, ProtocolKSequence,
    ProtocolKSequenceItem, ProtocolMap, ProtocolMapBody, ProtocolMapItem,
};
use krs_syntax::KrsSyntax;
use krs_syntax::positions::Form;
use krs_syntax::{
    FixedCellInitializer, InitializerCellContent, KSequence, KSequenceNotation, MapBody,
    MapExpression, StateTerm, TermExpression, TermNode, TermTree,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Attribute, FnArg, Ident, Path, parse_quote};

use super::configuration::{
    SortArgumentContext, cell_marker_function, configuration_sort_arguments,
};
use super::island_checks::initializer_state_island_import_checks;
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::terms::{KeyedTerm, TermBuilder, TermSide, WireSlots};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, sort_type_tokens, spelling,
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
        pub(crate) fn __krs_initializer_payload<R>(
            _configuration: impl ::core::ops::FnOnce(&'static str, #facade::__KrsSlots<'_>) -> R,
        ) -> ::core::result::Result<(R, #facade::HostProvenance), #facade::HostProvenanceError> {
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
    krs_syntax::InitAttribute::parse_tokens(attributes)?;
    let initializer = krs_syntax::InitializerFunction::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let anchors = initializer.provenance()?;
    let fallback = krs_syntax::TokenRange::for_tokens(initializer.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    // The initializer's declaration key is its wire node's own.
    let ledger = KeyLedger::new(&anchors, &[]);

    let bindings = initializer
        .variables()
        .iter()
        .map(|variable| variable.binding().clone())
        .collect::<Vec<_>>();
    let cfg = call_site_cfg_attributes(&initializer.item().attrs)?;
    let nonce = expansion_nonce(env, "initializer", &initializer.item().sig.ident, fallback);
    let mut builder = InitializerBuilder::new(&facade, &ledger, nonce, &cfg, &bindings);
    let mut variables = Vec::new();
    let self_type = Ident::new("Self", Span::call_site());
    let arguments_key = format_ident!("initializer_variable_{nonce:016x}");
    let mut argument_ordinal = 0;
    for (index, variable) in initializer.variables().iter().enumerate() {
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
        let binding = variable.binding().unraw().to_string();
        let external_name = variable.attribute().name().value();
        let main_key = variable
            .attribute()
            .is_main()
            .then(|| ledger.define(variable.main_key()))
            .transpose()?;
        let authored = spelling(variable.sort());
        let arguments = configuration_sort_arguments(
            variable.arguments(),
            &mut SortArgumentContext {
                facade: &facade,
                ledger: &ledger,
                owner: &self_type,
                owner_key: &arguments_key,
                cfg: &cfg,
                helpers: &mut builder.key_functions,
                slots: &mut builder.slots,
                ordinal: &mut argument_ordinal,
            },
        )?;
        variables.push(WireConfigurationVariable {
            binding_key: ledger.define(variable.key())?,
            binding,
            external_name_key: ledger.define(variable.name_key())?,
            external_name,
            sort: WireSortReference {
                key: ledger.define(variable.type_key())?,
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
        key: ledger.define(initializer.declaration_key())?,
        owner_key: ledger.define(initializer.result_type_key())?,
        owner: WireTypeReference {
            slot: builder
                .slots
                .type_slot(quote!(#facade::HostTypeKey(__krs_type_key::<Self>))),
            authored_path: "Self".to_owned(),
        },
        variables,
        body_key: ledger.define(initializer.body_key())?,
        cells,
    };
    ledger.finish()?;
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

        // The configuration's factory decodes the initializer inside this
        // body: the slot table holds the values the lexical witnesses
        // compute here, which live only as long as this body's expression.
        #(#cfg)*
        #[doc(hidden)]
        pub(crate) fn __krs_initializer_payload<R>(
            __krs_configuration: impl ::core::ops::FnOnce(&'static str, #facade::__KrsSlots<'_>) -> R,
        ) -> ::core::result::Result<(R, #facade::HostProvenance), #facade::HostProvenanceError> {
            let _krs_path_check = || {
                #(#island_import_checks)*
            };
            fn __krs_type_key<T: ?Sized + 'static>() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<T>()
            }
            ::core::result::Result::Ok((__krs_configuration(#wire, #slots), #provenance))
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

/// Expands an initializer's cells, `k!` sequences and maps, handing every
/// term they hold to the term walker at an initializer's value, whose names
/// are the initializer's parameters.
struct InitializerBuilder<'a> {
    facade: &'a Path,
    terms: TermBuilder<'a>,
    key_functions: Vec<TokenStream>,
    slots: WireSlots,
}

impl<'a> InitializerBuilder<'a> {
    fn new(
        facade: &'a Path,
        ledger: &'a KeyLedger<'a>,
        nonce: u64,
        cfg: &'a [Attribute],
        bindings: &'a [Ident],
    ) -> Self {
        Self {
            facade,
            terms: TermBuilder::new(facade, ledger, nonce, cfg, bindings, Form::Initializer)
                .with_associated_keys(),
            key_functions: Vec::new(),
            slots: WireSlots::new(facade),
        }
    }

    fn expand_cells(
        &mut self,
        cells: &[FixedCellInitializer],
        owner: &TokenStream,
    ) -> crate::Result<Vec<WireInitializerCell>> {
        let facade = self.facade;
        let ledger = self.terms.ledger;
        let mut output = Vec::new();
        for cell in cells {
            let marker = cell_marker_function(cell.name());
            let field = WireCellReference {
                key: ledger.define(cell.field_key())?,
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
                        constructor_key: ledger.define(cell.constructor_key())?,
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
                        key: ledger.define(cell.constructor_key())?,
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
                key: ledger.define(cell.key())?,
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
                let term = self.expand_term(term)?;
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
        let ledger = self.terms.ledger;
        // Every shell has its payload key: an empty one is anchored at
        // its invocation.
        let payload_key = ledger.define(sequence.payload_key())?;
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            Some(ledger.define(sequence.tail_key())?)
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
            let key = ledger.define(item.keys().payload())?;
            let value = self.expand_term(item)?;
            items.push(ProtocolKSequenceItem { key, value });
        }
        // `..pgm` after the items would denote `items ~> $PGM`, the
        // variable's sequence after them. An initializer's `k!` lists its
        // items and takes no remainder, so the remainder is refused where it
        // is written rather than dropped; a configuration variable of an
        // item sort is written as an item.
        if let Some(range) = sequence.tail().range() {
            return Err(ExpandError::at_range(
                codes::syntax::UNSUPPORTED_INITIALIZER_BODY,
                range,
                "unsupported declarative initializer body: an initializer's `k!` lists its items and takes no remainder; write a configuration variable of an item sort as an item, as in `k::k![Cmd::Go(), pgm]`",
            ));
        }
        Ok(ProtocolKSequence {
            payload_key,
            dot_k_key,
            notation,
            items,
        })
    }

    fn expand_map(&mut self, map: &MapExpression) -> crate::Result<ProtocolMap<WireTerm>> {
        let ledger = self.terms.ledger;
        // Every shell has its payload key: an empty one is anchored at
        // its invocation.
        let payload_key = ledger.define(map.payload_key())?;
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => ProtocolMapBody::Empty {
                explicit_dot: *explicit_dot,
            },
            MapBody::Items { items, remainder } => {
                let mut output = Vec::new();
                for item in items {
                    let key_key = ledger.define(item.key().keys().payload())?;
                    let value_key = ledger.define(item.value().keys().payload())?;
                    let key = self.expand_term(item.key())?;
                    let value = self.expand_term(item.value())?;
                    output.push(ProtocolMapItem {
                        key_key,
                        key,
                        value_key,
                        value,
                    });
                }
                // `..m` after the items would denote the items joined with
                // the variable's map, a join that is undefined when the two
                // share a key, which only a run would find. An initializer's
                // `map!` lists its items and takes no remainder, so the
                // remainder is refused where it is written rather than
                // dropped.
                if let Some(range) = remainder.range() {
                    return Err(ExpandError::at_range(
                        codes::syntax::UNSUPPORTED_INITIALIZER_BODY,
                        range,
                        "unsupported declarative initializer body: an initializer's `map!` takes no remainder, since joining its items with another map is undefined when the two share a key, which only a run would find; list the map's items",
                    ));
                }
                ProtocolMapBody::Items { items: output }
            }
            MapBody::Update { base, key, value } => {
                let base_key = ledger.define(base.keys().payload())?;
                let key_key = ledger.define(key.keys().payload())?;
                let value_key = ledger.define(value.keys().payload())?;
                let base = self.expand_term(base)?;
                let key = self.expand_term(key)?;
                let value = self.expand_term(value)?;
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
    ) -> crate::Result<ProtocolInitializerTerm<WireTerm>> {
        let key = self.terms.ledger.define(term.keys().term())?;
        let term = self
            .terms
            .expand_wire(KeyedTerm::of(term), TermSide::Right, &mut self.slots)?;
        Ok(ProtocolInitializerTerm { key, term })
    }
}
