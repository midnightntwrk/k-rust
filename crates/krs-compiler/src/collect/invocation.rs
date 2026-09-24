//! Reparsing of authored KRS attribute invocations and comparison with host payloads.

use std::collections::BTreeMap;

use krs_ir::{HostDescriptorPayload, ProvenanceKey, RustVisibility, StableItemId};
use krs_syntax::surface::{AttributeMacro, FunctionMacro};
use krs_syntax::{
    ConfigurationDeclaration, ConstructorDeclaration, EnumConstructorDeclaration,
    InitializerFunction, ProvenanceAnchor, ProvenanceRole, RuleItem, SortDeclaration, SortsEntry,
    StateClaimItem, StateContextAliasItem, StateRuleItem, SubsortDeclaration, TokenDeclaration,
    TokenRange, parse_alias_attribute, parse_associativity_declaration, parse_bracket_attribute,
    parse_claim_attribute, parse_configuration_attribute, parse_constructor_attribute,
    parse_constructors_attribute, parse_equation_attribute, parse_function_attribute,
    parse_init_attribute, parse_precedence_declaration, parse_priority_attribute,
    parse_rule_attribute, parse_rule_block, parse_seqstrict_attribute,
    parse_simplification_attribute, parse_sort_attribute, parse_sorts_declaration,
    parse_strict_attribute, parse_subsort_attribute, parse_symbol_attribute, parse_token_attribute,
};
use proc_macro2::TokenStream;
use syn::{Attribute, ImplItem, Item, Meta};

use super::provenance::{Coordinates, token_coordinates};
use super::{display_item, path_spelling};
use crate::facade::AttributeResolver;
use crate::{CollectionError, CollectionErrorKind};

#[derive(Clone, Debug)]
pub(super) struct ParsedInvocation {
    pub(super) primary: ProvenanceKey,
    pub(super) item_name: String,
    pub(super) anchors: BTreeMap<ProvenanceKey, Coordinates>,
    payload: ParsedInvocationPayload,
    pub(super) visibility: RustVisibility,
    pub(super) explicit_symbol: Option<krs_ir::ExplicitSymbol>,
}

#[derive(Clone, Debug)]
enum ParsedInvocationPayload {
    Declaration,
    Rule {
        bindings: Vec<String>,
    },
    HeadRule {
        bindings: Vec<String>,
        lhs: String,
        result_kind: String,
        extras: Vec<(String, String)>,
    },
    Configuration,
}

#[allow(clippy::too_many_lines)]
pub(super) fn collect_invocations(
    items: &[Item],
    resolver: &AttributeResolver<'_>,
    output: &mut Vec<ParsedInvocation>,
) -> Result<(), CollectionError> {
    let resolver = &resolver.scoped(items);
    for item in items {
        if let Item::Trait(syn::ItemTrait { attrs, .. })
        | Item::Struct(syn::ItemStruct { attrs, .. })
        | Item::Enum(syn::ItemEnum { attrs, .. })
        | Item::Fn(syn::ItemFn { attrs, .. })
        | Item::Impl(syn::ItemImpl { attrs, .. }) = item
        {
            resolver.check(attrs)?;
        }
        match item {
            Item::Trait(item_trait) => {
                let (sort_visibility, sort_symbol) = declaration_metadata(
                    resolver,
                    &item_trait.vis,
                    &item_trait.attrs,
                    AttributeMacro::Sort,
                )?;
                for attribute in item_trait
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Sort))
                {
                    let sort_attribute = parse_sort_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration =
                        SortDeclaration::from_item(item_trait.clone()).map_err(source_syntax)?;
                    if sort_attribute.is_reference()
                        && sort_attribute.parents().len() != declaration.parents().len()
                    {
                        return Err(CollectionError::new(
                            CollectionErrorKind::SourceSyntax,
                            "a reference sort must materialize one semantic parent path for each Rust marker supertrait",
                        ));
                    }
                    let mut anchors = if let Some(alias) = sort_attribute.alias() {
                        let mut anchors = vec![ProvenanceAnchor::new(
                            ProvenanceRole::SortDeclaration,
                            0,
                            TokenRange::for_tokens(alias).map_err(source_syntax)?,
                        )];
                        for (ordinal, parent) in sort_attribute.parents().iter().enumerate() {
                            let ordinal = u32::try_from(ordinal).map_err(|_| {
                                CollectionError::new(
                                    CollectionErrorKind::SourceSyntax,
                                    "reference sort has too many semantic parents",
                                )
                            })?;
                            anchors.push(ProvenanceAnchor::new(
                                ProvenanceRole::SortParent,
                                ordinal,
                                TokenRange::for_tokens(parent).map_err(source_syntax)?,
                            ));
                        }
                        anchors
                    } else {
                        declaration.provenance().map_err(source_syntax)?
                    };
                    if let Some(symbol) = &sort_symbol {
                        anchors.extend(symbol.provenance().map_err(source_syntax)?);
                    }
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::SortDeclaration,
                            sort_attribute
                                .alias()
                                .map_or_else(|| item_trait.ident.to_string(), ToString::to_string),
                            anchors,
                            ParsedInvocationPayload::Declaration,
                        )?,
                        sort_visibility.clone(),
                        sort_symbol.as_ref(),
                    ));
                }
                for attribute in item_trait
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Bracket))
                {
                    let bracket = parse_bracket_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let sort_attribute = item_trait
                        .attrs
                        .iter()
                        .find(|candidate| resolver.invokes(candidate, AttributeMacro::Sort))
                        .map(|candidate| {
                            parse_sort_attribute(attribute_tokens(candidate)?)
                                .map_err(source_syntax)
                        })
                        .transpose()?;
                    let semantic_name = sort_attribute.as_ref().map_or_else(
                        || item_trait.ident.to_string(),
                        |parsed| {
                            parsed
                                .alias()
                                .map_or_else(|| item_trait.ident.to_string(), ToString::to_string)
                        },
                    );
                    let mut anchors = bracket.provenance().map_err(source_syntax)?;
                    let semantic_anchor = sort_attribute
                        .as_ref()
                        .and_then(krs_syntax::SortAttribute::alias)
                        .map_or_else(
                            || TokenRange::for_tokens(&item_trait.ident),
                            TokenRange::for_tokens,
                        )
                        .map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::SortDeclaration,
                        0,
                        semantic_anchor,
                    ));
                    output.push(parsed_invocation(
                        ProvenanceRole::BracketDeclaration,
                        semantic_name,
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Struct(item_struct) => {
                let (constructor_visibility, constructor_symbol) = declaration_metadata(
                    resolver,
                    &item_struct.vis,
                    &item_struct.attrs,
                    AttributeMacro::Constructor,
                )?;
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Function))
                {
                    let parsed = parse_function_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConstructorDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    parsed
                        .production()
                        .validate_declaration(&declaration)
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.production().provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    let mut grammar_anchors = parsed.provenance().map_err(source_syntax)?;
                    grammar_anchors.extend(declaration.full_provenance().map_err(source_syntax)?);
                    if parsed.is_total() {
                        grammar_anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::FunctionDeclaration,
                            0,
                            TokenRange::for_tokens(&item_struct.ident).map_err(source_syntax)?,
                        ));
                    }
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorSort,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorDeclaration,
                        item_struct.ident.to_string(),
                        grammar_anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Constructor))
                {
                    let parsed = parse_constructor_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConstructorDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    let mut grammar_anchors = parsed.full_provenance().map_err(source_syntax)?;
                    grammar_anchors.extend(declaration.full_provenance().map_err(source_syntax)?);
                    if let Some(symbol) = &constructor_symbol {
                        let symbol_anchors = symbol.provenance().map_err(source_syntax)?;
                        anchors.extend(symbol_anchors.clone());
                        grammar_anchors.extend(symbol_anchors);
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Alias))
                    {
                        parse_alias_attribute(attribute_tokens(helper)?).map_err(source_syntax)?;
                        let marker = helper
                            .path()
                            .segments
                            .last()
                            .expect("named attributes have a final path segment");
                        grammar_anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::AliasProduction,
                            0,
                            TokenRange::for_tokens(&marker.ident).map_err(source_syntax)?,
                        ));
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Strict))
                    {
                        grammar_anchors.extend(
                            parse_strict_attribute(attribute_tokens(helper)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    for helper in item_struct
                        .attrs
                        .iter()
                        .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Seqstrict))
                    {
                        grammar_anchors.extend(
                            parse_seqstrict_attribute(attribute_tokens(helper)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::ConstructorSort,
                            item_struct.ident.to_string(),
                            anchors.clone(),
                            ParsedInvocationPayload::Declaration,
                        )?,
                        constructor_visibility.clone(),
                        constructor_symbol.as_ref(),
                    ));
                    output.push(with_declaration_metadata(
                        parsed_invocation(
                            ProvenanceRole::ConstructorDeclaration,
                            item_struct.ident.to_string(),
                            grammar_anchors,
                            ParsedInvocationPayload::Declaration,
                        )?,
                        constructor_visibility.clone(),
                        constructor_symbol.as_ref(),
                    ));
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Token))
                {
                    let token_attribute = parse_token_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let token =
                        TokenDeclaration::from_item(item_struct.clone()).map_err(source_syntax)?;
                    let mut anchors = token_attribute.provenance().map_err(source_syntax)?;
                    anchors.extend(token.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::SortDeclaration,
                        item_struct.ident.to_string(),
                        vec![ProvenanceAnchor::new(
                            ProvenanceRole::SortDeclaration,
                            0,
                            TokenRange::for_tokens(token.name()).map_err(source_syntax)?,
                        )],
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::TokenDeclaration,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Configuration))
                {
                    let parsed = parse_configuration_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let declaration = ConfigurationDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.extend(declaration.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConfigurationDeclaration,
                        item_struct.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Configuration,
                    )?);
                }
                for _attribute in item_struct
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Cell))
                {
                    let declaration = ConfigurationDeclaration::from_item(item_struct.clone())
                        .map_err(source_syntax)?;
                    output.push(parsed_invocation(
                        ProvenanceRole::ConfigurationDeclaration,
                        item_struct.ident.to_string(),
                        declaration.provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Enum(item_enum)
                if item_enum
                    .attrs
                    .iter()
                    .any(|attribute| resolver.invokes(attribute, AttributeMacro::Constructors)) =>
            {
                let invoking = item_enum
                    .attrs
                    .iter()
                    .find(|attribute| resolver.invokes(attribute, AttributeMacro::Constructors))
                    .expect("the match guard found a constructors attribute");
                let attribute = parse_constructors_attribute(attribute_tokens(invoking)?)
                    .map_err(source_syntax)?;
                let mut reparsed = item_enum.clone();
                reparsed
                    .attrs
                    .retain(|attribute| !resolver.invokes(attribute, AttributeMacro::Constructors));
                let declaration = EnumConstructorDeclaration::from_parts(&attribute, reparsed)
                    .map_err(source_syntax)?;
                if !declaration.is_open_family() {
                    output.push(parsed_invocation(
                        ProvenanceRole::SortDeclaration,
                        declaration.sort_name().to_string(),
                        declaration.sort_provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::SubsortDeclaration,
                        declaration.sort_name().to_string(),
                        declaration.membership_provenance().map_err(source_syntax)?,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for variant in declaration.variants() {
                    let anchors = declaration
                        .variant_provenance(variant)
                        .map_err(source_syntax)?;
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorSort,
                        variant.name().to_string(),
                        anchors.clone(),
                        ParsedInvocationPayload::Declaration,
                    )?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ConstructorDeclaration,
                        variant.name().to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                if let Some(anchors) = declaration.precedence_provenance().map_err(source_syntax)? {
                    output.push(parsed_invocation(
                        ProvenanceRole::PrecedenceDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                if let Some(anchors) = declaration
                    .associativity_provenance()
                    .map_err(source_syntax)?
                {
                    output.push(parsed_invocation(
                        ProvenanceRole::AssociativityDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
            }
            Item::Fn(item_fn) => {
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Claim))
                {
                    let parsed = parse_claim_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let claim =
                        StateClaimItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let mut anchors = claim.provenance().map_err(source_syntax)?;
                    anchors.extend(parsed.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ClaimDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::ContextAlias))
                {
                    let parsed =
                        krs_syntax::parse_context_alias_attribute(attribute_tokens(attribute)?)
                            .map_err(source_syntax)?;
                    let alias = StateContextAliasItem::from_item(item_fn.clone(), parsed.here())
                        .map_err(source_syntax)?;
                    let mut anchors = parsed.provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::ContextAliasDeclaration,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    anchors.extend(alias.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::ContextAliasDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Simplification))
                {
                    let parsed = parse_simplification_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let mut anchors = rule.full_provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::SimplificationMarker,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    anchors.extend(parsed.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule { bindings },
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Equation))
                {
                    parse_equation_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let mut anchors = rule.full_provenance().map_err(source_syntax)?;
                    for priority in item_fn
                        .attrs
                        .iter()
                        .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Priority))
                    {
                        anchors.extend(
                            parse_priority_attribute(attribute_tokens(priority)?)
                                .map_err(source_syntax)?
                                .provenance()
                                .map_err(source_syntax)?,
                        );
                    }
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule { bindings },
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Alias))
                {
                    parse_alias_attribute(attribute_tokens(attribute)?).map_err(source_syntax)?;
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let mut anchors = rule.full_provenance().map_err(source_syntax)?;
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::AliasClause,
                        0,
                        TokenRange::for_tokens(&item_fn.sig.ident).map_err(source_syntax)?,
                    ));
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule { bindings },
                    )?);
                }
                for attribute in item_fn
                    .attrs
                    .iter()
                    .filter(|attr| resolver.invokes(attr, AttributeMacro::Rule))
                {
                    let rule_attribute = parse_rule_attribute(attribute_tokens(attribute)?)
                        .map_err(source_syntax)?;
                    if let Ok(rule) = StateRuleItem::from_item(item_fn.clone()) {
                        let mut anchors = rule.provenance().map_err(source_syntax)?;
                        anchors.extend(rule_attribute.provenance().map_err(source_syntax)?);
                        output.push(parsed_invocation(
                            ProvenanceRole::RuleDeclaration,
                            item_fn.sig.ident.to_string(),
                            anchors,
                            ParsedInvocationPayload::Declaration,
                        )?);
                        continue;
                    }
                    let rule = RuleItem::from_item(item_fn.clone()).map_err(source_syntax)?;
                    let bindings = rule
                        .parameter()
                        .pattern
                        .bindings()
                        .iter()
                        .map(ToString::to_string)
                        .collect();
                    let mut anchors = rule.full_provenance().map_err(source_syntax)?;
                    anchors.extend(rule_attribute.provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        item_fn.sig.ident.to_string(),
                        anchors,
                        ParsedInvocationPayload::Rule { bindings },
                    )?);
                }
            }
            Item::Impl(item_impl) => {
                for attribute in item_impl
                    .attrs
                    .iter()
                    .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Subsort))
                {
                    let mut reparsed_item = item_impl.clone();
                    reparsed_item
                        .attrs
                        .retain(|candidate| !resolver.invokes(candidate, AttributeMacro::Subsort));
                    let declaration =
                        SubsortDeclaration::from_item(reparsed_item).map_err(source_syntax)?;
                    let tokens = attribute_tokens(attribute)?;
                    let anchors = if tokens.is_empty() {
                        declaration.provenance().map_err(source_syntax)?
                    } else {
                        let reference = parse_subsort_attribute(tokens).map_err(source_syntax)?;
                        vec![
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortDeclaration,
                                0,
                                TokenRange::for_tokens(declaration.item())
                                    .map_err(source_syntax)?,
                            ),
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortSuperSort,
                                0,
                                TokenRange::for_tokens(reference.sort()).map_err(source_syntax)?,
                            ),
                            ProvenanceAnchor::new(
                                ProvenanceRole::SubsortSubSort,
                                0,
                                TokenRange::for_tokens(declaration.sub_sort())
                                    .map_err(source_syntax)?,
                            ),
                        ]
                    };
                    output.push(parsed_invocation(
                        ProvenanceRole::SubsortDeclaration,
                        String::new(),
                        anchors,
                        ParsedInvocationPayload::Declaration,
                    )?);
                }
                for implementation_item in &item_impl.items {
                    let ImplItem::Fn(method) = implementation_item else {
                        continue;
                    };
                    resolver.check(&method.attrs)?;
                    for attribute in method
                        .attrs
                        .iter()
                        .filter(|attribute| resolver.invokes(attribute, AttributeMacro::Init))
                    {
                        parse_init_attribute(attribute_tokens(attribute)?)
                            .map_err(source_syntax)?;
                        let mut method = method.clone();
                        method
                            .attrs
                            .retain(|attribute| !resolver.invokes(attribute, AttributeMacro::Init));
                        let initializer =
                            InitializerFunction::from_item(method).map_err(source_syntax)?;
                        output.push(parsed_invocation(
                            ProvenanceRole::InitializerDeclaration,
                            initializer.item().sig.ident.to_string(),
                            initializer.provenance().map_err(source_syntax)?,
                            ParsedInvocationPayload::Declaration,
                        )?);
                    }
                }
            }
            Item::Macro(item_macro)
                if resolver.resolve_macro(&item_macro.mac.path) == Some(FunctionMacro::Rules) =>
            {
                let block =
                    parse_rule_block(item_macro.mac.tokens.clone()).map_err(source_syntax)?;
                for clause in block.clauses() {
                    let rule = clause.rule();
                    let bindings = clause.bindings().iter().map(ToString::to_string).collect();
                    let extras = clause
                        .extras()
                        .iter()
                        .map(|extra| match extra {
                            krs_syntax::RuleExtra::HaveMap { cell, .. } => {
                                ("have".to_owned(), cell.to_string())
                            }
                            krs_syntax::RuleExtra::UpdateMap { cell, .. } => {
                                ("update".to_owned(), cell.to_string())
                            }
                            krs_syntax::RuleExtra::RewriteCell { cell, .. } => {
                                ("rewrite".to_owned(), cell.to_string())
                            }
                        })
                        .collect();
                    let mut anchors = clause.provenance().map_err(source_syntax)?;
                    anchors.extend(clause.attribute().provenance().map_err(source_syntax)?);
                    output.push(parsed_invocation(
                        ProvenanceRole::RuleDeclaration,
                        rule.item()
                            .sig
                            .ident
                            .to_string()
                            .trim_start_matches("r#")
                            .to_owned(),
                        anchors,
                        ParsedInvocationPayload::HeadRule {
                            bindings,
                            lhs: rule.parameter().pattern.spelling(),
                            result_kind: match clause.head_result() {
                                krs_syntax::RuleHeadResult::Replace(_) => "replace",
                                krs_syntax::RuleHeadResult::Splice { .. } => "splice",
                                krs_syntax::RuleHeadResult::Erase(_) => "erase",
                            }
                            .to_owned(),
                            extras,
                        },
                    )?);
                }
            }
            Item::Macro(item_macro)
                if matches!(
                    resolver.resolve_macro(&item_macro.mac.path),
                    Some(FunctionMacro::Sorts | FunctionMacro::FrameworkSorts)
                ) =>
            {
                let declaration = parse_sorts_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                for entry in declaration.entries() {
                    match entry {
                        SortsEntry::Sort(sort) => {
                            output.push(with_visibility(
                                parsed_invocation(
                                    ProvenanceRole::SortDeclaration,
                                    sort.name().to_string(),
                                    sort.provenance().map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?,
                                RustVisibility::Public,
                            ));
                            for bracket in sort.brackets() {
                                output.push(parsed_invocation(
                                    ProvenanceRole::BracketDeclaration,
                                    sort.name().to_string(),
                                    sort.bracket_provenance(bracket).map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?);
                            }
                        }
                        SortsEntry::Membership(membership) => {
                            for member in membership.members() {
                                output.push(parsed_invocation(
                                    ProvenanceRole::SubsortDeclaration,
                                    String::new(),
                                    membership
                                        .member_provenance(member)
                                        .map_err(source_syntax)?,
                                    ParsedInvocationPayload::Declaration,
                                )?);
                            }
                        }
                    }
                }
            }
            Item::Macro(item_macro)
                if resolver.resolve_macro(&item_macro.mac.path)
                    == Some(FunctionMacro::Precedence) =>
            {
                let declaration = parse_precedence_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                output.push(parsed_invocation(
                    ProvenanceRole::PrecedenceDeclaration,
                    String::new(),
                    declaration.provenance().map_err(source_syntax)?,
                    ParsedInvocationPayload::Declaration,
                )?);
            }
            Item::Macro(item_macro)
                if resolver.resolve_macro(&item_macro.mac.path)
                    == Some(FunctionMacro::Associativity) =>
            {
                let declaration = parse_associativity_declaration(item_macro.mac.tokens.clone())
                    .map_err(source_syntax)?;
                output.push(parsed_invocation(
                    ProvenanceRole::AssociativityDeclaration,
                    String::new(),
                    declaration.provenance().map_err(source_syntax)?,
                    ParsedInvocationPayload::Declaration,
                )?);
            }
            Item::Mod(module) => {
                if let Some((_, nested)) = &module.content {
                    collect_invocations(nested, resolver, output)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn with_visibility(
    mut invocation: ParsedInvocation,
    visibility: RustVisibility,
) -> ParsedInvocation {
    invocation.visibility = visibility;
    invocation
}

fn parsed_invocation(
    primary_role: ProvenanceRole,
    item_name: String,
    anchors: Vec<ProvenanceAnchor>,
    payload: ParsedInvocationPayload,
) -> Result<ParsedInvocation, CollectionError> {
    let primary = primary_role.key(0).map_err(|error| {
        CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!("invalid shared-parser provenance key: {error}"),
        )
    })?;
    let parsed = parsed_anchor_map(anchors)?;
    Ok(ParsedInvocation {
        primary,
        item_name,
        anchors: parsed,
        payload,
        visibility: RustVisibility::Inherited,
        explicit_symbol: None,
    })
}

fn parsed_anchor_map(
    anchors: Vec<ProvenanceAnchor>,
) -> Result<BTreeMap<ProvenanceKey, Coordinates>, CollectionError> {
    let mut parsed = BTreeMap::new();
    for anchor in anchors {
        let key = anchor.key().map_err(|error| {
            CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                format!("invalid shared-parser provenance key: {error}"),
            )
        })?;
        let coordinates = token_coordinates(anchor.range())?;
        if parsed.insert(key.clone(), coordinates).is_some() {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                format!(
                    "shared parser repeated provenance key `{}`#{}",
                    key.role(),
                    key.ordinal()
                ),
            ));
        }
    }
    Ok(parsed)
}

#[allow(clippy::match_same_arms, clippy::too_many_lines)]
pub(super) fn validate_reparsed_payload(
    payload: &HostDescriptorPayload,
    invocation: &ParsedInvocation,
    id: &StableItemId,
) -> Result<(), CollectionError> {
    match (payload, &invocation.payload) {
        (
            HostDescriptorPayload::Sort(_)
            | HostDescriptorPayload::Constructor(_)
            | HostDescriptorPayload::Grammar(_)
            | HostDescriptorPayload::Cell(_)
            | HostDescriptorPayload::ConfigurationRule(_)
            | HostDescriptorPayload::ContextAlias(_),
            ParsedInvocationPayload::Declaration,
        ) => Ok(()),
        (HostDescriptorPayload::FixedConfiguration(_), ParsedInvocationPayload::Configuration) => {
            Ok(())
        }
        (
            HostDescriptorPayload::HeadRule(rule),
            ParsedInvocationPayload::HeadRule {
                bindings,
                lhs,
                result_kind,
                extras,
            },
        ) => {
            let host_bindings = rule
                .bindings
                .iter()
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>();
            let host_extras = rule
                .extras
                .iter()
                .map(|extra| match extra {
                    krs_ir::ProtocolHeadRuleExtra::HaveMap { cell, .. } => {
                        ("have".to_owned(), cell.name.clone())
                    }
                    krs_ir::ProtocolHeadRuleExtra::UpdateMap { cell, .. } => {
                        ("update".to_owned(), cell.name.clone())
                    }
                    krs_ir::ProtocolHeadRuleExtra::RewriteCell { cell, .. } => {
                        ("rewrite".to_owned(), cell.name.clone())
                    }
                })
                .collect::<Vec<_>>();
            let host_rhs = match &rule.result {
                krs_ir::ProtocolHeadRuleResult::Replace(_) => "replace",
                krs_ir::ProtocolHeadRuleResult::Splice(_) => "splice",
                krs_ir::ProtocolHeadRuleResult::Erase => "erase",
            };
            if host_bindings != *bindings
                || host_extras != *extras
                || host_rhs != result_kind
                || lhs.trim().is_empty()
            {
                return Err(provenance_mismatch(id, "head-anchored rule structure"));
            }
            Ok(())
        }
        (
            HostDescriptorPayload::StructuredRule(rule),
            ParsedInvocationPayload::Rule { bindings, .. },
        ) if rule.bindings == *bindings => Ok(()),
        (HostDescriptorPayload::StructuredRule(_), ParsedInvocationPayload::Rule { .. }) => {
            Err(provenance_mismatch(id, "authored structured-rule bindings"))
        }
        _ => Err(CollectionError::new(
            CollectionErrorKind::ProvenanceMismatch,
            format!(
                "reparsed source for `{}` has a different KRS declaration kind",
                display_item(id)
            ),
        )),
    }
}

fn provenance_mismatch(id: &StableItemId, field: &str) -> CollectionError {
    CollectionError::new(
        CollectionErrorKind::ProvenanceMismatch,
        format!(
            "macro and shared parser disagree about {field} for `{}`",
            display_item(id)
        ),
    )
}

fn attribute_tokens(attribute: &Attribute) -> Result<TokenStream, CollectionError> {
    match &attribute.meta {
        Meta::Path(_) => Ok(TokenStream::new()),
        Meta::List(list) => Ok(list.tokens.clone()),
        Meta::NameValue(_) => Err(CollectionError::new(
            CollectionErrorKind::SourceSyntax,
            format!(
                "KRS attribute `{}` must use path or list syntax",
                path_spelling(attribute.path())
            ),
        )),
    }
}

pub(super) fn declaration_metadata(
    resolver: &AttributeResolver<'_>,
    visibility: &syn::Visibility,
    attributes: &[Attribute],
    target: AttributeMacro,
) -> Result<(RustVisibility, Option<krs_syntax::SymbolAttribute>), CollectionError> {
    let visibility = match visibility {
        syn::Visibility::Inherited => RustVisibility::Inherited,
        syn::Visibility::Public(_) => RustVisibility::Public,
        syn::Visibility::Restricted(restricted) => {
            let path = path_spelling(&restricted.path).replace(' ', "");
            RustVisibility::restricted(path, restricted.in_token.is_some()).map_err(|error| {
                CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!("invalid Rust declaration visibility: {error}"),
                )
            })?
        }
    };
    let symbols = attributes
        .iter()
        .enumerate()
        .filter(|(_, attribute)| resolver.invokes(attribute, AttributeMacro::Symbol))
        .collect::<Vec<_>>();
    let target_name = target.name();
    let symbol_spelling = symbols.first().map_or_else(
        || "#[k::symbol]".to_owned(),
        |(_, attribute)| format!("#[{}]", path_spelling(attribute.path())),
    );
    let target_spelling = symbols
        .first()
        .and_then(|(_, attribute)| attribute.path().segments.first())
        .map_or_else(
            || format!("#[k::{target_name}]"),
            |alias| format!("#[{}::{target_name}]", alias.ident),
        );
    let symbol = match symbols.as_slice() {
        [] => None,
        [(symbol_index, symbol)] => {
            let targets = attributes
                .iter()
                .enumerate()
                .filter(|(_, attribute)| resolver.invokes(attribute, target))
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            let [target_index] = targets.as_slice() else {
                return Err(CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!(
                        "{symbol_spelling} requires exactly one {target_spelling} target on its declaration"
                    ),
                ));
            };
            if symbol_index.checked_add(1) != Some(*target_index) {
                return Err(CollectionError::new(
                    CollectionErrorKind::SourceSyntax,
                    format!(
                        "{symbol_spelling} must immediately precede {target_spelling} so attribute order is unambiguous"
                    ),
                ));
            }
            Some(parse_symbol_attribute(attribute_tokens(symbol)?).map_err(source_syntax)?)
        }
        _ => {
            return Err(CollectionError::new(
                CollectionErrorKind::SourceSyntax,
                format!("a declaration may carry only one {symbol_spelling} attribute"),
            ));
        }
    };
    Ok((visibility, symbol))
}

fn with_declaration_metadata(
    mut invocation: ParsedInvocation,
    visibility: RustVisibility,
    symbol: Option<&krs_syntax::SymbolAttribute>,
) -> ParsedInvocation {
    invocation.visibility = visibility;
    invocation.explicit_symbol = symbol.map(|symbol| symbol.value().clone());
    invocation
}

#[allow(clippy::needless_pass_by_value)]
fn source_syntax(error: krs_syntax::SyntaxError) -> CollectionError {
    source_syntax_at(error, 0)
}

#[allow(clippy::needless_pass_by_value)]
pub(super) fn source_syntax_at(
    error: krs_syntax::SyntaxError,
    byte_offset: usize,
) -> CollectionError {
    let range = error.source_range().and_then(|range| {
        Some((
            byte_offset.checked_add(range.start())?,
            byte_offset.checked_add(range.end())?,
        ))
    });
    let detail = range.map_or_else(
        || format!("shared KRS source parser rejected authored source: {error}"),
        |(start, end)| {
            format!(
                "shared KRS source parser rejected authored source at bytes {start}..{end}: {error}"
            )
        },
    );
    CollectionError::new(CollectionErrorKind::SourceSyntax, detail)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::facade::FacadeAliases;

    #[test]
    fn framework_catalogue_entry_collects_the_two_readable_sorts() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("../krs/Cargo.toml");
        let facade = FacadeAliases::from_manifest(&manifest).unwrap();
        let resolver = AttributeResolver::new(&facade, "src/lib.rs");
        let source: syn::File = syn::parse_quote! {
            use krs_macros::__framework_sorts;
            crate::__framework_sorts! {
                KItem;
                KResult: KItem;
            }
        };
        let mut invocations = Vec::new();
        collect_invocations(&source.items, &resolver, &mut invocations).unwrap();
        assert_eq!(
            invocations
                .iter()
                .map(|invocation| (invocation.primary.role(), invocation.item_name.as_str()))
                .collect::<Vec<_>>(),
            [
                ("sort_declaration", "KItem"),
                ("sort_declaration", "KResult")
            ],
        );
    }
}
