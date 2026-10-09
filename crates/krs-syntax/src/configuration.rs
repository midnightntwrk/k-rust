use std::collections::BTreeSet;

use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{
    Attribute, Field, Fields, GenericArgument, Ident, ItemStruct, Path, PathArguments, Type,
};

use crate::ReferenceCandidate;
use crate::parse::{KrsSyntax, checked_ordinal};
use crate::path::{is_plain_path, without_last_arguments};
use crate::{
    CellAttributePayload, ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind,
    TokenRange,
};

/// Leaf term content or a nominal nested fixed-cell group.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Span-preserving syn nodes are the public parser contract."
)]
pub enum ConfigurationCellContent {
    /// A `Cell<T>` or `KCell<T>` leaf.
    Leaf {
        /// Cell wrapper path with generic arguments removed.
        wrapper: Path,
        /// Complete authored content type.
        ty: Type,
        /// Outer content-sort path, retaining authored qualification.
        sort: Path,
        /// Generic object-sort arguments carried by the leaf content type.
        arguments: Vec<Path>,
        /// Whether this is the distinguished computation-cell wrapper.
        computation: bool,
        /// Whether the wrapper is inferred from a readable plain field.
        inferred_wrapper: bool,
    },
    /// A field whose type resolves to a `#[k::cell]` struct.
    Nested {
        /// Rust-resolved nested cell declaration path.
        declaration: Path,
    },
}

/// One ordered fixed-cell field in a configuration or nested cell struct.
#[derive(Clone, Debug)]
pub struct FixedCellField {
    field: Field,
    name: Ident,
    emitted_name: String,
    attribute: CellAttributePayload,
    content: ConfigurationCellContent,
    cell_helper_present: bool,
    optional: bool,
}

/// Name of the computation-cell field type in the single-cell configuration surface.
pub type ComputationCellField = FixedCellField;

impl FixedCellField {
    /// Returns the original authored Rust field.
    #[must_use]
    pub const fn field(&self) -> &Field {
        &self.field
    }

    /// Returns the Rust field identifier.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the exact emitted K cell name.
    #[must_use]
    pub fn emitted_name(&self) -> &str {
        &self.emitted_name
    }

    /// Returns classified optional name/color metadata.
    #[must_use]
    pub const fn attribute(&self) -> &CellAttributePayload {
        &self.attribute
    }

    /// Returns leaf or nested content.
    #[must_use]
    pub const fn cell_content(&self) -> &ConfigurationCellContent {
        &self.content
    }

    /// Whether this is an optional (`?`) cell, declared `Option<T>` (KF-023,
    /// R7); its content is that of `T`.
    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }

    /// Returns the leaf wrapper path, or `None` for a nested cell.
    #[must_use]
    pub const fn wrapper(&self) -> Option<&Path> {
        match &self.content {
            ConfigurationCellContent::Leaf { wrapper, .. } => Some(wrapper),
            ConfigurationCellContent::Nested { .. } => None,
        }
    }

    /// Returns the outer leaf content-sort path, or `None` for a nested cell.
    #[must_use]
    pub const fn content(&self) -> Option<&Path> {
        match &self.content {
            ConfigurationCellContent::Leaf { sort, .. } => Some(sort),
            ConfigurationCellContent::Nested { .. } => None,
        }
    }

    /// Whether this leaf uses `KCell`; nested cells return false.
    #[must_use]
    pub const fn is_computation_cell(&self) -> bool {
        matches!(
            self.content,
            ConfigurationCellContent::Leaf {
                computation: true,
                ..
            }
        )
    }

    /// Whether a readable plain field caused its leaf wrapper to be inferred.
    #[must_use]
    pub const fn has_inferred_wrapper(&self) -> bool {
        matches!(
            self.content,
            ConfigurationCellContent::Leaf {
                inferred_wrapper: true,
                ..
            }
        )
    }
}

/// A named, nongeneric fixed configuration or nested fixed-cell declaration.
#[derive(Clone, Debug)]
pub struct ConfigurationDeclaration {
    item: ItemStruct,
    cells: Vec<FixedCellField>,
}

impl ConfigurationDeclaration {
    /// Validates an ordered fixed-cell struct for the fixed-state model.
    ///
    /// # Errors
    ///
    /// Rejects tuple/unit/empty/generic structs, unsupported helpers, malformed
    /// leaves, generic nested groups, and duplicate emitted sibling names.
    pub fn from_item(item: ItemStruct) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() {
            return Err(unsupported_declaration(
                "fixed cell declarations cannot have generic parameters",
                item.generics.params.span(),
            ));
        }
        if let Some(where_clause) = &item.generics.where_clause {
            return Err(unsupported_declaration(
                "fixed cell declarations cannot have a where clause",
                where_clause.span(),
            ));
        }
        let Fields::Named(named) = &item.fields else {
            return Err(unsupported_declaration(
                "a fixed configuration must be a named-field struct",
                item.fields.span(),
            ));
        };
        if named.named.is_empty() {
            return Err(unsupported_declaration(
                "a fixed configuration requires at least one cell",
                named.span(),
            ));
        }

        let explicit_wrapper_surface = named.named.iter().any(|field| {
            matches!(option_content(&field.ty).unwrap_or(&field.ty), Type::Path(path)
            if path.path.segments.last().is_some_and(|segment| {
                matches!(segment.ident.to_string().as_str(), "Cell" | "KCell")
            }))
        });
        if !explicit_wrapper_surface {
            let has_readable_leaf = named
                .named
                .iter()
                .any(|field| field.attrs.iter().any(is_cell_attribute));
            if has_readable_leaf
                && let Some(field) = named
                    .named
                    .iter()
                    .find(|field| !field.attrs.iter().any(is_cell_attribute))
            {
                return Err(unsupported_field(
                    "wrapper-free configurations require `#[k::cell]` on every plain field",
                    field.ty.span(),
                ));
            }
        }
        let mut cells = Vec::with_capacity(named.named.len());
        let mut emitted_names = BTreeSet::new();
        for field in &named.named {
            let parsed = parse_cell_field(field.clone(), !explicit_wrapper_surface)?;
            if !emitted_names.insert(parsed.emitted_name.clone()) {
                return Err(unsupported_field(
                    "two sibling fields cannot emit the same cell name",
                    parsed
                        .attribute
                        .name()
                        .map_or_else(|| parsed.name.span(), syn::LitStr::span),
                ));
            }
            cells.push(parsed);
        }
        if cells.iter().any(FixedCellField::has_inferred_wrapper)
            && let Some(field) = cells.iter().find(|field| !field.cell_helper_present)
        {
            return Err(unsupported_field(
                "wrapper-free configurations require `#[k::cell]` on every plain field",
                field.field.ty.span(),
            ));
        }
        Ok(Self { item, cells })
    }

    /// Returns the original span-preserving Rust struct.
    #[must_use]
    pub const fn item(&self) -> &ItemStruct {
        &self.item
    }

    /// Returns the declaration name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns all top-level fixed cells in authored order.
    #[must_use]
    pub fn cells(&self) -> &[FixedCellField] {
        &self.cells
    }

    /// Returns the first cell for the single-cell configuration surface.
    #[must_use]
    pub fn cell(&self) -> Option<&ComputationCellField> {
        self.cells.first()
    }

    /// Returns deterministic declaration and cell metadata anchors.
    ///
    /// # Errors
    ///
    /// Returns endpoint/ordinal errors only for invalid token metadata.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::ConfigurationDeclaration,
            0,
            TokenRange::for_tokens(&self.item.ident)?,
        )];
        let mut argument_ordinal = 0_usize;
        for (ordinal, cell) in self.cells.iter().enumerate() {
            let ordinal = checked_ordinal(
                ordinal,
                ProvenanceRole::ConfigurationField,
                cell.name.span(),
            )?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationField,
                ordinal,
                TokenRange::for_tokens(&cell.name)?,
            ));
            // Cell-attribute anchors in the payload's order (name, color, multiplicity,
            // type, stream, exit), at this field's ordinal.
            for anchor in cell.attribute.provenance()? {
                anchors.push(ProvenanceAnchor::new(
                    anchor.role(),
                    ordinal,
                    anchor.range(),
                ));
            }
            match &cell.content {
                ConfigurationCellContent::Leaf {
                    wrapper,
                    ty,
                    arguments,
                    inferred_wrapper,
                    ..
                } => {
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::ConfigurationCellWrapper,
                        ordinal,
                        if *inferred_wrapper {
                            TokenRange::for_tokens(ty)?
                        } else {
                            TokenRange::for_tokens(wrapper)?
                        },
                    ));
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::ConfigurationCellContent,
                        ordinal,
                        TokenRange::for_tokens(ty)?,
                    ));
                    for argument in arguments {
                        anchors.push(ProvenanceAnchor::new(
                            ProvenanceRole::ConfigurationCellContentArgument,
                            checked_ordinal(
                                argument_ordinal,
                                ProvenanceRole::ConfigurationField,
                                argument.span(),
                            )?,
                            TokenRange::for_tokens(argument)?,
                        ));
                        argument_ordinal += 1;
                    }
                }
                ConfigurationCellContent::Nested { declaration } => {
                    anchors.push(ProvenanceAnchor::new(
                        ProvenanceRole::ConfigurationCellContent,
                        ordinal,
                        TokenRange::for_tokens(declaration)?,
                    ));
                }
            }
        }
        Ok(anchors)
    }

    /// Returns wrapper/content/nested paths with keys matching [`Self::provenance`].
    #[must_use]
    pub fn reference_candidates(&self) -> Vec<ReferenceCandidate> {
        let mut output = Vec::new();
        let mut argument_ordinal = 0_u32;
        for (ordinal, cell) in self.cells.iter().enumerate() {
            let Ok(ordinal) = u32::try_from(ordinal) else {
                break;
            };
            match &cell.content {
                ConfigurationCellContent::Leaf {
                    wrapper,
                    sort,
                    arguments,
                    inferred_wrapper,
                    ..
                } => {
                    if !inferred_wrapper {
                        output.push(ReferenceCandidate {
                            key: key(ProvenanceRole::ConfigurationCellWrapper, ordinal),
                            path: wrapper.clone(),
                            kind: (),
                        });
                    }
                    output.push(ReferenceCandidate {
                        key: key(ProvenanceRole::ConfigurationCellContent, ordinal),
                        path: sort.clone(),
                        kind: (),
                    });
                    for argument in arguments {
                        output.push(ReferenceCandidate {
                            key: key(
                                ProvenanceRole::ConfigurationCellContentArgument,
                                argument_ordinal,
                            ),
                            path: argument.clone(),
                            kind: (),
                        });
                        let Some(next) = argument_ordinal.checked_add(1) else {
                            break;
                        };
                        argument_ordinal = next;
                    }
                }
                ConfigurationCellContent::Nested { declaration } => {
                    output.push(ReferenceCandidate {
                        key: key(ProvenanceRole::ConfigurationCellContent, ordinal),
                        path: declaration.clone(),
                        kind: (),
                    });
                }
            }
        }
        output
    }
}

impl KrsSyntax for ConfigurationDeclaration {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2::<ItemStruct>(tokens)?)
    }
}

fn parse_cell_field(field: Field, infer_plain_leaf: bool) -> Result<FixedCellField, SyntaxError> {
    let name = field
        .ident
        .clone()
        .ok_or_else(|| unsupported_field("fixed cells require named Rust fields", field.span()))?;
    let (attribute, cell_helper_present) = parse_cell_helper(&field.attrs)?;
    let emitted_name = attribute
        .name()
        .map_or_else(|| name.unraw().to_string(), syn::LitStr::value);
    let optional = attribute
        .multiplicity()
        .is_some_and(|multiplicity| multiplicity.value() == "?");
    let ty = match (option_content(&field.ty), optional) {
        (Some(content), true) => content,
        (None, false) => &field.ty,
        (Some(_), false) => {
            return Err(unsupported_field(
                "an Option field is an optional cell: add `multiplicity = \"?\"` to its `#[k::cell(..)]`",
                field.ty.span(),
            ));
        }
        (None, true) => {
            return Err(unsupported_field(
                "a `multiplicity = \"?\"` cell is declared `Option<T>`, T its leaf sort or nested cell struct",
                field.ty.span(),
            ));
        }
    };
    let content = parse_cell_type(
        ty,
        cell_helper_present && infer_plain_leaf && !attribute.is_nested(),
    )?;
    Ok(FixedCellField {
        field,
        name,
        emitted_name,
        attribute,
        content,
        cell_helper_present,
        optional,
    })
}

/// The `T` of a field typed `Option<T>`, the declared type of an optional
/// (`?`) cell (KF-023, R7).
#[must_use]
pub fn option_content(ty: &Type) -> Option<&Type> {
    let Type::Path(path) = ty else {
        return None;
    };
    if path.qself.is_some() {
        return None;
    }
    let last = path.path.segments.last()?;
    let prelude = path.path.segments.len() == 1
        || path
            .path
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .ends_with(&["option".to_owned(), "Option".to_owned()]);
    if last.ident != "Option" || !prelude {
        return None;
    }
    let PathArguments::AngleBracketed(arguments) = &last.arguments else {
        return None;
    };
    match arguments.args.iter().collect::<Vec<_>>().as_slice() {
        [GenericArgument::Type(content)] => Some(content),
        _ => None,
    }
}

fn parse_cell_helper(
    attributes: &[Attribute],
) -> Result<(CellAttributePayload, bool), SyntaxError> {
    let mut helpers = attributes
        .iter()
        .filter(|attribute| is_cell_attribute(attribute));
    let Some(attribute) = helpers.next() else {
        return Ok((CellAttributePayload::default(), false));
    };
    if let Some(repeated) = helpers.next() {
        return Err(unsupported_field(
            "a cell field accepts at most one `#[k::cell(...)]` helper",
            repeated.span(),
        ));
    }
    let parsed = match &attribute.meta {
        syn::Meta::Path(_) => Ok(CellAttributePayload::default()),
        syn::Meta::List(list) => CellAttributePayload::parse_tokens(list.tokens.clone()),
        syn::Meta::NameValue(value) => Err(unsupported_field(
            "`cell` metadata uses `#[k::cell(...)]` arguments",
            value.span(),
        )),
    }?;
    Ok((parsed, true))
}

fn parse_cell_type(
    ty: &Type,
    cell_helper_present: bool,
) -> Result<ConfigurationCellContent, SyntaxError> {
    let Type::Path(type_path) = ty else {
        return Err(unsupported_field(
            "cell fields require a Rust type path",
            ty.span(),
        ));
    };
    let (true, Some(last)) = (type_path.qself.is_none(), type_path.path.segments.last()) else {
        return Err(unsupported_field(
            "cell fields require a plain type path",
            ty.span(),
        ));
    };
    let computation = last.ident == "KCell";
    if last.ident == "Cell" || computation {
        let PathArguments::AngleBracketed(arguments) = &last.arguments else {
            return Err(unsupported_field(
                "`Cell` and `KCell` require exactly one content type",
                last.span(),
            ));
        };
        if arguments.args.len() != 1 {
            return Err(unsupported_field(
                "`Cell` and `KCell` require exactly one content type",
                arguments.span(),
            ));
        }
        let Some(GenericArgument::Type(content_ty @ Type::Path(content_path))) =
            arguments.args.first()
        else {
            return Err(unsupported_field(
                "cell content must be a Rust type path",
                arguments.span(),
            ));
        };
        if content_path.qself.is_some() || content_path.path.segments.is_empty() {
            return Err(unsupported_field(
                "cell content must be a Rust type path",
                content_path.span(),
            ));
        }
        let sort = without_last_arguments(&content_path.path);
        if !is_plain_path(&sort) {
            return Err(unsupported_field(
                "the outer cell content sort must be a plain Rust path",
                sort.span(),
            ));
        }
        if computation
            && sort
                .segments
                .last()
                .is_none_or(|segment| segment.ident != "KSequence")
        {
            return Err(unsupported_field(
                "`KCell` content must be builtin `KSequence`",
                content_ty.span(),
            ));
        }
        let wrapper = without_last_arguments(&type_path.path);
        if !is_plain_path(&wrapper) {
            return Err(unsupported_field(
                "cell wrappers must be plain paths",
                wrapper.span(),
            ));
        }
        return Ok(ConfigurationCellContent::Leaf {
            wrapper,
            ty: content_ty.clone(),
            sort,
            arguments: content_sort_arguments(content_ty),
            computation,
            inferred_wrapper: false,
        });
    }
    let computation = last.ident == "KSequence";
    if cell_helper_present {
        return parse_inferred_leaf(ty, type_path, computation);
    }
    parse_nested_cell(ty, type_path, computation)
}

fn parse_nested_cell(
    ty: &Type,
    type_path: &syn::TypePath,
    computation: bool,
) -> Result<ConfigurationCellContent, SyntaxError> {
    if computation {
        return Err(unsupported_field(
            "plain leaf fields require a `#[k::cell]` helper",
            ty.span(),
        ));
    }
    if !is_plain_path(&type_path.path) {
        return Err(unsupported_field(
            "nested fixed-cell declarations cannot have generic arguments",
            type_path.span(),
        ));
    }
    Ok(ConfigurationCellContent::Nested {
        declaration: type_path.path.clone(),
    })
}

fn parse_inferred_leaf(
    ty: &Type,
    type_path: &syn::TypePath,
    computation: bool,
) -> Result<ConfigurationCellContent, SyntaxError> {
    let sort = without_last_arguments(&type_path.path);
    if !is_plain_path(&sort) {
        return Err(unsupported_field(
            "the outer cell content sort must be a plain Rust path",
            sort.span(),
        ));
    }
    let wrapper = Path::from(Ident::new(
        if computation { "KCell" } else { "Cell" },
        ty.span(),
    ));
    Ok(ConfigurationCellContent::Leaf {
        wrapper,
        ty: ty.clone(),
        sort,
        arguments: content_sort_arguments(ty),
        computation,
        inferred_wrapper: true,
    })
}

fn content_sort_arguments(ty: &Type) -> Vec<Path> {
    let Type::Path(type_path) = ty else {
        return Vec::new();
    };
    let Some(last) = type_path.path.segments.last() else {
        return Vec::new();
    };
    let PathArguments::AngleBracketed(arguments) = &last.arguments else {
        return Vec::new();
    };
    let mut output = Vec::new();
    for argument in &arguments.args {
        let GenericArgument::Type(Type::Path(path)) = argument else {
            return Vec::new();
        };
        if path.qself.is_some() {
            return Vec::new();
        }
        let candidate = path.path.clone();
        if candidate
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "Term")
        {
            // Reference-surface `Term<dyn Sort>` arguments are already
            // represented by the explicit rule binders they feed. Layer-1
            // aliases are the inference-bearing form retained here.
            return Vec::new();
        }
        if is_plain_path(&candidate) {
            output.push(candidate);
        } else {
            return Vec::new();
        }
    }
    output
}

fn is_cell_attribute(attribute: &Attribute) -> bool {
    is_plain_path(attribute.path())
        && attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "cell")
}

fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
}

fn unsupported_declaration(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedConfigurationDeclaration { reason },
        span,
    )
}

fn unsupported_field(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedConfigurationField { reason },
        span,
    )
}
