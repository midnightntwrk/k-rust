use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, ExprCall, ExprMacro, ExprPath, ExprStruct, FnArg, Ident, ImplItemFn, Lit,
    LitStr, Member, Pat, PatType, Path, PathArguments, ReturnType, Stmt, Token, Type,
};

use crate::attribute::{is_plain_path, path_spelling};
use crate::rule::{TermSort, parse_term_sort};
use crate::{
    MapBody, ProvenanceAnchor, ProvenanceRole, StateTerm, SyntaxError, SyntaxErrorKind,
    TermExpression, TermSymbolKind, TokenRange, parse_k_sequence_expression, parse_map_expression,
    parse_term_expression,
};

/// Parsed payload of one `#[k::config_var(name = "...", main)]` helper.
#[derive(Clone, Debug)]
pub struct ConfigurationVariableAttribute {
    name: LitStr,
    main: Option<Ident>,
    inferred_name: bool,
    inferred_main: bool,
}

impl ConfigurationVariableAttribute {
    /// Returns the external K configuration-variable name.
    #[must_use]
    pub const fn name(&self) -> &LitStr {
        &self.name
    }

    /// Returns the authored `main` marker token.
    #[must_use]
    pub const fn main_token(&self) -> Option<&Ident> {
        self.main.as_ref()
    }

    /// Whether this variable is the sole positional main input.
    #[must_use]
    pub const fn is_main(&self) -> bool {
        self.main.is_some()
    }

    /// Whether the external name was derived from the Rust binding.
    #[must_use]
    pub const fn has_inferred_name(&self) -> bool {
        self.inferred_name
    }

    /// Whether `main` was inferred from use in the computation cell.
    #[must_use]
    pub const fn has_inferred_main(&self) -> bool {
        self.inferred_main
    }
}

/// One accepted main configuration-variable parameter.
#[derive(Clone, Debug)]
pub struct ConfigurationVariable {
    parameter: PatType,
    binding: Ident,
    attribute: ConfigurationVariableAttribute,
    term_sort: Option<TermSort>,
    sort: Path,
}

impl ConfigurationVariable {
    /// Returns the original typed parameter, including its helper attribute.
    #[must_use]
    pub const fn parameter(&self) -> &PatType {
        &self.parameter
    }

    /// Returns the plain Rust parameter binding.
    #[must_use]
    pub const fn binding(&self) -> &Ident {
        &self.binding
    }

    /// Returns the checked helper payload.
    #[must_use]
    pub const fn attribute(&self) -> &ConfigurationVariableAttribute {
        &self.attribute
    }

    /// Returns the checked `Term<dyn Sort>` type.
    ///
    /// # Panics
    ///
    /// Panics for a direct typed builtin value. Fixed-state consumers should use
    /// [`Self::optional_term_sort`] or [`Self::sort`].
    #[must_use]
    pub const fn term_sort(&self) -> &TermSort {
        self.term_sort
            .as_ref()
            .expect("this configuration variable is not written as `Term<...>`")
    }

    /// Returns the resolved outer semantic sort path for either supported type form.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// Returns the optional `Term<S>` detail for open/closed term variables.
    #[must_use]
    pub const fn optional_term_sort(&self) -> Option<&TermSort> {
        self.term_sort.as_ref()
    }
}

/// Leaf or nested content in a declarative fixed-cell initializer.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Span-preserving syn nodes are the public parser contract.
pub enum InitializerCellContent {
    /// `Cell::new(value)` or `KCell::new(k![...])`.
    Leaf {
        /// Rust-resolved cell constructor path.
        constructor: Path,
        /// Structured state term.
        value: StateTerm,
        /// Whether this leaf is the computation cell.
        computation: bool,
        /// Whether the constructor was inferred from a plain expression.
        inferred_constructor: bool,
    },
    /// Nominal nested cell struct literal.
    Nested {
        /// Rust-resolved nested declaration path.
        constructor: Path,
        /// Ordered child initializers.
        children: Vec<FixedCellInitializer>,
    },
}

/// One ordered node in a complete initializer cell tree.
#[derive(Clone, Debug)]
pub struct FixedCellInitializer {
    field: syn::FieldValue,
    name: Ident,
    content: InitializerCellContent,
}

impl FixedCellInitializer {
    /// Original named Rust field value.
    #[must_use]
    pub const fn field(&self) -> &syn::FieldValue {
        &self.field
    }

    /// Cell field identity to resolve against the declaration tree.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Leaf or nested initializer content.
    #[must_use]
    pub const fn content(&self) -> &InitializerCellContent {
        &self.content
    }

    /// Whether a readable plain expression caused its leaf constructor to be inferred.
    #[must_use]
    pub const fn has_inferred_constructor(&self) -> bool {
        matches!(
            self.content,
            InitializerCellContent::Leaf {
                inferred_constructor: true,
                ..
            }
        )
    }
}

/// One rustc-resolvable type or constructor path in an initializer.
#[derive(Clone, Debug)]
pub struct InitializerReferenceCandidate {
    key: ProvenanceKey,
    path: Path,
}

impl InitializerReferenceCandidate {
    /// Returns the parser-owned provenance key.
    #[must_use]
    pub const fn key(&self) -> &ProvenanceKey {
        &self.key
    }

    /// Returns the authored Rust path.
    #[must_use]
    pub const fn path(&self) -> &Path {
        &self.path
    }

    /// Returns a deterministic token spelling for diagnostics and tests.
    #[must_use]
    pub fn path_spelling(&self) -> String {
        path_spelling(&self.path)
    }
}

/// Checked initializer for the sole fixed computation-cell field.
#[derive(Clone, Debug)]
pub struct ComputationCellInitializer {
    field: syn::FieldValue,
    constructor: Path,
    term: TermExpression,
}

impl ComputationCellInitializer {
    /// Returns the original `k: ...` field expression.
    #[must_use]
    pub const fn field(&self) -> &syn::FieldValue {
        &self.field
    }

    /// Returns the authored `KCell::new` path.
    #[must_use]
    pub const fn constructor(&self) -> &Path {
        &self.constructor
    }

    /// Returns the single-item `k!` payload parsed by the shared term parser.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }
}

/// A complete declarative fixed-state initializer associated-function shape.
///
/// The stable procedural-macro API supplies an associated method as item
/// tokens without its invoking `#[k::init]` attribute. Consequently this AST
/// checks the method-shaped tokens but cannot independently prove that the
/// invocation occurred lexically inside an inherent `impl`; the host macro
/// must preserve the item so rustc checks that context.
#[derive(Clone, Debug)]
pub struct InitializerFunction {
    item: ImplItemFn,
    variables: Vec<ConfigurationVariable>,
    body: ExprStruct,
    cells: Vec<FixedCellInitializer>,
    legacy_cell: Option<ComputationCellInitializer>,
}

impl InitializerFunction {
    /// Validates a parsed method-shaped item as a closed fixed-cell initializer.
    ///
    /// # Errors
    ///
    /// Rejects receivers, unsupported qualifiers, more than one parameter,
    /// ambiguous `main` markers, non-`Self` results, statements/control flow,
    /// missing/repeated fields, arbitrary calls, and non-single-item `k!`
    /// computation contents at their local spans.
    pub fn from_item(item: ImplItemFn) -> Result<Self, SyntaxError> {
        validate_signature(&item)?;

        let mut variables = Vec::with_capacity(item.sig.inputs.len());
        for argument in &item.sig.inputs {
            let FnArg::Typed(parameter) = argument else {
                return Err(unsupported_signature(
                    "initializers cannot have a `self` receiver",
                    argument.span(),
                ));
            };
            variables.push(parse_configuration_variable(parameter.clone())?);
        }

        if let Some(second_main) = variables
            .iter()
            .filter(|variable| variable.attribute.is_main())
            .nth(1)
        {
            return Err(SyntaxError::new(
                SyntaxErrorKind::AmbiguousMainConfigurationVariable,
                second_main
                    .attribute
                    .main
                    .as_ref()
                    .map_or_else(|| second_main.binding.span(), Ident::span),
            ));
        }

        let (body, cells, legacy_cell) = parse_body(&item)?;
        infer_main_configuration_variable(&mut variables, &cells)?;
        Ok(Self {
            item,
            variables,
            body,
            cells,
            legacy_cell,
        })
    }

    /// Returns the original span-preserving method item.
    #[must_use]
    pub const fn item(&self) -> &ImplItemFn {
        &self.item
    }

    /// Returns configuration variables in authored parameter order.
    #[must_use]
    pub fn variables(&self) -> &[ConfigurationVariable] {
        &self.variables
    }

    /// Returns the complete `Self { ... }` declarative body expression.
    #[must_use]
    pub const fn body(&self) -> &ExprStruct {
        &self.body
    }

    /// Returns the sole computation-cell initializer.
    ///
    /// # Panics
    ///
    /// Panics unless this is a legacy single-item `k` initializer. Fixed-state
    /// consumers should use [`Self::cells`].
    #[must_use]
    pub const fn cell(&self) -> &ComputationCellInitializer {
        self.legacy_cell
            .as_ref()
            .expect("this initializer has no legacy single-item `k` cell")
    }

    /// Returns the legacy single-item `k` initializer when this declaration
    /// has that compatibility shape.
    #[must_use]
    pub const fn legacy_cell(&self) -> Option<&ComputationCellInitializer> {
        self.legacy_cell.as_ref()
    }

    /// Returns the complete ordered initializer forest.
    #[must_use]
    pub fn cells(&self) -> &[FixedCellInitializer] {
        &self.cells
    }

    /// Returns canonical method, parameter, body, field, constructor, and term anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::InitializerDeclaration,
                0,
                TokenRange::for_tokens(&self.item.sig.ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::InitializerResultType,
                0,
                TokenRange::for_tokens(initializer_result_type(&self.item))?,
            ),
        ];
        for (ordinal, variable) in self.variables.iter().enumerate() {
            let ordinal = checked_ordinal(
                ordinal,
                ProvenanceRole::ConfigurationVariable,
                variable.binding.span(),
            )?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationVariable,
                ordinal,
                TokenRange::for_tokens(&variable.binding)?,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationVariableName,
                ordinal,
                if variable.attribute.inferred_name {
                    TokenRange::for_tokens(&variable.binding)?
                } else {
                    TokenRange::for_tokens(&variable.attribute.name)?
                },
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationVariableType,
                ordinal,
                TokenRange::for_tokens(&*variable.parameter.ty)?,
            ));
            if let Some(main) = &variable.attribute.main {
                anchors.push(ProvenanceAnchor::new(
                    ProvenanceRole::ConfigurationVariableMain,
                    ordinal,
                    TokenRange::for_tokens(main)?,
                ));
            }
        }
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::InitializerBody,
            0,
            TokenRange::for_tokens(&self.body)?,
        ));
        let mut cell_ordinal = 0;
        let mut constructor_ordinal = 0;
        let mut term_ordinal = 0;
        append_initializer_anchors(
            &self.cells,
            &mut anchors,
            &mut cell_ordinal,
            &mut constructor_ordinal,
            &mut term_ordinal,
        )?;
        Ok(anchors)
    }

    /// Returns rustc-resolvable result-type, variable-sort, and constructor candidates.
    ///
    /// Bare references matching the optional configuration-variable binding
    /// are retained as term anchors but omitted from resolution candidates.
    ///
    /// # Errors
    ///
    /// Returns a structured overflow error if a role has more than `u32::MAX`
    /// occurrences.
    pub fn reference_candidates(&self) -> Result<Vec<InitializerReferenceCandidate>, SyntaxError> {
        let Type::Path(result_type) = initializer_result_type(&self.item) else {
            unreachable!("the initializer return type was validated as `Self`")
        };
        let mut candidates = vec![InitializerReferenceCandidate {
            key: canonical_key(ProvenanceRole::InitializerResultType, 0),
            path: result_type.path.clone(),
        }];
        for (ordinal, variable) in self.variables.iter().enumerate() {
            candidates.push(InitializerReferenceCandidate {
                key: canonical_key(
                    ProvenanceRole::ConfigurationVariableType,
                    checked_ordinal(
                        ordinal,
                        ProvenanceRole::ConfigurationVariableType,
                        variable.sort.span(),
                    )?,
                ),
                path: variable.sort.clone(),
            });
        }
        let mut constructor_ordinal = 0;
        let mut term_ordinal = 0;
        append_initializer_candidates(
            &self.cells,
            &self.variables,
            &mut candidates,
            &mut constructor_ordinal,
            &mut term_ordinal,
        )?;
        Ok(candidates)
    }
}

/// Parses a fixed-state initializer method from proc-macro item tokens.
///
/// # Errors
///
/// Returns Rust parsing failures or a structured closed-grammar error.
pub fn parse_initializer_function(tokens: TokenStream) -> Result<InitializerFunction, SyntaxError> {
    InitializerFunction::from_item(syn::parse2::<ImplItemFn>(tokens)?)
}

/// Parses a fixed-state initializer method shape directly from source text.
///
/// The source is the method item delivered to an attribute macro, so it does
/// not include the invoking `#[k::init]` attribute.
///
/// # Errors
///
/// Returns the same failures as [`parse_initializer_function`].
pub fn parse_initializer_function_source(source: &str) -> Result<InitializerFunction, SyntaxError> {
    InitializerFunction::from_item(syn::parse_str::<ImplItemFn>(source)?)
}

fn validate_signature(item: &ImplItemFn) -> Result<(), SyntaxError> {
    if let Some(attribute) = item.attrs.first() {
        return Err(unsupported_signature(
            "attributes other than the invoking `#[k::init]` are unsupported",
            attribute.span(),
        ));
    }
    let signature = &item.sig;
    if signature.ident != "init" {
        return Err(unsupported_signature(
            "the associated initializer must be named `init`",
            signature.ident.span(),
        ));
    }
    if let Some(token) = signature.constness {
        return Err(unsupported_signature(
            "initializers cannot be `const`",
            token.span,
        ));
    }
    if let Some(token) = signature.asyncness {
        return Err(unsupported_signature(
            "initializers cannot be `async`",
            token.span,
        ));
    }
    if let Some(token) = signature.unsafety {
        return Err(unsupported_signature(
            "initializers cannot be `unsafe`",
            token.span,
        ));
    }
    if let Some(abi) = &signature.abi {
        return Err(unsupported_signature(
            "initializers cannot declare an extern ABI",
            abi.span(),
        ));
    }
    if !signature.generics.params.is_empty() {
        return Err(unsupported_signature(
            "initializer generics are unsupported",
            signature.generics.params.span(),
        ));
    }
    if let Some(where_clause) = &signature.generics.where_clause {
        return Err(unsupported_signature(
            "initializer where clauses are unsupported",
            where_clause.span(),
        ));
    }
    if let Some(variadic) = &signature.variadic {
        return Err(unsupported_signature(
            "variadic initializers are not supported",
            variadic.span(),
        ));
    }
    let ReturnType::Type(_, result) = &signature.output else {
        return Err(unsupported_signature(
            "the initializer must return `Self`",
            signature.ident.span(),
        ));
    };
    if !is_self_type(result) {
        return Err(unsupported_signature(
            "the initializer must return exactly `Self`",
            result.span(),
        ));
    }
    Ok(())
}

fn parse_configuration_variable(parameter: PatType) -> Result<ConfigurationVariable, SyntaxError> {
    let Pat::Ident(binding_pattern) = &*parameter.pat else {
        return Err(unsupported_variable(
            "configuration variables require a plain identifier binding",
            parameter.pat.span(),
        ));
    };
    if binding_pattern.by_ref.is_some()
        || binding_pattern.mutability.is_some()
        || binding_pattern.subpat.is_some()
        || !binding_pattern.attrs.is_empty()
    {
        return Err(unsupported_variable(
            "configuration variables require a plain immutable identifier",
            binding_pattern.span(),
        ));
    }
    if parameter.attrs.len() > 1
        || parameter
            .attrs
            .first()
            .is_some_and(|attribute| !is_config_var_attribute(attribute))
    {
        let span = parameter
            .attrs
            .first()
            .map_or_else(|| parameter.pat.span(), Attribute::span);
        return Err(unsupported_variable(
            "initializer parameters accept at most one `#[k::config_var(...)]` override",
            span,
        ));
    }
    let binding = binding_pattern.ident.clone();
    let attribute = if let Some(attribute) = parameter.attrs.first() {
        parse_config_var_attribute(attribute)?
    } else {
        ConfigurationVariableAttribute {
            name: LitStr::new(&derived_external_name(&binding), binding.span()),
            main: None,
            inferred_name: true,
            inferred_main: false,
        }
    };
    let (term_sort, sort) = if let Ok(term_sort) = parse_term_sort((*parameter.ty).clone()) {
        let sort = term_sort.sort().clone();
        (Some(term_sort), sort)
    } else {
        let Type::Path(type_path) = &*parameter.ty else {
            return Err(unsupported_variable(
                "expected `Term<S>` or a typed builtin configuration value",
                parameter.ty.span(),
            ));
        };
        if type_path.qself.is_some() || type_path.path.segments.is_empty() {
            return Err(unsupported_variable(
                "configuration-variable types require a Rust path",
                parameter.ty.span(),
            ));
        }
        let mut sort = type_path.path.clone();
        sort.segments
            .last_mut()
            .expect("path is nonempty")
            .arguments = PathArguments::None;
        if !is_plain_path(&sort) {
            return Err(unsupported_variable(
                "the outer configuration-variable sort must be a plain path",
                parameter.ty.span(),
            ));
        }
        (None, sort)
    };
    Ok(ConfigurationVariable {
        parameter,
        binding,
        attribute,
        term_sort,
        sort,
    })
}

fn parse_config_var_attribute(
    attribute: &Attribute,
) -> Result<ConfigurationVariableAttribute, SyntaxError> {
    let structured = std::cell::RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parse_config_var_stream(input) {
        Ok(value) => Ok(value),
        Err(error) => {
            structured.replace(Some(error.clone()));
            Err(error.into_syn_error())
        }
    };
    attribute.parse_args_with(parser).map_err(|error| {
        structured
            .borrow_mut()
            .take()
            .unwrap_or_else(|| error.into())
    })
}

fn parse_config_var_stream(
    input: ParseStream<'_>,
) -> Result<ConfigurationVariableAttribute, SyntaxError> {
    let missing_span = input.span();
    let mut name = None;
    let mut main = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        match key.to_string().as_str() {
            "name" if name.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "name" },
                    key.span(),
                ));
            }
            "main" if main.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "main" },
                    key.span(),
                ));
            }
            "name" => {
                input.parse::<Token![=]>()?;
                let expression: Expr = input.parse()?;
                let Expr::Lit(literal) = expression else {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::InvalidArgumentValue {
                            name: "name",
                            expected: "a nonempty Rust string literal",
                        },
                        expression.span(),
                    ));
                };
                let Lit::Str(value) = literal.lit else {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::InvalidArgumentValue {
                            name: "name",
                            expected: "a nonempty Rust string literal",
                        },
                        literal.span(),
                    ));
                };
                if !literal.attrs.is_empty() || value.value().is_empty() {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::InvalidArgumentValue {
                            name: "name",
                            expected: "a nonempty unadorned Rust string literal",
                        },
                        value.span(),
                    ));
                }
                name = Some(value);
            }
            "main" => main = Some(key),
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument {
                        name: key.to_string(),
                    },
                    key.span(),
                ));
            }
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(ConfigurationVariableAttribute {
        name: name.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "name" },
                missing_span,
            )
        })?,
        main,
        inferred_name: false,
        inferred_main: false,
    })
}

fn parse_body(
    item: &ImplItemFn,
) -> Result<
    (
        ExprStruct,
        Vec<FixedCellInitializer>,
        Option<ComputationCellInitializer>,
    ),
    SyntaxError,
> {
    if item.block.stmts.len() != 1 {
        return Err(unsupported_body(
            "the body must contain exactly one declarative `Self { ... }` expression",
            item.block.span(),
        ));
    }
    let Stmt::Expr(Expr::Struct(body), None) = &item.block.stmts[0] else {
        return Err(unsupported_body(
            "statements, semicolons, control flow, mutation, and early return are forbidden",
            item.block.stmts[0].span(),
        ));
    };
    if body.qself.is_some()
        || body.path.leading_colon.is_some()
        || body.path.segments.len() != 1
        || body.path.segments[0].ident != "Self"
        || !matches!(body.path.segments[0].arguments, PathArguments::None)
    {
        return Err(unsupported_body(
            "the initializer root must be exactly `Self { ... }`",
            body.path.span(),
        ));
    }
    if let Some(rest) = &body.rest {
        return Err(unsupported_body(
            "struct update/rest syntax is not declarative initialization",
            rest.span(),
        ));
    }
    let mut names = std::collections::BTreeSet::new();
    let mut cells = Vec::with_capacity(body.fields.len());
    let mut legacy_cell = None;
    for field in &body.fields {
        let Member::Named(name) = &field.member else {
            return Err(unsupported_body(
                "initializer fields must use named Rust members",
                field.member.span(),
            ));
        };
        if !names.insert(name.to_string()) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateConfigurationField { name: "fixed cell" },
                name.span(),
            ));
        }
        if let Some(attribute) = field.attrs.first() {
            return Err(unsupported_body(
                "initializer field attributes are unsupported",
                attribute.span(),
            ));
        }
        let parsed = parse_initializer_cell(field.clone())?;
        if name == "k"
            && let InitializerCellContent::Leaf {
                constructor,
                value: StateTerm::KSequence(sequence),
                ..
            } = &parsed.content
            && sequence.items().len() == 1
            && matches!(sequence.tail(), crate::StateMacroRemainder::Exact)
        {
            legacy_cell = Some(ComputationCellInitializer {
                field: field.clone(),
                constructor: constructor.clone(),
                term: sequence.items()[0].clone(),
            });
        }
        cells.push(parsed);
    }
    if cells.is_empty() {
        return Err(unsupported_body(
            "an initializer requires at least one fixed cell field",
            body.brace_token.span.close(),
        ));
    }
    Ok((body.clone(), cells, legacy_cell))
}

#[allow(clippy::too_many_lines)] // Validation stays linear and reports each local syn node.
fn parse_initializer_cell(field: syn::FieldValue) -> Result<FixedCellInitializer, SyntaxError> {
    let Member::Named(name) = &field.member else {
        unreachable!("initializer fields were checked as named")
    };
    let name = name.clone();
    let content = match &field.expr {
        Expr::Call(ExprCall {
            attrs, func, args, ..
        }) => {
            if !attrs.is_empty() || args.len() != 1 {
                return Err(unsupported_body(
                    "cell constructors require exactly one argument",
                    field.expr.span(),
                ));
            }
            let Expr::Path(ExprPath {
                attrs,
                qself: None,
                path,
            }) = &**func
            else {
                return Err(unsupported_body(
                    "cell constructors must be plain paths",
                    func.span(),
                ));
            };
            if !attrs.is_empty() || !is_plain_path(path) || path.segments.len() < 2 {
                return Err(unsupported_body(
                    "cell constructors must be plain paths",
                    path.span(),
                ));
            }
            let mut reversed = path.segments.iter().rev();
            let method = reversed.next().expect("constructor path is nonempty");
            let wrapper = reversed.next().expect("constructor has two segments");
            if method.ident != "new"
                || !matches!(wrapper.ident.to_string().as_str(), "Cell" | "KCell")
            {
                return Err(unsupported_body(
                    "leaf constructors must end in `Cell::new` or `KCell::new`",
                    path.span(),
                ));
            }
            let argument = args.first().expect("one argument was checked");
            let computation = wrapper.ident == "KCell";
            let value = parse_initializer_state_term(argument, computation)?;
            InitializerCellContent::Leaf {
                constructor: path.clone(),
                value,
                computation,
                inferred_constructor: false,
            }
        }
        Expr::Struct(nested) => {
            if nested.qself.is_some() || !is_plain_path(&nested.path) || nested.rest.is_some() {
                return Err(unsupported_body(
                    "nested cell initialization requires a complete plain struct literal",
                    nested.span(),
                ));
            }
            let mut names = std::collections::BTreeSet::new();
            let mut children = Vec::with_capacity(nested.fields.len());
            for child in &nested.fields {
                let Member::Named(child_name) = &child.member else {
                    return Err(unsupported_body(
                        "nested initializer fields must be named",
                        child.member.span(),
                    ));
                };
                if !names.insert(child_name.to_string()) {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::DuplicateConfigurationField { name: "fixed cell" },
                        child_name.span(),
                    ));
                }
                if let Some(attribute) = child.attrs.first() {
                    return Err(unsupported_body(
                        "initializer field attributes are not semantic",
                        attribute.span(),
                    ));
                }
                children.push(parse_initializer_cell(child.clone())?);
            }
            if children.is_empty() {
                return Err(unsupported_body(
                    "nested cell initialization cannot be empty",
                    nested.span(),
                ));
            }
            InitializerCellContent::Nested {
                constructor: nested.path.clone(),
                children,
            }
        }
        Expr::Macro(expression) => {
            let path = &expression.mac.path;
            if !expression.attrs.is_empty() || !is_plain_path(path) {
                return Err(unsupported_body(
                    "state macro paths must be plain",
                    expression.span(),
                ));
            }
            let computation = path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "k");
            let value = parse_initializer_state_term(&field.expr, computation)?;
            InitializerCellContent::Leaf {
                constructor: inferred_constructor_path(computation, field.expr.span()),
                value,
                computation,
                inferred_constructor: true,
            }
        }
        Expr::Path(_) => InitializerCellContent::Leaf {
            constructor: inferred_constructor_path(false, field.expr.span()),
            value: StateTerm::Term(parse_term_expression(field.expr.to_token_stream())?),
            computation: false,
            inferred_constructor: true,
        },
        other => {
            return Err(unsupported_body(
                "initializer cells require a cell constructor, a readable plain term, or a nested cell struct",
                other.span(),
            ));
        }
    };
    Ok(FixedCellInitializer {
        field,
        name,
        content,
    })
}

fn parse_initializer_state_term(
    expression: &Expr,
    computation: bool,
) -> Result<StateTerm, SyntaxError> {
    if let Expr::Macro(ExprMacro { attrs, mac }) = expression {
        if !attrs.is_empty() || !is_plain_path(&mac.path) {
            return Err(unsupported_body(
                "state macro paths must be plain",
                expression.span(),
            ));
        }
        let name = mac
            .path
            .segments
            .last()
            .expect("plain path is nonempty")
            .ident
            .to_string();
        return match name.as_str() {
            "k" if computation => Ok(StateTerm::KSequence(parse_k_sequence_expression(
                mac.tokens.clone(),
            )?)),
            "map" if !computation => Ok(StateTerm::Map(parse_map_expression(mac.tokens.clone())?)),
            _ => Err(unsupported_body(
                "`KCell` requires `k!`; `Cell` accepts ordinary terms or `map!`",
                expression.span(),
            )),
        };
    }
    if computation {
        return Err(unsupported_body(
            "`KCell::new` requires an explicit `k!` payload",
            expression.span(),
        ));
    }
    Ok(StateTerm::Term(parse_term_expression(
        expression.to_token_stream(),
    )?))
}

fn append_initializer_anchors(
    cells: &[FixedCellInitializer],
    output: &mut Vec<ProvenanceAnchor>,
    cell_ordinal: &mut usize,
    constructor_ordinal: &mut usize,
    term_ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for cell in cells {
        let current = checked_ordinal(
            *cell_ordinal,
            ProvenanceRole::InitializerCell,
            cell.name.span(),
        )?;
        *cell_ordinal += 1;
        let range = TokenRange::for_tokens(&cell.field.member)?;
        output.push(ProvenanceAnchor::new(
            ProvenanceRole::InitializerCell,
            current,
            range,
        ));
        output.push(ProvenanceAnchor::new(
            ProvenanceRole::InitializerField,
            current,
            range,
        ));
        match &cell.content {
            InitializerCellContent::Leaf {
                constructor,
                value,
                inferred_constructor,
                ..
            } => {
                let current = checked_ordinal(
                    *constructor_ordinal,
                    ProvenanceRole::InitializerCellConstructor,
                    constructor.span(),
                )?;
                *constructor_ordinal += 1;
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::InitializerCellConstructor,
                    current,
                    if *inferred_constructor {
                        TokenRange::for_tokens(&cell.field.expr)?
                    } else {
                        TokenRange::for_tokens(constructor)?
                    },
                ));
                append_state_term_anchors(value, output, term_ordinal)?;
            }
            InitializerCellContent::Nested {
                constructor,
                children,
            } => {
                let current = checked_ordinal(
                    *constructor_ordinal,
                    ProvenanceRole::InitializerNestedConstructor,
                    constructor.span(),
                )?;
                *constructor_ordinal += 1;
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::InitializerNestedConstructor,
                    current,
                    TokenRange::for_tokens(constructor)?,
                ));
                append_initializer_anchors(
                    children,
                    output,
                    cell_ordinal,
                    constructor_ordinal,
                    term_ordinal,
                )?;
            }
        }
    }
    Ok(())
}

fn append_state_term_anchors(
    value: &StateTerm,
    output: &mut Vec<ProvenanceAnchor>,
    term_ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    match value {
        StateTerm::Term(term) => append_term_anchors(term, output, term_ordinal),
        StateTerm::KSequence(sequence) => {
            output.extend(sequence.provenance()?);
            for term in sequence.items() {
                append_term_anchors(term, output, term_ordinal)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => {
            output.extend(map.provenance()?);
            match map.body() {
                MapBody::Empty { .. } => Ok(()),
                MapBody::Items { items, .. } => {
                    for item in items {
                        append_term_anchors(item.key(), output, term_ordinal)?;
                        append_term_anchors(item.value(), output, term_ordinal)?;
                    }
                    Ok(())
                }
                MapBody::Update { base, key, value } => {
                    append_term_anchors(base, output, term_ordinal)?;
                    append_term_anchors(key, output, term_ordinal)?;
                    append_term_anchors(value, output, term_ordinal)
                }
            }
        }
    }
}

fn append_term_anchors(
    term: &TermExpression,
    output: &mut Vec<ProvenanceAnchor>,
    term_ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    let current = checked_ordinal(
        *term_ordinal,
        ProvenanceRole::InitializerTerm,
        term.expression().span(),
    )?;
    *term_ordinal += 1;
    output.push(ProvenanceAnchor::new(
        ProvenanceRole::InitializerTerm,
        current,
        TokenRange::for_tokens(term.expression())?,
    ));
    for symbol in term.symbols() {
        let ordinal = output
            .iter()
            .filter(|anchor| anchor.role() == ProvenanceRole::InitializerTermPath)
            .count();
        output.push(ProvenanceAnchor::new(
            ProvenanceRole::InitializerTermPath,
            checked_ordinal(
                ordinal,
                ProvenanceRole::InitializerTermPath,
                symbol.path().span(),
            )?,
            TokenRange::for_tokens(symbol.path())?,
        ));
    }
    Ok(())
}

fn append_initializer_candidates(
    cells: &[FixedCellInitializer],
    variables: &[ConfigurationVariable],
    output: &mut Vec<InitializerReferenceCandidate>,
    constructor_ordinal: &mut usize,
    term_path_ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for cell in cells {
        match &cell.content {
            InitializerCellContent::Leaf {
                constructor,
                value,
                inferred_constructor,
                ..
            } => {
                let current = checked_ordinal(
                    *constructor_ordinal,
                    ProvenanceRole::InitializerCellConstructor,
                    constructor.span(),
                )?;
                if !inferred_constructor {
                    output.push(InitializerReferenceCandidate {
                        key: canonical_key(ProvenanceRole::InitializerCellConstructor, current),
                        path: constructor.clone(),
                    });
                }
                *constructor_ordinal += 1;
                append_state_term_candidates(value, variables, output, term_path_ordinal)?;
            }
            InitializerCellContent::Nested {
                constructor,
                children,
            } => {
                output.push(InitializerReferenceCandidate {
                    key: canonical_key(
                        ProvenanceRole::InitializerNestedConstructor,
                        checked_ordinal(
                            *constructor_ordinal,
                            ProvenanceRole::InitializerNestedConstructor,
                            constructor.span(),
                        )?,
                    ),
                    path: constructor.clone(),
                });
                *constructor_ordinal += 1;
                append_initializer_candidates(
                    children,
                    variables,
                    output,
                    constructor_ordinal,
                    term_path_ordinal,
                )?;
            }
        }
    }
    Ok(())
}

fn append_state_term_candidates(
    value: &StateTerm,
    variables: &[ConfigurationVariable],
    output: &mut Vec<InitializerReferenceCandidate>,
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    match value {
        StateTerm::Term(term) => append_term_candidates(term, variables, output, ordinal),
        StateTerm::KSequence(sequence) => {
            for item in sequence.items() {
                append_term_candidates(item, variables, output, ordinal)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => match map.body() {
            MapBody::Empty { .. } => Ok(()),
            MapBody::Items { items, .. } => {
                for item in items {
                    append_term_candidates(item.key(), variables, output, ordinal)?;
                    append_term_candidates(item.value(), variables, output, ordinal)?;
                }
                Ok(())
            }
            MapBody::Update { base, key, value } => {
                append_term_candidates(base, variables, output, ordinal)?;
                append_term_candidates(key, variables, output, ordinal)?;
                append_term_candidates(value, variables, output, ordinal)
            }
        },
    }
}

fn append_term_candidates(
    term: &TermExpression,
    variables: &[ConfigurationVariable],
    output: &mut Vec<InitializerReferenceCandidate>,
    ordinal: &mut usize,
) -> Result<(), SyntaxError> {
    for symbol in term.symbols() {
        let current = checked_ordinal(
            *ordinal,
            ProvenanceRole::InitializerTermPath,
            symbol.path().span(),
        )?;
        *ordinal += 1;
        if symbol.kind() == TermSymbolKind::Reference
            && variables.iter().any(|variable| {
                symbol.path().leading_colon.is_none()
                    && symbol.path().segments.len() == 1
                    && symbol.path().segments[0].ident == variable.binding
            })
        {
            continue;
        }
        output.push(InitializerReferenceCandidate {
            key: canonical_key(ProvenanceRole::InitializerTermPath, current),
            path: symbol.path().clone(),
        });
    }
    Ok(())
}

fn is_config_var_attribute(attribute: &Attribute) -> bool {
    is_plain_path(attribute.path())
        && attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "config_var")
}

fn derived_external_name(binding: &Ident) -> String {
    binding.unraw().to_string().to_uppercase()
}

fn inferred_constructor_path(computation: bool, span: proc_macro2::Span) -> Path {
    Path::from(Ident::new(if computation { "KCell" } else { "Cell" }, span))
}

fn infer_main_configuration_variable(
    variables: &mut [ConfigurationVariable],
    cells: &[FixedCellInitializer],
) -> Result<(), SyntaxError> {
    if variables
        .iter()
        .any(|variable| variable.attribute.is_main())
    {
        return Ok(());
    }
    let mut used = std::collections::BTreeSet::new();
    collect_computation_variable_uses(cells, variables, &mut used);
    let mut matches = variables
        .iter_mut()
        .filter(|variable| used.contains(&variable.binding.to_string()));
    let Some(main) = matches.next() else {
        return Ok(());
    };
    if let Some(ambiguous) = matches.next() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::AmbiguousMainConfigurationVariable,
            ambiguous.binding.span(),
        ));
    }
    main.attribute.main = Some(main.binding.clone());
    main.attribute.inferred_main = true;
    Ok(())
}

fn collect_computation_variable_uses(
    cells: &[FixedCellInitializer],
    variables: &[ConfigurationVariable],
    output: &mut std::collections::BTreeSet<String>,
) {
    for cell in cells {
        match &cell.content {
            InitializerCellContent::Leaf {
                value: StateTerm::KSequence(sequence),
                computation: true,
                ..
            } => {
                for term in sequence.items() {
                    for symbol in term.symbols() {
                        if symbol.kind() != TermSymbolKind::Reference
                            || symbol.path().leading_colon.is_some()
                            || symbol.path().segments.len() != 1
                        {
                            continue;
                        }
                        let binding = &symbol.path().segments[0].ident;
                        if variables
                            .iter()
                            .any(|variable| variable.binding == *binding)
                        {
                            output.insert(binding.to_string());
                        }
                    }
                }
            }
            InitializerCellContent::Nested { children, .. } => {
                collect_computation_variable_uses(children, variables, output);
            }
            InitializerCellContent::Leaf { .. } => {}
        }
    }
}

fn is_self_type(ty: &Type) -> bool {
    matches!(ty, Type::Path(path)
        if path.qself.is_none()
            && path.path.leading_colon.is_none()
            && path.path.segments.len() == 1
            && path.path.segments[0].ident == "Self"
            && matches!(path.path.segments[0].arguments, PathArguments::None))
}

fn initializer_result_type(item: &ImplItemFn) -> &Type {
    let ReturnType::Type(_, result) = &item.sig.output else {
        unreachable!("the initializer return type was validated")
    };
    result
}

fn canonical_key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
        .expect("the static provenance role catalog contains only nonempty roles")
}

fn checked_ordinal(
    ordinal: usize,
    role: ProvenanceRole,
    span: proc_macro2::Span,
) -> Result<u32, SyntaxError> {
    u32::try_from(ordinal).map_err(|_| {
        SyntaxError::new(
            SyntaxErrorKind::TooManyProvenanceOccurrences {
                role: role.as_str(),
            },
            span,
        )
    })
}

fn unsupported_signature(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedInitializerSignature { reason },
        span,
    )
}

fn unsupported_variable(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedConfigurationVariable { reason },
        span,
    )
}

fn unsupported_body(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedInitializerBody { reason }, span)
}
