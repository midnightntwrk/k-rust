use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, ExprCall, ExprMacro, ExprPath, ExprStruct, FnArg, Ident, ImplItemFn, Lit,
    LitStr, Member, Pat, PatType, Path, PathArguments, ReturnType, Stmt, Token, Type, TypePath,
};

use crate::ReferenceCandidate;
use crate::parse::{
    KeyAllocator, KrsSyntax, structured_args,
    unsupported_configuration_variable as unsupported_variable,
    unsupported_initializer_body as unsupported_body,
    unsupported_initializer_signature as unsupported_signature,
};
use crate::path::{is_plain_path, plain_path_last, without_last_arguments};
use crate::state_macro::{StateMacroContext, StatePosition, parse_k_sequence, parse_map};
use crate::term_sort::{TermSort, parse_typed_term_sort};
use crate::{
    ProvenanceAnchor, ProvenanceRole, StateTerm, SyntaxError, SyntaxErrorKind, TermExpression,
    TermSymbolKind, TokenRange,
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
    arguments: Vec<crate::SortArgument>,
    key: Option<ProvenanceKey>,
    name_key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
    main_key: Option<ProvenanceKey>,
}

impl ConfigurationVariable {
    /// The key of the binding, the variable itself.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the external name: the `name` literal, or the binding
    /// when the name is derived from it.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the parameter type.
    #[must_use]
    pub const fn type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }

    /// The key of the authored `main` marker, numbered as the variable is;
    /// `None` when the variable has none.
    #[must_use]
    pub const fn main_key(&self) -> Option<&ProvenanceKey> {
        self.main_key.as_ref()
    }

    /// Keys the binding, the external name, the type, each collection
    /// argument in preorder, then an authored `main` marker at the binding's
    /// ordinal.
    fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.main_key = None;
        crate::SortArgument::clear_keys(&mut self.arguments);
        let binding = TokenRange::for_tokens(&self.binding)?;
        let key = keys.key(ProvenanceRole::ConfigurationVariable, binding)?;
        self.name_key = Some(keys.key(
            ProvenanceRole::ConfigurationVariableName,
            if self.attribute.inferred_name {
                binding
            } else {
                TokenRange::for_tokens(&self.attribute.name)?
            },
        )?);
        self.type_key = Some(keys.key(
            ProvenanceRole::ConfigurationVariableType,
            TokenRange::for_tokens(&*self.parameter.ty)?,
        )?);
        crate::SortArgument::allocate_keys(
            &mut self.arguments,
            keys,
            ProvenanceRole::ConfigurationVariableTypeArgument,
        )?;
        if let Some(term_sort) = &mut self.term_sort {
            term_sort.arguments_mut().clone_from_slice(&self.arguments);
        }
        // `main` is numbered as its variable is.
        if let Some(main) = &self.attribute.main {
            self.main_key = Some(keys.paired(
                ProvenanceRole::ConfigurationVariableMain,
                &key,
                TokenRange::for_tokens(main)?,
            )?);
        }
        self.key = Some(key);
        Ok(())
    }

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

    /// Returns the checked `Term<S>` detail when this variable uses a term type.
    #[must_use]
    pub const fn term_sort(&self) -> Option<&TermSort> {
        self.term_sort.as_ref()
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
    /// Returns the element types of a collection type (`Value` of
    /// `xs: List<Value>`, `Int` and `Set<Int>` of `Map<Int, Set<Int>>`),
    /// read as a cell's are; empty for a bare collection and every other sort.
    #[must_use]
    pub fn arguments(&self) -> &[crate::SortArgument] {
        &self.arguments
    }
}

/// Leaf or nested content in a declarative fixed-cell initializer.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Span-preserving syn nodes are the public parser contract."
)]
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
    optional: bool,
    key: Option<ProvenanceKey>,
    field_key: Option<ProvenanceKey>,
    constructor_key: Option<ProvenanceKey>,
}

impl FixedCellInitializer {
    /// The key of the cell, at its field name.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the field name as a field of its struct.
    #[must_use]
    pub const fn field_key(&self) -> Option<&ProvenanceKey> {
        self.field_key.as_ref()
    }

    /// The key of the constructor, numbered as the cell is: a leaf's
    /// `Cell::new`/`KCell::new` path, or its whole value when the constructor
    /// is inferred, or a nested cell's struct path.
    #[must_use]
    pub const fn constructor_key(&self) -> Option<&ProvenanceKey> {
        self.constructor_key.as_ref()
    }

    /// Forgets the keys of the cell and of everything inside it, before the
    /// initializer's pass keys them.
    fn clear_keys(&mut self) {
        self.key = None;
        self.field_key = None;
        self.constructor_key = None;
        match &mut self.content {
            InitializerCellContent::Leaf { value, .. } => value.clear_keys(),
            InitializerCellContent::Nested { children, .. } => {
                for child in children {
                    child.clear_keys();
                }
            }
        }
    }

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

    /// Whether the value was written `Some(template)`: the template of an
    /// optional (`?`) cell (KF-023, R7). [`Self::field`] then holds the
    /// template expression.
    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
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
    result_type: TypePath,
    variables: Vec<ConfigurationVariable>,
    body: ExprStruct,
    cells: Vec<FixedCellInitializer>,
    legacy_cell: Option<ComputationCellInitializer>,
    declaration_key: Option<ProvenanceKey>,
    result_type_key: Option<ProvenanceKey>,
    body_key: Option<ProvenanceKey>,
    /// The anchors of the initializer's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
        let result_type = parse_signature(&item)?;

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
        Self {
            item,
            result_type,
            variables,
            body,
            cells,
            legacy_cell,
            declaration_key: None,
            result_type_key: None,
            body_key: None,
            anchors: Vec::new(),
        }
        .keyed()
    }

    /// Keys the initializer, as a sentence of its own: the method name, the
    /// result type, each configuration variable, the body, then every cell
    /// with its constructor, `k!`/`map!` structure and terms
    /// ([`allocate_initializer_keys`]), and across the terms, in that order,
    /// their constant islands, their lexemes, their record field names and
    /// their literals.
    /// Each role runs across the whole initializer, because a key names one
    /// authored node of the sentence.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.declaration_key = Some(keys.key(
            ProvenanceRole::InitializerDeclaration,
            TokenRange::for_tokens(&self.item.sig.ident)?,
        )?);
        self.result_type_key = Some(keys.key(
            ProvenanceRole::InitializerResultType,
            TokenRange::for_tokens(&self.result_type)?,
        )?);
        for variable in &mut self.variables {
            variable.allocate_keys(&mut keys)?;
        }
        self.body_key = Some(keys.key(
            ProvenanceRole::InitializerBody,
            TokenRange::for_tokens(&self.body)?,
        )?);
        for cell in &mut self.cells {
            cell.clear_keys();
        }
        allocate_initializer_keys(&mut keys, &mut self.cells)?;
        // Constant islands are numbered per kind over the initializer's terms
        // in the order expansion visits them.
        let mut terms = Vec::new();
        initializer_terms_mut(&mut self.cells, &mut terms);
        for term in &mut terms {
            let (nodes, _, term_keys) = term.keying();
            crate::state_rule::allocate_claim_node_keys(&mut keys, [(nodes, term_keys)])?;
        }
        for term in &mut terms {
            let (nodes, _, term_keys) = term.keying();
            crate::term::allocate_lexeme_keys(&mut keys, nodes, term_keys)?;
        }
        // Sort tests, a `k::matches!` pattern's alternatives, turbofish sort markers (KF-027),
        // `k::matches!` shells and pattern wildcards (KF-031), and `let` statements and their
        // pattern wildcards (KF-032), each kind in expansion order, as a rule's terms number
        // them.
        let islands: [crate::term::IslandKeys; 5] = [
            crate::term::allocate_sort_test_keys,
            crate::term::allocate_pattern_or_keys,
            crate::term::allocate_application_instance_keys,
            crate::term::allocate_matches_keys,
            crate::term::allocate_let_keys,
        ];
        for island in islands {
            for term in &mut terms {
                let (nodes, _, term_keys) = term.keying();
                island(&mut keys, nodes, term_keys)?;
            }
        }
        // Record field names, numbered in preorder across the terms.
        for term in &mut terms {
            let (_, tree, term_keys) = term.keying();
            crate::term::allocate_record_field_keys(
                &mut keys,
                tree,
                term_keys,
                ProvenanceRole::InitializerRecordFieldName,
            )?;
        }
        // Literals, each its own node, numbered in preorder across the terms.
        for term in &mut terms {
            let (nodes, _, term_keys) = term.keying();
            crate::term::allocate_literal_keys(
                &mut keys,
                nodes,
                term_keys,
                ProvenanceRole::InitializerTermLiteral,
            )?;
        }
        // The legacy view's term is a copy of the `k` cell's item: it takes
        // the item's keys.
        if let Some(legacy) = &mut self.legacy_cell
            && let Some(term) = self.cells.iter().find_map(|cell| match &cell.content {
                InitializerCellContent::Leaf {
                    value: StateTerm::KSequence(sequence),
                    ..
                } if cell.name == "k" => sequence.items().first(),
                _ => None,
            })
        {
            legacy.term = term.clone();
        }
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The key of the method name, the initializer itself.
    #[must_use]
    pub const fn declaration_key(&self) -> Option<&ProvenanceKey> {
        self.declaration_key.as_ref()
    }

    /// The key of the `Self` result type.
    #[must_use]
    pub const fn result_type_key(&self) -> Option<&ProvenanceKey> {
        self.result_type_key.as_ref()
    }

    /// The key of the `Self { ... }` body.
    #[must_use]
    pub const fn body_key(&self) -> Option<&ProvenanceKey> {
        self.body_key.as_ref()
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

    /// Returns the legacy single-item `k` initializer when present.
    #[must_use]
    pub const fn cell(&self) -> Option<&ComputationCellInitializer> {
        self.legacy_cell.as_ref()
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
    /// None: the initializer was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Returns rustc-resolvable result-type, variable-sort, and constructor candidates.
    ///
    /// Bare references matching the optional configuration-variable binding
    /// are retained as term anchors but omitted from resolution candidates.
    ///
    /// # Errors
    ///
    /// None: the initializer was keyed when it was parsed.
    ///
    /// # Panics
    ///
    /// Never: parsing keys every type, constructor and path a candidate
    /// names.
    pub fn reference_candidates(&self) -> Result<Vec<ReferenceCandidate>, SyntaxError> {
        let mut candidates = vec![ReferenceCandidate {
            key: self.result_type_key.clone().expect(KEYED),
            path: self.result_type.path.clone(),
            kind: (),
        }];
        for variable in &self.variables {
            candidates.push(ReferenceCandidate {
                key: variable.type_key.clone().expect(KEYED),
                path: variable.sort.clone(),
                kind: (),
            });
        }
        let arguments = self
            .variables
            .iter()
            .flat_map(|variable| crate::SortArgument::preorder(&variable.arguments));
        for argument in arguments {
            candidates.push(ReferenceCandidate {
                key: argument.key().expect(KEYED).clone(),
                path: argument.path.clone(),
                kind: (),
            });
        }
        append_initializer_candidates(&self.cells, &self.variables, &mut candidates);
        Ok(candidates)
    }
}

const KEYED: &str = "an initializer is keyed when it is parsed";

impl KrsSyntax for InitializerFunction {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2::<ImplItemFn>(tokens)?)
    }
}

/// Attributes an initializer may carry besides the invoking `#[k::init]`.
///
/// Documentation, lint levels, and `cfg` say nothing about the K configuration the initializer
/// builds; they stay on the generated Rust method, and `cfg` also guards the items generated
/// beside it. `forbid` is excluded: the expansion allows lints that its generated signature
/// triggers, and rustc rejects an `allow` under a `forbid` of the same lint.
const INITIALIZER_RUST_ATTRIBUTES: &[&str] = &["doc", "allow", "expect", "warn", "deny", "cfg"];

fn parse_signature(item: &ImplItemFn) -> Result<TypePath, SyntaxError> {
    if let Some(attribute) = item.attrs.iter().find(|attribute| {
        !attribute.path().get_ident().is_some_and(|ident| {
            INITIALIZER_RUST_ATTRIBUTES
                .iter()
                .any(|name| ident.unraw() == name)
        })
    }) {
        return Err(unsupported_signature(
            "besides the invoking `#[k::init]`, an initializer accepts only doc comments and \
             `allow`, `expect`, `warn`, `deny`, and `cfg` attributes",
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
    let result_type = match &**result {
        Type::Path(path)
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1
                && path.path.segments[0].ident == "Self"
                && matches!(path.path.segments[0].arguments, PathArguments::None) =>
        {
            path
        }
        _ => {
            return Err(unsupported_signature(
                "the initializer must return exactly `Self`",
                result.span(),
            ));
        }
    };
    Ok(result_type.clone())
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
    crate::parse::validate_authored_binder(&binding.to_string(), binding.span())?;
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
    let (term_sort, sort, arguments) = if let Ok(term_sort) =
        parse_typed_term_sort((*parameter.ty).clone())
    {
        let sort = term_sort.sort().clone();
        let arguments = term_sort.arguments().to_vec();
        (Some(term_sort), sort, arguments)
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
        let sort = without_last_arguments(&type_path.path);
        if !is_plain_path(&sort) {
            return Err(unsupported_variable(
                "the outer configuration-variable sort must be a plain path",
                parameter.ty.span(),
            ));
        }
        let arguments =
            crate::configuration::collection_arguments(&parameter.ty, invalid_variable_argument)?;
        (None, sort, arguments)
    };
    Ok(ConfigurationVariable {
        parameter,
        binding,
        attribute,
        term_sort,
        sort,
        arguments,
        key: None,
        name_key: None,
        type_key: None,
        main_key: None,
    })
}

fn invalid_variable_argument(span: proc_macro2::Span) -> SyntaxError {
    unsupported_variable(
        "a collection argument is a sort (`Int`, `k::Term<dyn Value>`) or a collection type (`Set<Int>`)",
        span,
    )
}

fn parse_config_var_attribute(
    attribute: &Attribute,
) -> Result<ConfigurationVariableAttribute, SyntaxError> {
    structured_args(attribute, parse_config_var_stream)
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
        let parsed = parse_initializer_cell(field.clone(), name.clone())?;
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

#[expect(
    clippy::too_many_lines,
    reason = "Validation stays linear and reports each local syn node."
)]
fn parse_initializer_cell(
    field: syn::FieldValue,
    name: Ident,
) -> Result<FixedCellInitializer, SyntaxError> {
    // An optional cell's value is `Some(template)`: K's declaration template
    // (KF-023, R7). The cell starts absent unless it carries `initial`.
    if let Some(template) = optional_template(&field.expr) {
        let mut inner = field.clone();
        inner.expr = template.clone();
        let mut parsed = parse_initializer_cell(inner, name)?;
        parsed.optional = true;
        return Ok(parsed);
    }
    if is_option_none(&field.expr) {
        return Err(unsupported_body(
            "K needs a template for a `?` cell; write Some(<template>) and add `initial` if the cell starts present",
            field.expr.span(),
        ));
    }
    // A literal, or a call of a qualified path other than `Cell::new`/`KCell::new` (such as
    // `list::empty()`), is a readable plain term, as a path is, and so is the notation for a
    // builtin call (`a && b`, `x.max::<Int>(0)`). A bare call stays a host call. A
    // compiler-owned island (`k::bytes!(..)`, `k::id!(..)`, `k::lexeme!(..)`) is a term too,
    // so a constant can be a cell's whole value and any other island reports its own error.
    if let Some(reason) = unsorted_cell_value(&field.expr) {
        return Err(unsupported_body(reason, field.expr.span()));
    }
    let readable_term = match &field.expr {
        Expr::Lit(_) | Expr::Unary(_) => true,
        // A collection literal is the term its calls build; the empty `map![]` and a map's
        // functional update are the cell's own map, below.
        Expr::Macro(ExprMacro { mac, .. }) => is_term_macro(mac),
        expression if crate::notation::is_expression_notation(expression) => true,
        Expr::Call(ExprCall { func, .. }) => {
            !is_cell_constructor(func)
                && matches!(&**func, Expr::Path(ExprPath { path, .. }) if path.segments.len() > 1)
        }
        _ => false,
    };
    if readable_term {
        let content = InitializerCellContent::Leaf {
            constructor: inferred_constructor_path(false, field.expr.span()),
            value: StateTerm::Term(TermExpression::parse_tokens(field.expr.to_token_stream())?),
            computation: false,
            inferred_constructor: true,
        };
        return Ok(FixedCellInitializer {
            field,
            name,
            content,
            optional: false,
            key: None,
            field_key: None,
            constructor_key: None,
        });
    }
    let content = match &field.expr {
        Expr::Call(ExprCall {
            attrs, func, args, ..
        }) => {
            let (true, 1, Some(argument)) = (attrs.is_empty(), args.len(), args.first()) else {
                return Err(unsupported_body(
                    "cell constructors require exactly one argument",
                    field.expr.span(),
                ));
            };
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
            let mut reversed = path.segments.iter().rev();
            let (true, Some(method), Some(wrapper)) = (
                attrs.is_empty() && is_plain_path(path),
                reversed.next(),
                reversed.next(),
            ) else {
                return Err(unsupported_body(
                    "cell constructors must be plain paths",
                    path.span(),
                ));
            };
            if method.ident != "new"
                || !matches!(wrapper.ident.to_string().as_str(), "Cell" | "KCell")
            {
                return Err(unsupported_body(
                    "leaf constructors must end in `Cell::new` or `KCell::new`",
                    path.span(),
                ));
            }
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
                children.push(parse_initializer_cell(child.clone(), child_name.clone())?);
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
            value: StateTerm::Term(TermExpression::parse_tokens(field.expr.to_token_stream())?),
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
        optional: false,
        key: None,
        field_key: None,
        constructor_key: None,
    })
}

/// Why `expression` cannot be a leaf cell's whole initial value, though it is an initializer
/// term below one: K reads each leaf cell's sort from its initial content, the native frontend
/// from the content's head production as it reads the configuration, and a `let` block (K's
/// `#let`), `k::matches!` (`:=K`) and `k::is!` (a sort predicate K generates later) head none it
/// knows then; Java K infers no sort for `#let` there either (finding NT-7-2).
fn unsorted_cell_value(expression: &Expr) -> Option<&'static str> {
    match expression {
        Expr::Block(_) => Some(
            "a `let` block is an initializer term, but no K frontend reads a cell's sort from it: K takes a cell's sort from its initial content, and neither Java K's kompile (`#let` gets no sort there) nor the native frontend (no production heads `#let` as it reads the configuration) finds one; write the block below a constructor or an operation of the cell's sort, as in `{ .. } && true` for a `Bool` cell",
        ),
        Expr::Macro(ExprMacro { mac, .. })
            if mac
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "matches")
                && !crate::term::is_std_matches(&mac.path) =>
        {
            Some(
                "`k::matches!` is an initializer term, but the native frontend reads no cell's sort from it: K takes a cell's sort from its initial content, and no production heads K's `:=K` as the native frontend reads the configuration; write `k::matches!(..) && true` for the `Bool` cell, or the test below a constructor",
            )
        }
        Expr::Macro(ExprMacro { mac, .. })
            if mac
                .path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "is") =>
        {
            Some(
                "`k::is!` is an initializer term, but the native frontend reads no cell's sort from it: K takes a cell's sort from its initial content, and the sort predicate it applies is generated after the native frontend reads the configuration; write `k::is!(..) && true` for the `Bool` cell, or the test below a constructor",
            )
        }
        _ => None,
    }
}

/// Whether `path` is `Some`/`None` alone or under `Option::`.
pub(crate) fn is_option_variant(path: &syn::Path, variant: &str) -> bool {
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    path.segments
        .iter()
        .all(|segment| matches!(segment.arguments, PathArguments::None))
        && segments.last().is_some_and(|last| last == variant)
        && (segments.len() == 1 || segments[segments.len() - 2] == "Option")
}

/// The template `t` of an initializer value `Some(t)`.
fn optional_template(expression: &Expr) -> Option<&Expr> {
    let Expr::Call(ExprCall {
        attrs, func, args, ..
    }) = expression
    else {
        return None;
    };
    let Expr::Path(ExprPath {
        qself: None, path, ..
    }) = &**func
    else {
        return None;
    };
    (attrs.is_empty() && args.len() == 1 && is_option_variant(path, "Some")).then(|| &args[0])
}

fn is_option_none(expression: &Expr) -> bool {
    matches!(expression, Expr::Path(ExprPath { qself: None, path, .. }) if is_option_variant(path, "None"))
}

/// Whether the macro `mac`, a leaf cell's whole value or its `Cell::new` argument, is a term: a
/// compiler-owned island (`k::id!(..)`), a set literal, or a map literal.
///
/// A cell's own `map![..]` that writes entries or a rest is built as every collection literal is,
/// `map![k1 -> v1, .., kn -> vn]` the calls `map::update(..map::update(map::empty(), k1, v1)..,
/// kn, vn)` and `map![k -> v, ..m]` the call `map::update(m, k, v)`: the map is total, and of two
/// keys that evaluate equal (configuration variables started with one value) the later one wins,
/// where K's join of the entries would leave the configuration undefined. The empty map
/// (`map![]`, `map![.Map]`) and a functional update (`map![m; k <- v]`) keep the cell's own
/// reading, which is already the value they build.
fn is_term_macro(mac: &syn::Macro) -> bool {
    crate::term::is_island_macro(&mac.path)
        || match crate::collection_literal::literal_collection(&mac.path) {
            Some(crate::collection_literal::Collection::Set) => true,
            Some(crate::collection_literal::Collection::Map) => {
                crate::state_macro::built_map_is_literal(mac.tokens.clone())
            }
            None => false,
        }
}

/// Whether `func` names a cell constructor, `Cell::new` or `KCell::new` under any prefix.
fn is_cell_constructor(func: &Expr) -> bool {
    let Expr::Path(ExprPath { path, .. }) = func else {
        return false;
    };
    let mut reversed = path.segments.iter().rev();
    matches!(
        (reversed.next(), reversed.next()),
        (Some(method), Some(wrapper))
            if method.ident == "new" && (wrapper.ident == "Cell" || wrapper.ident == "KCell")
    )
}

fn parse_initializer_state_term(
    expression: &Expr,
    computation: bool,
) -> Result<StateTerm, SyntaxError> {
    // An island and a collection literal are terms; `k!`, the empty `map![]` and a map's
    // functional update are the cell's own content.
    if let Expr::Macro(ExprMacro { attrs, mac }) = expression
        && !(attrs.is_empty() && !computation && is_term_macro(mac))
    {
        let (true, Some(last)) = (attrs.is_empty(), plain_path_last(&mac.path)) else {
            return Err(unsupported_body(
                "state macro paths must be plain",
                expression.span(),
            ));
        };
        let name = last.ident.to_string();
        // An empty shell is anchored at its invocation, path to closing
        // delimiter.
        let invocation = || TokenRange::for_tokens(mac).map(Some);
        return match name.as_str() {
            "k" if computation => Ok(StateTerm::KSequence(parse_k_sequence(
                mac.tokens.clone(),
                StateMacroContext::Expression,
                invocation()?,
            )?)),
            "map" if !computation => Ok(StateTerm::Map(
                parse_map(
                    mac.tokens.clone(),
                    StateMacroContext::Expression,
                    invocation()?,
                )?
                .island_of(Some(mac.path.clone())),
            )),
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
    Ok(StateTerm::Term(TermExpression::parse_tokens(
        expression.to_token_stream(),
    )?))
}

/// Keys the initializer's cells, constructors, terms, and `k!`/`map!`
/// structure. Each role runs across the whole initializer, in the order
/// expansion visits the nodes (cells in declaration order, nested groups in
/// place), because a provenance key names one authored node of the sentence.
/// A cell's field and constructor are numbered as the cell is.
fn allocate_initializer_keys(
    keys: &mut KeyAllocator,
    cells: &mut [FixedCellInitializer],
) -> Result<(), SyntaxError> {
    for cell in cells {
        let range = TokenRange::for_tokens(&cell.field.member)?;
        let key = keys.key(ProvenanceRole::InitializerCell, range)?;
        cell.field_key = Some(keys.key(ProvenanceRole::InitializerField, range)?);
        match &mut cell.content {
            InitializerCellContent::Leaf {
                constructor,
                value,
                inferred_constructor,
                ..
            } => {
                cell.constructor_key = Some(keys.paired(
                    ProvenanceRole::InitializerCellConstructor,
                    &key,
                    if *inferred_constructor {
                        TokenRange::for_tokens(&cell.field.expr)?
                    } else {
                        TokenRange::for_tokens(&*constructor)?
                    },
                )?);
                allocate_state_term_keys(keys, value)?;
            }
            InitializerCellContent::Nested {
                constructor,
                children,
            } => {
                cell.constructor_key = Some(keys.paired(
                    ProvenanceRole::InitializerNestedConstructor,
                    &key,
                    TokenRange::for_tokens(&*constructor)?,
                )?);
                allocate_initializer_keys(keys, children)?;
            }
        }
        cell.key = Some(key);
    }
    Ok(())
}

/// The initializer's terms in expansion order: cells in order, a leaf's term,
/// a `k!`'s items, a `map!`'s key then value, an update's base, key, value.
fn initializer_terms_mut<'a>(
    cells: &'a mut [FixedCellInitializer],
    output: &mut Vec<&'a mut TermExpression>,
) {
    for cell in cells {
        match &mut cell.content {
            InitializerCellContent::Leaf { value, .. } => output.extend(value.terms_mut()),
            InitializerCellContent::Nested { children, .. } => {
                initializer_terms_mut(children, output);
            }
        }
    }
}

/// Keys a leaf's state: a `k!` or `map!` with the state macros' own pass,
/// under the standalone `k_sequence_*` and `map_*` roles, which an
/// initializer's states take, then each of its terms; or the leaf's term.
fn allocate_state_term_keys(
    keys: &mut KeyAllocator,
    value: &mut StateTerm,
) -> Result<(), SyntaxError> {
    match value {
        // Initializers hold templates only, never `Some`/`None` or instance lists.
        StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_) => Ok(()),
        StateTerm::Term(term) | StateTerm::Group(term) => allocate_term_keys(keys, term),
        StateTerm::KSequence(sequence) => {
            sequence.allocate_keys(keys, StatePosition::Standalone)?;
            for term in sequence.items_mut() {
                allocate_term_keys(keys, term)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => {
            map.allocate_keys(keys, StatePosition::Standalone)?;
            for term in map.terms_mut() {
                allocate_term_keys(keys, term)?;
            }
            Ok(())
        }
    }
}

/// Keys a term as an initializer term, then its paths.
fn allocate_term_keys(
    keys: &mut KeyAllocator,
    term: &mut TermExpression,
) -> Result<(), SyntaxError> {
    let range = TokenRange::for_tokens(term.expression())?;
    let (_, _, term_keys) = term.keying();
    term_keys.set_term(keys.key(ProvenanceRole::InitializerTerm, range)?);
    term.allocate_symbol_keys(keys, ProvenanceRole::InitializerTermPath)
}

fn append_initializer_candidates(
    cells: &[FixedCellInitializer],
    variables: &[ConfigurationVariable],
    output: &mut Vec<ReferenceCandidate>,
) {
    for cell in cells {
        match &cell.content {
            InitializerCellContent::Leaf {
                constructor,
                value,
                inferred_constructor,
                ..
            } => {
                if !inferred_constructor {
                    output.push(ReferenceCandidate {
                        key: cell.constructor_key.clone().expect(KEYED),
                        path: constructor.clone(),
                        kind: (),
                    });
                }
                for term in value.terms() {
                    append_term_candidates(term, variables, output);
                }
            }
            InitializerCellContent::Nested {
                constructor,
                children,
            } => {
                output.push(ReferenceCandidate {
                    key: cell.constructor_key.clone().expect(KEYED),
                    path: constructor.clone(),
                    kind: (),
                });
                append_initializer_candidates(children, variables, output);
            }
        }
    }
}

fn append_term_candidates(
    term: &TermExpression,
    variables: &[ConfigurationVariable],
    output: &mut Vec<ReferenceCandidate>,
) {
    for (index, symbol) in term.symbols().iter().enumerate() {
        if symbol.kind() == TermSymbolKind::Reference
            && variables.iter().any(|variable| {
                symbol.path().leading_colon.is_none()
                    && symbol.path().segments.len() == 1
                    && symbol.path().segments[0].ident == variable.binding
            })
        {
            continue;
        }
        output.push(ReferenceCandidate {
            key: term.keys().symbol(index).expect(KEYED).clone(),
            path: symbol.path().clone(),
            kind: (),
        });
    }
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

#[cfg(test)]
mod keyed {
    use super::{
        ConfigurationVariable, FixedCellInitializer, InitializerCellContent, InitializerFunction,
    };
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SortArgument, SyntaxError};

    impl ConfigurationVariable {
        /// Records the keys of the variable and its name, at its binding or
        /// authored name, its type and type arguments, and `main`.
        fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.key.as_ref(), &self.binding)?;
            if self.attribute.inferred_name {
                nodes.push_tokens(self.name_key.as_ref(), &self.binding)?;
            } else {
                nodes.push_tokens(self.name_key.as_ref(), &self.attribute.name)?;
            }
            nodes.push_tokens(self.type_key.as_ref(), &*self.parameter.ty)?;
            SortArgument::keyed_nodes(&self.arguments, nodes)?;
            if let Some(main) = &self.attribute.main {
                nodes.push_tokens(self.main_key.as_ref(), main)?;
            }
            Ok(())
        }
    }

    impl FixedCellInitializer {
        /// Records the keys of the cell and its field, at the field's name,
        /// of its constructor, then of its state or its children.
        fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.key.as_ref(), &self.field.member)?;
            nodes.push_tokens(self.field_key.as_ref(), &self.field.member)?;
            match &self.content {
                InitializerCellContent::Leaf {
                    constructor,
                    value,
                    inferred_constructor,
                    ..
                } => {
                    if *inferred_constructor {
                        nodes.push_tokens(self.constructor_key.as_ref(), &self.field.expr)?;
                    } else {
                        nodes.push_tokens(self.constructor_key.as_ref(), constructor)?;
                    }
                    value.keyed_nodes(nodes)?;
                }
                InitializerCellContent::Nested {
                    constructor,
                    children,
                } => {
                    nodes.push_tokens(self.constructor_key.as_ref(), constructor)?;
                    for child in children {
                        child.keyed_nodes(nodes)?;
                    }
                }
            }
            Ok(())
        }
    }

    impl InitializerFunction {
        /// Records the keys of the declaration, the result type, each
        /// configuration variable, the body, then each cell.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.declaration_key.as_ref(), &self.item.sig.ident)?;
            nodes.push_tokens(self.result_type_key.as_ref(), &self.result_type)?;
            for variable in &self.variables {
                variable.keyed_nodes(nodes)?;
            }
            nodes.push_tokens(self.body_key.as_ref(), &self.body)?;
            for cell in &self.cells {
                cell.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }
}
