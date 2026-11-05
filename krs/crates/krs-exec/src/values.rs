//! Typed values of a definition's terms, named by KRS declarations rather than emitted K names.
//!
//! A [`Value`] is host-side data for a ground term of the definition: a constructor application
//! named by the KRS declaration of its production, a builtin, a flattened collection, a token, or,
//! for anything that has no KRS description, the KORE pattern itself ([`Value::Opaque`]).
//! [`ValueIndex`] decodes backend results into values and encodes values as configuration
//! inputs; [`crate::Semantics::values`] returns the index of a loaded definition.
//!
//! Injections are not part of a value. In KORE, `inj{A, B}(a)` denotes `a` viewed in `B`, and
//! injections compose, so the sort a term sits at belongs to its position: decoding strips
//! injections, and encoding leaves them to the configuration assembler, which types a value as it
//! types parsed text. Constructors decode only when the backend treats their symbol as a free
//! constructor, or the application as data (a constructor an `anywhere` rule rewrites, applied
//! where no equation reduces it), and builtins have one canonical form each, so two ground values
//! are equal exactly when the terms they describe are.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, OnceLock};

use k_rust::{
    k_rust_backend::{
        builtin::canonical_float_text,
        data_term::DataHeads,
        definition::BackendDefinition,
        matching::SortGraph,
        term::{FunctionType, HeadRole, Sort as BackendSort, SymbolType},
    },
    kast::{Label, Sort as KastSort, Term as KastTerm, convert::Converter},
    kompile::{encode_kore_label, encode_kore_sort},
    kore::{
        ast::{KoreString, Pattern, Sort, Symbol},
        walk,
    },
    names::WellKnownSymbol,
};
use krs_ir::BuiltinSort;
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, SymbolId, SymbolIdentity,
};
use num_bigint::BigInt;

use crate::inputs::InputType;

/// The KRS declaration of a constructor or a sort: the Rust path of the item that declares it,
/// from its crate root (`sm83::machine::Register::A`).
///
/// It compares by path, so values decoded by two [`crate::Semantics`] of one definition are
/// interchangeable, and it does not change when the emitted K name of its symbol does.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Decl(Arc<str>);

impl Decl {
    /// The declaration's full path.
    #[must_use]
    pub fn path(&self) -> &str {
        &self.0
    }

    /// Whether `name` is the path or a `::`-aligned suffix of it (`Register::A`).
    fn is_named(&self, name: &str) -> bool {
        self.0.as_ref() == name
            || self
                .0
                .strip_suffix(name)
                .is_some_and(|prefix| prefix.ends_with("::"))
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

/// A sort, named by its KRS declaration or as one of K's builtin sorts.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SortRef {
    /// A sort declared in KRS.
    Declared(Decl),
    /// A sort of the K language.
    Builtin(BuiltinSort),
}

impl fmt::Display for SortRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared(decl) => decl.fmt(formatter),
            Self::Builtin(sort) => formatter.write_str(sort.k_name()),
        }
    }
}

/// A `Float` value, kept as the canonical text of its literal (`2.0000000000000000e+00p53x11`).
///
/// The format is part of the value, the zeros of the two signs are two values, and each format
/// has one NaN, so equality is the identity of the domain value, not `==Float`.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Float(String);

impl Float {
    /// The value a K `Float` literal names, in any of its spellings (`1.5`, `1.5f`, `0.15e1`,
    /// `1.5p53x11`).
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::Unencodable`] for a text that is no literal or a value k-rust
    /// does not compute.
    pub fn parse(literal: &str) -> Result<Self, ValueError> {
        canonical_float_text(literal)
            .map(Self)
            .map_err(|refusal| ValueError::Unencodable(format!("`{literal}`: {refusal:?}")))
    }

    /// The binary64 value of `value`.
    ///
    /// # Panics
    ///
    /// Never: every binary64 value, NaN and the infinities included, has a literal.
    #[must_use]
    pub fn from_f64(value: f64) -> Self {
        Self::parse(&ieee_literal(
            value.is_nan(),
            value.is_infinite(),
            value.is_sign_negative(),
            &format!("{value:e}"),
            "",
        ))
        .expect("every binary64 value has a literal")
    }

    /// The binary32 value of `value`.
    ///
    /// # Panics
    ///
    /// Never: every binary32 value, NaN and the infinities included, has a literal.
    #[must_use]
    pub fn from_f32(value: f32) -> Self {
        Self::parse(&ieee_literal(
            value.is_nan(),
            value.is_infinite(),
            value.is_sign_negative(),
            &format!("{value:e}"),
            "f",
        ))
        .expect("every binary32 value has a literal")
    }

    /// The canonical literal.
    #[must_use]
    pub fn literal(&self) -> &str {
        &self.0
    }

    /// The value as an `f64` when its format is binary64.
    #[must_use]
    pub fn to_f64(&self) -> Option<f64> {
        parse_ieee(self.0.strip_suffix("p53x11")?)
    }

    /// The value as an `f32` when its format is binary32.
    #[must_use]
    pub fn to_f32(&self) -> Option<f32> {
        parse_ieee(self.0.strip_suffix("p24x8")?)
    }
}

/// A K literal of an IEEE value: `NaN`, `Infinity` or `-Infinity`, or else `exponent_form`
/// (an exponent form `Float::parse` reads), then the format's `suffix`.
pub(crate) fn ieee_literal(
    nan: bool,
    infinite: bool,
    negative: bool,
    exponent_form: &str,
    suffix: &str,
) -> String {
    let body = if nan {
        "NaN".to_owned()
    } else if infinite {
        if negative { "-Infinity" } else { "Infinity" }.to_owned()
    } else {
        exponent_form.to_owned()
    };
    format!("{body}{suffix}")
}

fn parse_ieee<T: std::str::FromStr>(body: &str) -> Option<T> {
    match body {
        "NaN" => "NaN".parse().ok(),
        "Infinity" => "inf".parse().ok(),
        "-Infinity" => "-inf".parse().ok(),
        _ => body.parse().ok(),
    }
}

/// A constructor application, named by the KRS declaration of its production.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Ctor {
    decl: Decl,
    sort_args: Vec<SortRef>,
    fields: Vec<(Arc<str>, Value)>,
}

impl Ctor {
    /// The production's declaration.
    #[must_use]
    pub const fn decl(&self) -> &Decl {
        &self.decl
    }

    /// The sort arguments of a parametric production's application; empty otherwise.
    #[must_use]
    pub fn sort_args(&self) -> &[SortRef] {
        &self.sort_args
    }

    /// The fields in declaration order, named as in Rust (`"0"`, `"1"`, ... for a tuple variant).
    #[must_use]
    pub fn fields(&self) -> &[(Arc<str>, Value)] {
        &self.fields
    }

    /// The field named `name`.
    #[must_use]
    pub fn field(&self, name: &str) -> Option<&Value> {
        self.fields
            .iter()
            .find(|(field, _)| field.as_ref() == name)
            .map(|(_, value)| value)
    }
}

/// A term of the definition as data.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Value {
    /// A constructor application.
    Ctor(Ctor),
    /// An `Int`.
    Int(BigInt),
    /// A `Bool`.
    Bool(bool),
    /// A `String`.
    String(String),
    /// A `Bytes`.
    Bytes(Vec<u8>),
    /// A `Float`.
    Float(Float),
    /// A domain value of a sort without a builtin hook (an identifier, a KRS token sort).
    Token {
        /// The token's sort.
        sort: SortRef,
        /// The token text.
        text: String,
    },
    /// A K sequence (`.K`, `A ~> B`), the content of a `K`-sorted cell.
    Seq(Vec<Value>),
    /// A `List`.
    List(Vec<Value>),
    /// A `Set`.
    Set(BTreeSet<Value>),
    /// A `Map`.
    Map(BTreeMap<Value, Value>),
    /// A term with no KRS description, kept as its KORE pattern: a variable, an unevaluated
    /// function application, a matching-logic connective, a constructor that no KRS declaration
    /// names (a strictness freezer, a K-internal constructor), or a collection with a part that
    /// is neither an element nor a unit.
    Opaque(Pattern),
}

impl Value {
    /// A `Map` of `entries`; a later entry replaces an earlier one with an equal key.
    pub fn map(entries: impl IntoIterator<Item = (Self, Self)>) -> Self {
        Self::Map(entries.into_iter().collect())
    }

    /// A `List` of `items`.
    pub fn list(items: impl IntoIterator<Item = Self>) -> Self {
        Self::List(items.into_iter().collect())
    }

    /// A `Set` of `items`.
    pub fn set(items: impl IntoIterator<Item = Self>) -> Self {
        Self::Set(items.into_iter().collect())
    }

    /// A K sequence of `items`.
    pub fn seq(items: impl IntoIterator<Item = Self>) -> Self {
        Self::Seq(items.into_iter().collect())
    }

    /// The `Int`, if this is one.
    #[must_use]
    pub const fn as_int(&self) -> Option<&BigInt> {
        match self {
            Self::Int(value) => Some(value),
            _ => None,
        }
    }

    /// The `Int` as an `i64`, if this is one that fits.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        self.as_int().and_then(|value| i64::try_from(value).ok())
    }

    /// The `Bool`, if this is one.
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// The `String`, if this is one.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    /// The `Bytes`, if this is one.
    #[must_use]
    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Self::Bytes(value) => Some(value),
            _ => None,
        }
    }

    /// The `Float`, if this is one.
    #[must_use]
    pub const fn as_float(&self) -> Option<&Float> {
        match self {
            Self::Float(value) => Some(value),
            _ => None,
        }
    }

    /// The constructor application, if this is one.
    #[must_use]
    pub const fn as_ctor(&self) -> Option<&Ctor> {
        match self {
            Self::Ctor(value) => Some(value),
            _ => None,
        }
    }

    /// The items of a `List`, if this is one.
    #[must_use]
    pub fn as_list(&self) -> Option<&[Self]> {
        match self {
            Self::List(items) => Some(items),
            _ => None,
        }
    }

    /// The items of a K sequence, if this is one.
    #[must_use]
    pub fn as_seq(&self) -> Option<&[Self]> {
        match self {
            Self::Seq(items) => Some(items),
            _ => None,
        }
    }

    /// The items of a `Set`, if this is one.
    #[must_use]
    pub const fn as_set(&self) -> Option<&BTreeSet<Self>> {
        match self {
            Self::Set(items) => Some(items),
            _ => None,
        }
    }

    /// The entries of a `Map`, if this is one.
    #[must_use]
    pub const fn as_map(&self) -> Option<&BTreeMap<Self, Self>> {
        match self {
            Self::Map(entries) => Some(entries),
            _ => None,
        }
    }

    /// Whether the value holds no variable: every opaque part is a ground pattern.
    #[must_use]
    pub fn is_ground(&self) -> bool {
        match self {
            Self::Ctor(ctor) => ctor.fields.iter().all(|(_, value)| value.is_ground()),
            Self::Seq(items) | Self::List(items) => items.iter().all(Self::is_ground),
            Self::Set(items) => items.iter().all(Self::is_ground),
            Self::Map(entries) => entries
                .iter()
                .all(|(key, value)| key.is_ground() && value.is_ground()),
            Self::Opaque(pattern) => !has_variable(pattern),
            Self::Int(_)
            | Self::Bool(_)
            | Self::String(_)
            | Self::Bytes(_)
            | Self::Float(_)
            | Self::Token { .. } => true,
        }
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Self::Int(value.into())
    }
}

impl From<BigInt> for Value {
    fn from(value: BigInt) -> Self {
        Self::Int(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<Vec<u8>> for Value {
    fn from(value: Vec<u8>) -> Self {
        Self::Bytes(value)
    }
}

impl From<Float> for Value {
    fn from(value: Float) -> Self {
        Self::Float(value)
    }
}

fn has_variable(pattern: &Pattern) -> bool {
    let mut stack = vec![pattern];
    while let Some(pattern) = stack.pop() {
        match pattern {
            Pattern::Variable(_) => return true,
            Pattern::Exists { .. }
            | Pattern::Forall { .. }
            | Pattern::Mu { .. }
            | Pattern::Nu { .. } => {
                return true;
            }
            _ => stack.extend(walk::children(pattern)),
        }
    }
    false
}

/// Why a name, a value, or a pattern has no reading in this definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValueError {
    /// No constructor or sort has this name.
    UnknownName {
        /// What was looked up: `constructor` or `sort`.
        kind: &'static str,
        /// The name as written.
        name: String,
        /// Declarations whose last segment matches, to suggest.
        candidates: Vec<String>,
    },
    /// The name names a production of the other kind: a function where a constructor was
    /// asked for, or a constructor where a function was.
    WrongKind {
        /// The production the name resolves to.
        decl: String,
        /// Whether that production is a function.
        function: bool,
    },
    /// The name is a suffix of several declarations' paths.
    AmbiguousName {
        /// The name as written.
        name: String,
        /// The matching declarations.
        candidates: Vec<String>,
    },
    /// A constructor's fields do not match its declaration.
    Fields {
        /// The constructor.
        decl: String,
        /// The declared fields, in order.
        expected: Vec<String>,
        /// The supplied fields, in order.
        found: Vec<String>,
    },
    /// A value that is no term of this definition.
    Unencodable(String),
    /// A pattern that is no term or state of this definition.
    Malformed(String),
}

impl fmt::Display for ValueError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownName {
                kind,
                name,
                candidates,
            } => {
                write!(formatter, "no {kind} is named `{name}`")?;
                if !candidates.is_empty() {
                    write!(formatter, "; did you mean {}?", candidates.join(", "))?;
                }
                Ok(())
            }
            Self::WrongKind {
                decl,
                function: true,
            } => write!(
                formatter,
                "`{decl}` is a function; apply it with ValueIndex::call or {{\"$call\": {{\"{decl}\": ..}}}}"
            ),
            Self::WrongKind {
                decl,
                function: false,
            } => write!(
                formatter,
                "`{decl}` is a constructor; build it with ValueIndex::ctor, or write it without $call"
            ),
            Self::AmbiguousName { name, candidates } => write!(
                formatter,
                "`{name}` names several declarations: {}",
                candidates.join(", ")
            ),
            Self::Fields {
                decl,
                expected,
                found,
            } => write!(
                formatter,
                "`{decl}` has fields ({}), not ({})",
                expected.join(", "),
                found.join(", ")
            ),
            Self::Unencodable(message) => {
                write!(formatter, "value is no term of the definition: {message}")
            }
            Self::Malformed(message) => {
                write!(formatter, "pattern is no term of the definition: {message}")
            }
        }
    }
}

impl std::error::Error for ValueError {}

/// A production of the definition that a KRS declaration names: a constructor, or a function
/// (`function`).
#[derive(Debug)]
pub(crate) struct CtorInfo {
    pub(crate) decl: Decl,
    /// The KORE symbol name.
    symbol: String,
    pub(crate) fields: Vec<Arc<str>>,
    /// Each field's declared type, in field order: its sort and, for a typed collection, the
    /// element types the declaration states (`Map<Reg8, Int>`), as a parameter's or a cell's
    /// type is; `None` for a sort no KRS declaration and no builtin names (a cell sort, a sort
    /// parameter).
    pub(crate) field_types: Vec<Option<InputType>>,
    /// The result's declared type, with the same `None`.
    pub(crate) result: Option<InputType>,
    /// Whether the production is a function (`#[k::function]`, a `fn` declaration): its
    /// application is computed by the definition's equations, not data.
    pub(crate) function: bool,
    pub(crate) parameters: usize,
}

/// The declared type of a production's field or result: the sort `sort_ref` names and the element
/// types the declaration states. An element type whose sort KRS names none of (a sort parameter,
/// a cell sort) is the untyped position, which takes any term, so the type never claims more than
/// the declaration states; a position whose own sort KRS names none of has no type.
fn position_type(
    sort_ref: &impl Fn(&DefinitionSortRef) -> Option<SortRef>,
    sort: &DefinitionSortRef,
    arguments: &[krs_ir::CellSortArgument<DefinitionSortRef>],
) -> Option<InputType> {
    Some(InputType {
        sort: sort_ref(sort)?,
        arguments: arguments
            .iter()
            .map(|argument| {
                position_type(sort_ref, &argument.sort, &argument.arguments)
                    .unwrap_or_else(InputType::untyped)
            })
            .collect(),
    })
}

/// One collection kind's builder symbols, by KORE name.
#[derive(Debug, Default)]
struct CollectionSymbols {
    unit: Option<String>,
    element: Option<String>,
    concat: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Collection {
    List,
    Set,
    Map,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role {
    Unit,
    Element,
    Concat,
}

/// One cell of the configuration, addressed by the Rust field that declares it.
#[derive(Debug)]
pub(crate) struct CellNode {
    pub(crate) field: String,
    /// The KORE symbol of the cell's label.
    pub(crate) symbol: String,
    pub(crate) multiplicity: Option<krs_ir::CellMultiplicity>,
    /// A repeated cell's collection type: whether its instances are a list, a set or a map.
    pub(crate) collection: Option<krs_ir::CellCollectionType>,
    /// Whether the cell itself carries `unobservable`; a cell inside an unobservable cell is
    /// unobservable too ([`crate::Semantics::cells`]).
    pub(crate) unobservable: bool,
    pub(crate) children: Vec<CellNode>,
    /// A leaf cell's declared content sort and its element types, as the Definition IR states
    /// them; `None` for a group cell.
    pub(crate) content: Option<(
        DefinitionSortRef,
        Vec<krs_ir::CellSortArgument<DefinitionSortRef>>,
    )>,
}

/// The backend's symbol table as decoding and encoding read it.
struct BackendSymbols {
    known: HashSet<String>,
    free_constructors: HashSet<String>,
    /// The partial functions whose definition is their equations alone: declared `function`,
    /// not `total`, with no hook, `smt-hook` or `smtlib`, and evaluated by the definition's
    /// equations, each of which is decided at values ([`crate::decided`], [`crate::valueless`]).
    equational_partial: HashSet<String>,
    /// The hook of each declared function symbol that has one (`MAP.keys_list`).
    hooked_functions: HashMap<String, String>,
    /// The builtin collections' unit, element and concatenation symbols.
    collection_builders: HashSet<String>,
    /// The constructors an `anywhere` rule rewrites: the backend evaluates their applications
    /// as a function's, so one is a value of its constructor only where it is data
    /// ([`EquationHeadData`]).
    equation_heads: HashSet<String>,
    /// The result sort of each symbol whose result sort is a sort without parameters.
    result_sorts: HashMap<String, String>,
    collections: HashMap<String, (Collection, Role)>,
    builders: [CollectionSymbols; 3],
}

impl BackendSymbols {
    fn scan(backend: &BackendDefinition) -> Self {
        let mut known = HashSet::new();
        let mut free_constructors = HashSet::new();
        let mut equational_partial = HashSet::new();
        let mut hooked_functions = HashMap::new();
        let mut collection_builders = HashSet::new();
        let mut equation_heads = HashSet::new();
        let mut result_sorts = HashMap::new();
        let mut collections = HashMap::new();
        let mut builders: [CollectionSymbols; 3] = Default::default();
        for (name, symbol) in backend.symbols() {
            let name = name.to_string();
            known.insert(name.clone());
            match symbol.attributes.head_role() {
                HeadRole::FreeConstructor => {
                    free_constructors.insert(name.clone());
                }
                HeadRole::EquationHead => {
                    equation_heads.insert(name.clone());
                }
                HeadRole::Function { declared: true, .. }
                    if symbol.attributes.symbol_type
                        == SymbolType::Function(FunctionType::Partial)
                        && symbol.attributes.hook.is_none()
                        && symbol.attributes.smt.is_none()
                        && symbol.attributes.has_evaluators =>
                {
                    equational_partial.insert(name.clone());
                }
                HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {}
            }
            if matches!(
                symbol.attributes.head_role(),
                HeadRole::Function { declared: true, .. }
            ) && let Some(hook) = &symbol.attributes.hook
            {
                hooked_functions.insert(name.clone(), hook.to_string());
            }
            if symbol.attributes.collection.is_some() {
                collection_builders.insert(name.clone());
            }
            if let k_rust::k_rust_backend::term::SortNode::Application {
                name: sort,
                arguments,
            } = symbol.result_sort.node()
                && arguments.is_empty()
            {
                result_sorts.insert(name.clone(), sort.to_string());
            }
            let Some(hook) = symbol.attributes.hook.as_ref().map(ToString::to_string) else {
                continue;
            };
            let Some((namespace, operation)) = hook.split_once('.') else {
                continue;
            };
            let collection = match namespace {
                "LIST" => Collection::List,
                "SET" => Collection::Set,
                "MAP" => Collection::Map,
                _ => continue,
            };
            let role = match operation {
                "unit" => Role::Unit,
                "element" => Role::Element,
                "concat" => Role::Concat,
                _ => continue,
            };
            collections.insert(name.clone(), (collection, role));
            // The builders of a value are the symbols of K's own collection sort; a cell
            // collection has symbols with the same hooks at its own sort.
            let own_sort = match collection {
                Collection::List => BuiltinSort::List,
                Collection::Set => BuiltinSort::Set,
                Collection::Map => BuiltinSort::Map,
            };
            let result = match symbol.result_sort.node() {
                k_rust::k_rust_backend::term::SortNode::Application { name, .. } => {
                    name.to_string()
                }
                k_rust::k_rust_backend::term::SortNode::Variable(_) => continue,
            };
            if result == kore_sort_name(own_sort.k_name()) {
                let slot = &mut builders[collection_slot(collection)];
                let target = match role {
                    Role::Unit => &mut slot.unit,
                    Role::Element => &mut slot.element,
                    Role::Concat => &mut slot.concat,
                };
                *target = Some(name);
            }
        }
        let equational_partial = crate::decided::decided_at_values(backend, &equational_partial);
        Self {
            known,
            free_constructors,
            equational_partial,
            hooked_functions,
            collection_builders,
            equation_heads,
            result_sorts,
            collections,
            builders,
        }
    }
}

/// The decoding and encoding tables of one loaded definition, built once by
/// [`crate::Semantics`] and shared by every [`crate::View`] of its results.
#[derive(Debug)]
pub struct ValueIndex {
    ctors_by_symbol: HashMap<String, Arc<CtorInfo>>,
    /// Every production a KRS declaration names, constructors and functions alike.
    ctors_by_decl: HashMap<Decl, Arc<CtorInfo>>,
    sorts_by_kore: HashMap<String, SortRef>,
    kore_by_sort: HashMap<SortRef, String>,
    /// The KRS sorts by the IR's symbol identity.
    sorts_by_symbol: HashMap<SymbolId, SortRef>,
    /// The token sorts: K's `Id` and every sort a token production (`#[k::token]`) declares.
    token_sorts: BTreeSet<SortRef>,
    /// The backend's sort lattice.
    sort_graph: SortGraph,
    /// Hooks of the backend's sorts, by KORE name.
    sort_hooks: HashMap<String, String>,
    /// Hooks of the backend's sorts, by KAST name, for the KAST conversion of an encoded value.
    kast_sort_hooks: HashMap<String, String>,
    known_symbols: HashSet<String>,
    free_constructors: HashSet<String>,
    equational_partial: HashSet<String>,
    hooked_functions: HashMap<String, String>,
    collection_builders: HashSet<String>,
    equation_heads: HashSet<String>,
    equation_head_data: EquationHeadData,
    result_sorts: HashMap<String, String>,
    collections: HashMap<String, (Collection, Role)>,
    builders: [CollectionSymbols; 3],
    cells: Vec<CellNode>,
    top: String,
    /// The definition's overload axioms, which a printed term is compared modulo.
    overloads: crate::overloads::Overloads,
}

/// Whether an application of an equation head (a constructor an `anywhere` rule rewrites) is a
/// value of its constructor: where the backend shows it is data
/// ([`BackendDefinition::is_data`]). Such a head's applications are evaluated as a function's
/// are, and its `value-production` declaration states that an application no equation reduces is
/// a value of its sort; an application an equation still reduces (a state a run left unreduced) is
/// no value, whatever its symbol, and neither is one whose head the load withdrew value claims
/// from. The definition's data heads are computed on the first such application decoded.
struct EquationHeadData {
    definition: Arc<BackendDefinition>,
    heads: OnceLock<DataHeads>,
}

impl fmt::Debug for EquationHeadData {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EquationHeadData")
            .field("heads", &self.heads.get())
            .finish_non_exhaustive()
    }
}

impl EquationHeadData {
    fn new(definition: Arc<BackendDefinition>) -> Self {
        Self {
            definition,
            heads: OnceLock::new(),
        }
    }

    /// Whether the ground application `pattern` is data in the definition.
    fn holds(&self, pattern: &Pattern) -> bool {
        let Ok(term) = self
            .definition
            .admit_unverified(pattern, &[])
            .internalize_term()
        else {
            return false;
        };
        let heads = self.heads.get_or_init(|| self.definition.data_heads());
        self.definition.is_data(&term, heads)
    }
}

const fn collection_slot(collection: Collection) -> usize {
    match collection {
        Collection::List => 0,
        Collection::Set => 1,
        Collection::Map => 2,
    }
}

pub(crate) fn kore_sort_name(k_name: &str) -> String {
    match &encode_kore_sort(&KastSort::new(k_name)) {
        Sort::Application { name, .. } | Sort::Variable(name) => name.clone(),
    }
}

fn kore_symbol_name(label: &str) -> String {
    encode_kore_label(&Label::new(label)).name
}

fn decl_of(symbol: &SymbolIdentity) -> Option<Decl> {
    symbol
        .declaration()
        .map(|path| Decl(Arc::from(path.to_string())))
}

impl crate::valueless::Heads for ValueIndex {
    fn is_equational_partial(&self, symbol: &str) -> bool {
        self.equational_partial.contains(symbol)
    }

    fn is_data(&self, symbol: &str) -> bool {
        symbol == WellKnownSymbol::Inj.as_str()
            || self.free_constructors.contains(symbol)
            || self.collection_builders.contains(symbol)
    }
}

impl ValueIndex {
    /// Index the KRS declarations of `definition` against the backend's view of its compiled KORE.
    #[expect(
        clippy::too_many_lines,
        reason = "one pass over the declarations fills every table of the index"
    )]
    pub(crate) fn new(
        definition: &DefinitionIr,
        backend: &Arc<BackendDefinition>,
        kast_sort_hooks: &HashMap<String, String>,
    ) -> Self {
        let mut ctors_by_symbol = HashMap::new();
        let mut ctors_by_decl = HashMap::new();
        let mut sorts_by_kore = HashMap::new();
        let mut sorts_by_symbol = HashMap::new();
        let mut token_sorts = BTreeSet::from([SortRef::Builtin(BuiltinSort::Id)]);
        let mut cells = Vec::new();
        for sort in BuiltinSort::ALL {
            sorts_by_kore.insert(kore_sort_name(sort.k_name()), SortRef::Builtin(sort));
        }
        // The sorts first, so that a production's field and result sorts resolve wherever the
        // sort is declared.
        for sentence in definition
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
        {
            if let DefinitionSentence::SyntaxSort(sort) = sentence
                && let Some(decl) = decl_of(sort.symbol())
            {
                sorts_by_kore.insert(
                    kore_sort_name(sort.symbol().emitted_name()),
                    SortRef::Declared(decl.clone()),
                );
                sorts_by_symbol.insert(sort.symbol().id().clone(), SortRef::Declared(decl));
            }
        }
        let sort_ref = |sort: &DefinitionSortRef| match sort {
            DefinitionSortRef::Builtin(builtin) => Some(SortRef::Builtin(*builtin)),
            DefinitionSortRef::Declared(symbol) => sorts_by_symbol.get(symbol).cloned(),
            DefinitionSortRef::Cell(_) | DefinitionSortRef::Parameter(_) => None,
        };
        for module in definition.modules() {
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::Production(production) => {
                        let attributes = production.attributes();
                        if attributes.iter().any(|attribute| {
                            matches!(attribute, krs_ir::ProductionAttribute::Token { .. })
                        }) {
                            // A token production declares its sort's lexical syntax; its values
                            // are domain values, not applications.
                            if let Some(sort) = sort_ref(production.result_sort()) {
                                token_sorts.insert(sort);
                            }
                            continue;
                        }
                        let Some(decl) = decl_of(production.symbol()) else {
                            continue;
                        };
                        let (fields, field_types) = production
                            .items()
                            .iter()
                            .filter_map(|item| match item.kind() {
                                krs_ir::GrammarProductionItemKind::NonTerminal { field, sort } => {
                                    Some((
                                        Arc::from(field.as_str()),
                                        position_type(
                                            &sort_ref,
                                            sort,
                                            production.field_arguments(field),
                                        ),
                                    ))
                                }
                                _ => None,
                            })
                            .unzip();
                        let info = Arc::new(CtorInfo {
                            decl: decl.clone(),
                            symbol: kore_symbol_name(production.symbol().emitted_name()),
                            fields,
                            field_types,
                            result: position_type(
                                &sort_ref,
                                production.result_sort(),
                                production.result_arguments(),
                            ),
                            function: attributes.iter().any(|attribute| {
                                matches!(attribute, krs_ir::ProductionAttribute::Function { .. })
                            }),
                            parameters: production.parameters().len(),
                        });
                        ctors_by_symbol.insert(info.symbol.clone(), info.clone());
                        ctors_by_decl.insert(decl, info);
                    }
                    DefinitionSentence::Configuration(configuration) => {
                        cells = cell_nodes(configuration.cells());
                    }
                    _ => {}
                }
            }
        }
        let kore_by_sort = sorts_by_kore
            .iter()
            .map(|(kore, sort)| (sort.clone(), kore.clone()))
            .collect();
        let sort_hooks: HashMap<String, String> = backend
            .sorts()
            .iter()
            .filter_map(|(name, sort)| Some((name.to_string(), sort.hook.as_ref()?.to_string())))
            .collect();
        let symbols = BackendSymbols::scan(backend);
        Self {
            overloads: crate::overloads::Overloads::new(backend.axioms()),
            ctors_by_symbol,
            ctors_by_decl,
            sorts_by_kore,
            kore_by_sort,
            sorts_by_symbol,
            token_sorts,
            sort_graph: backend.sort_graph().clone(),
            sort_hooks,
            kast_sort_hooks: kast_sort_hooks.clone(),
            known_symbols: symbols.known,
            free_constructors: symbols.free_constructors,
            equational_partial: symbols.equational_partial,
            hooked_functions: symbols.hooked_functions,
            collection_builders: symbols.collection_builders,
            equation_heads: symbols.equation_heads,
            equation_head_data: EquationHeadData::new(Arc::clone(backend)),
            result_sorts: symbols.result_sorts,
            collections: symbols.collections,
            builders: symbols.builders,
            cells,
            top: kore_symbol_name(k_rust::kast::GeneratedCell::Top.label()),
        }
    }

    /// The definition's overload axioms ([`crate::overloads`]).
    pub(crate) const fn overloads(&self) -> &crate::overloads::Overloads {
        &self.overloads
    }

    /// The constructor named by `name`: its full path or a `::`-aligned suffix of it
    /// (`Register::A`), among the constructor productions; a function is no constructor.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::UnknownName`] or [`ValueError::AmbiguousName`]; the former, when
    /// `name` names a function, says so.
    pub fn decl(&self, name: &str) -> Result<Decl, ValueError> {
        self.production(name, false)
    }

    /// The function production named by `name`, as [`Self::decl`] names a constructor.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::UnknownName`] or [`ValueError::AmbiguousName`]; the former, when
    /// `name` names a constructor, says so.
    pub fn function_decl(&self, name: &str) -> Result<Decl, ValueError> {
        self.production(name, true)
    }

    /// The production named by `name` among the functions (`function`) or the constructors.
    fn production(&self, name: &str, function: bool) -> Result<Decl, ValueError> {
        let of_kind = |wanted: bool| {
            self.ctors_by_decl
                .iter()
                .filter(move |(_, info)| info.function == wanted)
                .map(|(decl, _)| decl)
        };
        let kind = if function { "function" } else { "constructor" };
        resolve(kind, name, of_kind(function)).map_err(|error| {
            if matches!(error, ValueError::UnknownName { .. })
                && let Ok(other) = resolve(kind, name, of_kind(!function))
            {
                ValueError::WrongKind {
                    decl: other.to_string(),
                    function: !function,
                }
            } else {
                error
            }
        })
    }

    /// Whether the loaded definition holds the production `decl` names: a declaration of a
    /// package whose module the main module does not import is in the Definition IR but not in
    /// the definition.
    pub(crate) fn is_loaded(&self, decl: &Decl) -> bool {
        self.ctors_by_decl
            .get(decl)
            .is_some_and(|info| self.known_symbols.contains(&info.symbol))
    }

    /// The production a KRS declaration names, constructor or function.
    pub(crate) fn info(&self, decl: &Decl) -> Option<&CtorInfo> {
        self.ctors_by_decl.get(decl).map(AsRef::as_ref)
    }

    /// Every production a KRS declaration names, constructors and functions alike.
    pub(crate) fn productions(&self) -> impl Iterator<Item = &CtorInfo> {
        self.ctors_by_decl.values().map(AsRef::as_ref)
    }

    /// The KRS sort the IR's sort reference names, when one does: a builtin, or a declared sort
    /// with a KRS declaration.
    pub(crate) fn sort_ref(&self, sort: &DefinitionSortRef) -> Option<SortRef> {
        match sort {
            DefinitionSortRef::Builtin(builtin) => Some(SortRef::Builtin(*builtin)),
            DefinitionSortRef::Declared(symbol) => self.sorts_by_symbol.get(symbol).cloned(),
            DefinitionSortRef::Cell(_) | DefinitionSortRef::Parameter(_) => None,
        }
    }

    /// The KRS sort of a KORE sort name, when one names it.
    pub(crate) fn sort_of_kore(&self, kore: &str) -> Option<SortRef> {
        self.sorts_by_kore.get(kore).cloned()
    }

    /// Whether `sort` is a token sort: K's `Id`, or a sort of a `#[k::token]` declaration.
    pub(crate) fn is_token_sort(&self, sort: &SortRef) -> bool {
        self.token_sorts.contains(sort)
    }

    /// The token sorts.
    pub(crate) fn token_sorts(&self) -> impl Iterator<Item = &SortRef> {
        self.token_sorts.iter()
    }

    /// Whether `sub` is at most `sup` in the definition's sort lattice; `None` where the lattice
    /// gives no answer (a sort it does not declare).
    pub(crate) fn is_subsort(&self, sub: &SortRef, sup: &SortRef) -> Option<bool> {
        if sub == sup {
            return Some(true);
        }
        let sub = self.kore_by_sort.get(sub)?;
        let sup = self.kore_by_sort.get(sup)?;
        self.sort_graph
            .check_subsort(
                &BackendSort::simple(sub.as_str()),
                &BackendSort::simple(sup.as_str()),
            )
            .ok()
    }

    /// A sort as a KRS author writes it: a KRS sort's last path segment, a builtin's K name.
    pub(crate) fn sort_name(sort: &SortRef) -> String {
        match sort {
            SortRef::Declared(decl) => decl
                .path()
                .rsplit("::")
                .next()
                .unwrap_or(decl.path())
                .to_owned(),
            SortRef::Builtin(sort) => sort.k_name().to_owned(),
        }
    }

    /// The sort named by `name`: a KRS sort's path or suffix, or a builtin sort's K name.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::UnknownName`] or [`ValueError::AmbiguousName`].
    pub fn sort(&self, name: &str) -> Result<SortRef, ValueError> {
        if let Some(sort) = BuiltinSort::ALL
            .into_iter()
            .find(|sort| sort.k_name() == name)
        {
            return Ok(SortRef::Builtin(sort));
        }
        let declared = self.kore_by_sort.keys().filter_map(|sort| match sort {
            SortRef::Declared(decl) => Some(decl),
            SortRef::Builtin(_) => None,
        });
        resolve("sort", name, declared).map(SortRef::Declared)
    }

    /// The application of the constructor named `name` (as [`Self::decl`] resolves it) to
    /// `fields`, given by name in any order.
    ///
    /// A function production is no constructor: its application is computed, not data, and
    /// [`Self::call`] builds it.
    ///
    /// # Errors
    ///
    /// Returns a name error ([`ValueError::WrongKind`] for a function), [`ValueError::Fields`]
    /// when the names are not exactly the declared fields, or [`ValueError::Unencodable`] for a
    /// parametric production, whose sort arguments this builder does not take.
    pub fn ctor<'a>(
        &self,
        name: &str,
        fields: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Result<Value, ValueError> {
        let decl = self.decl(name)?;
        self.apply(decl, fields)
    }

    /// The application of the function named `name` (as [`Self::function_decl`] resolves it)
    /// to `fields`, its parameters given by name in any order: the term whose value the
    /// definition's equations compute, which a configuration given it holds unevaluated until
    /// the first state is simplified, before the first step.
    ///
    /// # Errors
    ///
    /// Returns a name error ([`ValueError::WrongKind`] for a constructor), or the errors of
    /// [`Self::ctor`] for the fields and parametric productions.
    pub fn call<'a>(
        &self,
        name: &str,
        fields: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Result<Value, ValueError> {
        let decl = self.function_decl(name)?;
        if let Some(reason) = self.instance_function(&decl) {
            return Err(ValueError::Unencodable(reason));
        }
        self.apply(decl, fields)
    }

    /// Why the function `decl` cannot be applied outside a sentence, where it is evaluated in
    /// one instance of a Map collection: it receives that instance's key as a hidden argument
    /// (`krs_ir_levels::k_surface::instance_key_field`), and an input is evaluated in no instance.
    /// `None` for every other production.
    pub(crate) fn instance_function(&self, decl: &Decl) -> Option<String> {
        let holders = self
            .ctors_by_decl
            .get(decl)?
            .fields
            .iter()
            .filter_map(|field| krs_ir_levels::k_surface::instance_key_holder(field))
            .map(|holder| format!("`{holder}`"))
            .collect::<Vec<_>>();
        (!holders.is_empty()).then(|| {
            format!(
                "`{decl}` is evaluated in one instance of the Map collection cell {} (its function context reads that instance, or the context of a function it applies does), so it receives the instance's key, and an input is evaluated in no instance: a function has one value for its arguments, so it is applied only from a sentence about one instance",
                holders.join(" and ")
            )
        })
    }

    /// The application of the production `decl` to `fields`, given by name in any order.
    fn apply<'a>(
        &self,
        decl: Decl,
        fields: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Result<Value, ValueError> {
        let info = &self.ctors_by_decl[&decl];
        if info.parameters != 0 {
            return Err(ValueError::Unencodable(format!(
                "`{decl}` is a parametric production; decode one of its values instead"
            )));
        }
        let mut supplied: Vec<(&str, Value)> = fields.into_iter().collect();
        let found = supplied
            .iter()
            .map(|(name, _)| (*name).to_owned())
            .collect::<Vec<_>>();
        let mismatch = || ValueError::Fields {
            decl: decl.to_string(),
            expected: info.fields.iter().map(ToString::to_string).collect(),
            found: found.clone(),
        };
        if supplied.len() != info.fields.len() {
            return Err(mismatch());
        }
        let mut ordered = Vec::with_capacity(info.fields.len());
        for field in &info.fields {
            let position = supplied
                .iter()
                .position(|(name, _)| *name == field.as_ref())
                .ok_or_else(mismatch)?;
            ordered.push((field.clone(), supplied.swap_remove(position).1));
        }
        Ok(Value::Ctor(Ctor {
            decl,
            sort_args: Vec::new(),
            fields: ordered,
        }))
    }

    pub(crate) fn cells(&self) -> &[CellNode] {
        &self.cells
    }

    pub(crate) fn top_symbol(&self) -> &str {
        &self.top
    }

    /// The KORE name of the sort of a ground term, below its injections: a domain value's sort,
    /// or the result sort its symbol declares, which bounds every value an unevaluated function
    /// application can take. `None` for a variable, a connective, and a symbol whose result
    /// sort has parameters or sort variables.
    pub(crate) fn sort_of(&self, pattern: &Pattern) -> Option<String> {
        match strip_injections(pattern) {
            Pattern::DomainValue {
                sort: Sort::Application { name, arguments },
                ..
            } if arguments.is_empty() => Some(name.clone()),
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => {
                self.result_sorts.get(&symbol.name).cloned()
            }
            _ => None,
        }
    }

    /// The arguments of each element of a `sort` collection built from its unit, element, and
    /// concatenation symbols, below its injections: one argument per `List` or `Set` element, a
    /// key and a value per `Map` entry. `None` when `sort` is no collection or a part of the
    /// term is neither (a function application, a variable).
    pub(crate) fn collection_items<'p>(
        &self,
        pattern: &'p Pattern,
        sort: BuiltinSort,
    ) -> Option<Vec<Vec<&'p Pattern>>> {
        let collection = match sort {
            BuiltinSort::List => Collection::List,
            BuiltinSort::Set => Collection::Set,
            BuiltinSort::Map => Collection::Map,
            _ => return None,
        };
        let mut elements = Vec::new();
        self.collection_elements(strip_injections(pattern), collection, &mut elements)
            .then_some(elements)
    }

    /// A KORE sort's name as a KRS author writes it: the last segment of a KRS sort's Rust
    /// path, a builtin sort's K name, or else the K name the KORE name encodes.
    pub(crate) fn sort_display(&self, kore: &str) -> String {
        match self.sorts_by_kore.get(kore) {
            Some(SortRef::Declared(decl)) => decl
                .path()
                .rsplit("::")
                .next()
                .unwrap_or(decl.path())
                .to_owned(),
            Some(SortRef::Builtin(sort)) => sort.k_name().to_owned(),
            None => kore.strip_prefix("Sort").unwrap_or(kore).to_owned(),
        }
    }

    /// Decode a pattern of this definition.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::Malformed`] for a pattern that cannot be a term of this definition:
    /// a symbol it does not declare, a constructor with the wrong number of arguments, or a
    /// literal its builtin sort does not have.
    pub fn decode(&self, pattern: &Pattern) -> Result<Value, ValueError> {
        let opaque = || Ok(Value::Opaque(pattern.clone()));
        match pattern {
            Pattern::DomainValue { sort, value } => self.domain_value(pattern, sort, value),
            Pattern::Application { symbol, arguments }
            | Pattern::AssociativeApplication {
                symbol, arguments, ..
            } => {
                let name = symbol.name.as_str();
                if name == WellKnownSymbol::Inj.as_str() {
                    let [argument] = arguments.as_slice() else {
                        return Err(ValueError::Malformed(format!("{pattern}")));
                    };
                    return Ok(match self.decode(argument)? {
                        Value::Opaque(_) => Value::Opaque(pattern.clone()),
                        value => value,
                    });
                }
                if name == WellKnownSymbol::KSeq.as_str()
                    || name == WellKnownSymbol::Append.as_str()
                    || name == WellKnownSymbol::DotK.as_str()
                {
                    let mut items = Vec::new();
                    if !self.sequence(pattern, &mut items)? {
                        return opaque();
                    }
                    return Ok(Value::Seq(items));
                }
                if !self.known_symbols.contains(name) {
                    return Err(ValueError::Malformed(format!(
                        "the definition declares no symbol {name}"
                    )));
                }
                if let Some(&(collection, _)) = self.collections.get(name) {
                    return self.collection(pattern, collection);
                }
                match self.ctors_by_symbol.get(name) {
                    Some(info) if self.free_constructors.contains(name) => {
                        self.constructor(pattern, info, symbol, arguments)
                    }
                    Some(info)
                        if self.equation_heads.contains(name)
                            && self.equation_head_data.holds(pattern) =>
                    {
                        self.constructor(pattern, info, symbol, arguments)
                    }
                    _ => opaque(),
                }
            }
            _ => opaque(),
        }
    }

    fn domain_value(
        &self,
        pattern: &Pattern,
        sort: &Sort,
        value: &KoreString,
    ) -> Result<Value, ValueError> {
        let Sort::Application { name, arguments } = sort else {
            return Ok(Value::Opaque(pattern.clone()));
        };
        let malformed = |what: &str| Err(ValueError::Malformed(format!("{pattern} is not {what}")));
        let text = || value.as_utf8().map(str::to_owned);
        match self.sort_hooks.get(name).map(String::as_str) {
            Some("INT.Int") => match text().ok().and_then(|text| text.parse::<BigInt>().ok()) {
                Some(value) => Ok(Value::Int(value)),
                None => malformed("an Int"),
            },
            Some("BOOL.Bool") => match text().ok().as_deref() {
                Some("true") => Ok(Value::Bool(true)),
                Some("false") => Ok(Value::Bool(false)),
                _ => malformed("a Bool"),
            },
            Some("STRING.String") => match text() {
                Ok(text) => Ok(Value::String(text)),
                Err(_) => Ok(Value::Opaque(pattern.clone())),
            },
            Some("BYTES.Bytes") => Ok(Value::Bytes(value.as_bytes().to_vec())),
            Some("FLOAT.Float") => {
                let Ok(text) = text() else {
                    return malformed("a Float");
                };
                match canonical_float_text(&text) {
                    Ok(canonical) => Ok(Value::Float(Float(canonical))),
                    Err(refusal) if refusal.names_no_element() => malformed("a Float"),
                    Err(_) => Ok(Value::Opaque(pattern.clone())),
                }
            }
            _ => match (self.sorts_by_kore.get(name), text()) {
                (Some(sort), Ok(text)) if arguments.is_empty() => Ok(Value::Token {
                    sort: sort.clone(),
                    text,
                }),
                _ => Ok(Value::Opaque(pattern.clone())),
            },
        }
    }

    /// Flatten a K sequence into `items`; `false` when a part is neither an item nor a sequence.
    fn sequence(&self, pattern: &Pattern, items: &mut Vec<Value>) -> Result<bool, ValueError> {
        // A sequence is a chain one level per item: the parts still to read, leftmost on top,
        // are kept on a stack of the walk's own.
        let mut pending = vec![pattern];
        while let Some(pattern) = pending.pop() {
            let (Pattern::Application { symbol, arguments }
            | Pattern::AssociativeApplication {
                symbol, arguments, ..
            }) = pattern
            else {
                return Ok(false);
            };
            let name = symbol.name.as_str();
            if name == WellKnownSymbol::DotK.as_str() {
                if !arguments.is_empty() {
                    return Ok(false);
                }
            } else if name == WellKnownSymbol::KSeq.as_str()
                || name == WellKnownSymbol::Append.as_str()
            {
                let [head, tail] = arguments.as_slice() else {
                    return Err(ValueError::Malformed(format!("{pattern}")));
                };
                pending.push(tail);
                if name == WellKnownSymbol::KSeq.as_str() {
                    items.push(self.decode(head)?);
                } else {
                    pending.push(head);
                }
            } else {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn collection(&self, pattern: &Pattern, collection: Collection) -> Result<Value, ValueError> {
        let mut elements = Vec::new();
        if !self.collection_elements(pattern, collection, &mut elements) {
            return Ok(Value::Opaque(pattern.clone()));
        }
        Ok(match collection {
            Collection::List => Value::List(
                elements
                    .iter()
                    .map(|element| self.decode(element[0]))
                    .collect::<Result<_, _>>()?,
            ),
            Collection::Set => {
                let mut items = BTreeSet::new();
                for element in &elements {
                    if !items.insert(self.decode(element[0])?) {
                        return Ok(Value::Opaque(pattern.clone()));
                    }
                }
                Value::Set(items)
            }
            Collection::Map => {
                let mut entries = BTreeMap::new();
                for element in &elements {
                    let [key, value] = element.as_slice() else {
                        return Err(ValueError::Malformed(format!("{pattern}")));
                    };
                    if entries
                        .insert(self.decode(key)?, self.decode(value)?)
                        .is_some()
                    {
                        return Ok(Value::Opaque(pattern.clone()));
                    }
                }
                Value::Map(entries)
            }
        })
    }

    /// The arguments of each element application of a collection term, in order; `false` when
    /// a part is neither an element, a unit, nor a concatenation of the same collection.
    fn collection_elements<'p>(
        &self,
        pattern: &'p Pattern,
        collection: Collection,
        elements: &mut Vec<Vec<&'p Pattern>>,
    ) -> bool {
        // A collection is a chain one level per element: the parts still to read, leftmost on
        // top, are kept on a stack of the walk's own.
        let mut pending = vec![pattern];
        while let Some(pattern) = pending.pop() {
            let (Pattern::Application { symbol, arguments }
            | Pattern::AssociativeApplication {
                symbol, arguments, ..
            }) = pattern
            else {
                return false;
            };
            match self.collections.get(&symbol.name) {
                Some(&(kind, Role::Unit)) if kind == collection => {
                    if !arguments.is_empty() {
                        return false;
                    }
                }
                Some(&(kind, Role::Element)) if kind == collection => {
                    let expected = if collection == Collection::Map { 2 } else { 1 };
                    if arguments.len() != expected {
                        return false;
                    }
                    elements.push(arguments.iter().collect());
                }
                Some(&(kind, Role::Concat)) if kind == collection => {
                    pending.extend(arguments.iter().rev());
                }
                _ => return false,
            }
        }
        true
    }

    fn constructor(
        &self,
        pattern: &Pattern,
        info: &CtorInfo,
        symbol: &Symbol,
        arguments: &[Pattern],
    ) -> Result<Value, ValueError> {
        if arguments.len() != info.fields.len() || symbol.sort_parameters.len() != info.parameters {
            return Err(ValueError::Malformed(format!(
                "{pattern} does not apply `{}` to its {} fields",
                info.decl,
                info.fields.len()
            )));
        }
        let mut sort_args = Vec::with_capacity(info.parameters);
        for sort in &symbol.sort_parameters {
            match sort {
                Sort::Application { name, arguments } if arguments.is_empty() => {
                    match self.sorts_by_kore.get(name) {
                        Some(sort) => sort_args.push(sort.clone()),
                        None => return Ok(Value::Opaque(pattern.clone())),
                    }
                }
                _ => return Ok(Value::Opaque(pattern.clone())),
            }
        }
        let fields = info
            .fields
            .iter()
            .zip(arguments)
            .map(|(field, argument)| Ok((field.clone(), self.decode(argument)?)))
            .collect::<Result<_, ValueError>>()?;
        Ok(Value::Ctor(Ctor {
            decl: info.decl.clone(),
            sort_args,
            fields,
        }))
    }

    /// The KORE pattern of a value, without injections: the term it describes, before typing.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::Unencodable`] or [`ValueError::Fields`] for a value that is no
    /// ground term of this definition.
    pub(crate) fn encode(&self, value: &Value) -> Result<Pattern, ValueError> {
        let builtin = |sort: BuiltinSort, text: KoreString| Pattern::DomainValue {
            sort: kore_sort(&kore_sort_name(sort.k_name())),
            value: text,
        };
        Ok(match value {
            Value::Ctor(ctor) => {
                let info = self.ctors_by_decl.get(&ctor.decl).ok_or_else(|| {
                    ValueError::Unencodable(format!(
                        "no constructor is declared at `{}`",
                        ctor.decl
                    ))
                })?;
                if ctor.fields.len() != info.fields.len()
                    || ctor
                        .fields
                        .iter()
                        .zip(&info.fields)
                        .any(|((name, _), field)| name != field)
                {
                    return Err(ValueError::Fields {
                        decl: ctor.decl.to_string(),
                        expected: info.fields.iter().map(ToString::to_string).collect(),
                        found: ctor
                            .fields
                            .iter()
                            .map(|(name, _)| name.to_string())
                            .collect(),
                    });
                }
                if ctor.sort_args.len() != info.parameters {
                    return Err(ValueError::Unencodable(format!(
                        "`{}` takes {} sort arguments, not {}",
                        ctor.decl,
                        info.parameters,
                        ctor.sort_args.len()
                    )));
                }
                Pattern::Application {
                    symbol: Symbol {
                        name: info.symbol.clone(),
                        sort_parameters: ctor
                            .sort_args
                            .iter()
                            .map(|sort| self.kore_sort(sort))
                            .collect::<Result<_, _>>()?,
                    },
                    arguments: ctor
                        .fields
                        .iter()
                        .map(|(_, value)| self.encode(value))
                        .collect::<Result<_, _>>()?,
                }
            }
            Value::Int(value) => builtin(BuiltinSort::Int, KoreString::from(value.to_string())),
            Value::Bool(value) => builtin(BuiltinSort::Bool, KoreString::from(value.to_string())),
            Value::String(value) => builtin(BuiltinSort::String, KoreString::from(value.as_str())),
            Value::Bytes(value) => {
                builtin(BuiltinSort::Bytes, KoreString::from_bytes(value.clone()))
            }
            Value::Float(value) => builtin(BuiltinSort::Float, KoreString::from(value.literal())),
            Value::Token { sort, text } => Pattern::DomainValue {
                sort: self.kore_sort(sort)?,
                value: KoreString::from(text.as_str()),
            },
            Value::Seq(items) => {
                let mut sequence = application(WellKnownSymbol::DotK.as_str(), Vec::new());
                for item in items.iter().rev() {
                    sequence = application(
                        WellKnownSymbol::KSeq.as_str(),
                        vec![self.encode(item)?, sequence],
                    );
                }
                sequence
            }
            Value::List(items) => self.encode_collection(
                Collection::List,
                items.iter().map(|item| Ok(vec![self.encode(item)?])),
            )?,
            Value::Set(items) => self.encode_collection(
                Collection::Set,
                items.iter().map(|item| Ok(vec![self.encode(item)?])),
            )?,
            Value::Map(entries) => self.encode_collection(
                Collection::Map,
                entries
                    .iter()
                    .map(|(key, value)| Ok(vec![self.encode(key)?, self.encode(value)?])),
            )?,
            Value::Opaque(pattern) => {
                if has_variable(pattern) {
                    return Err(ValueError::Unencodable(format!(
                        "{pattern} has a variable; a configuration is ground"
                    )));
                }
                pattern.clone()
            }
        })
    }

    fn encode_collection(
        &self,
        collection: Collection,
        elements: impl Iterator<Item = Result<Vec<Pattern>, ValueError>>,
    ) -> Result<Pattern, ValueError> {
        let builders = &self.builders[collection_slot(collection)];
        let missing = || {
            ValueError::Unencodable(format!(
                "the definition has no {collection:?} builder symbols"
            ))
        };
        let mut built = None;
        for arguments in elements {
            let element = application(builders.element.as_ref().ok_or_else(missing)?, arguments?);
            built = Some(match built {
                None => element,
                Some(left) => application(
                    builders.concat.as_ref().ok_or_else(missing)?,
                    vec![left, element],
                ),
            });
        }
        match built {
            Some(built) => Ok(built),
            None => Ok(application(
                builders.unit.as_ref().ok_or_else(missing)?,
                Vec::new(),
            )),
        }
    }

    fn kore_sort(&self, sort: &SortRef) -> Result<Sort, ValueError> {
        self.kore_by_sort
            .get(sort)
            .map(|name| kore_sort(name))
            .ok_or_else(|| ValueError::Unencodable(format!("the definition has no sort {sort}")))
    }

    /// The sort of a value's term below its injections, as KRS names it: a builtin's, a token's,
    /// a constructor's or function's result sort; `None` for an opaque pattern and a result
    /// sort no KRS declaration names.
    pub(crate) fn value_sort(&self, value: &Value) -> Option<SortRef> {
        Some(SortRef::Builtin(match value {
            Value::Ctor(ctor) => {
                return self
                    .ctors_by_decl
                    .get(&ctor.decl)?
                    .result
                    .as_ref()
                    .map(|result| result.sort.clone());
            }
            Value::Token { sort, .. } => return Some(sort.clone()),
            Value::Opaque(_) => return None,
            Value::Int(_) => BuiltinSort::Int,
            Value::Bool(_) => BuiltinSort::Bool,
            Value::String(_) => BuiltinSort::String,
            Value::Bytes(_) => BuiltinSort::Bytes,
            Value::Float(_) => BuiltinSort::Float,
            Value::Seq(_) => BuiltinSort::KSequence,
            Value::List(_) => BuiltinSort::List,
            Value::Set(_) => BuiltinSort::Set,
            Value::Map(_) => BuiltinSort::Map,
        }))
    }

    /// What an opaque part is, for a refusal that names it: a variable, an unevaluated function
    /// application (of a KRS function or a builtin hook), a constructor application that is no
    /// value, a constructor no KRS declaration names, a collection with a part that is no
    /// element, or a matching-logic connective.
    pub(crate) fn opaque_part(&self, pattern: &Pattern) -> String {
        match strip_injections(pattern) {
            Pattern::Variable(variable) => format!("the variable `{}`", variable.name),
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => {
                let name = symbol.name.as_str();
                match self.ctors_by_symbol.get(name) {
                    Some(info) if info.function => format!(
                        "an unevaluated application of the function `{}`",
                        info.decl
                    ),
                    Some(info) => format!(
                        "an application of `{}` that is no value of the constructor (an equation still reduces it, or a sort argument has no KRS name)",
                        info.decl
                    ),
                    None if self.collections.contains_key(name)
                        || name == WellKnownSymbol::KSeq.as_str()
                        || name == WellKnownSymbol::Append.as_str() =>
                    {
                        "a collection with a part that is neither an element nor a unit (a variable or an unevaluated application)".to_owned()
                    }
                    None => match self.hooked_functions.get(name) {
                        Some(hook) => format!(
                            "an unevaluated application of the builtin function `{hook}`"
                        ),
                        None => format!(
                            "the application of `{name}`, a constructor no KRS declaration names (a strictness freezer, or one K generates)"
                        ),
                    },
                }
            }
            Pattern::DomainValue { sort, value } => format!(
                "the domain value {:?} of `{sort}`, which no KRS value describes",
                value.as_utf8().unwrap_or("<bytes>")
            ),
            Pattern::String(_) => "a string literal of the pattern language".to_owned(),
            Pattern::Top { .. } => "the connective `\\top`".to_owned(),
            Pattern::Bottom { .. } => "the connective `\\bottom`".to_owned(),
            Pattern::And { .. } => "the connective `\\and`".to_owned(),
            Pattern::Or { .. } => "the connective `\\or`".to_owned(),
            Pattern::Not { .. } => "the connective `\\not`".to_owned(),
            Pattern::Exists { .. } => "the quantifier `\\exists`".to_owned(),
            Pattern::Forall { .. } => "the quantifier `\\forall`".to_owned(),
            Pattern::Equals { .. } => "the predicate `\\equals`".to_owned(),
            Pattern::Ceil { .. } => "the predicate `\\ceil`".to_owned(),
            _ => "a matching-logic connective".to_owned(),
        }
    }

    /// The KAST term of a value, as the configuration assembler takes a value bound without
    /// the parser.
    pub(crate) fn to_kast(&self, value: &Value) -> Result<KastTerm, ValueError> {
        let pattern = self.encode(value)?;
        Converter::new(&self.kast_sort_hooks)
            .convert(&pattern)
            .map_err(|error| ValueError::Unencodable(error.to_string()))
    }
}

/// `pattern` below its injections: `inj{A, B}(a)` is `a` viewed in `B`.
pub(crate) fn strip_injections(mut pattern: &Pattern) -> &Pattern {
    while let Pattern::Application { symbol, arguments } = pattern
        && symbol.name == WellKnownSymbol::Inj.as_str()
        && let [argument] = arguments.as_slice()
    {
        pattern = argument;
    }
    pattern
}

fn kore_sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn application(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

pub(crate) fn resolve<'d>(
    kind: &'static str,
    name: &str,
    decls: impl Iterator<Item = &'d Decl>,
) -> Result<Decl, ValueError> {
    let decls = decls.collect::<Vec<_>>();
    let mut matches = decls
        .iter()
        .filter(|decl| decl.is_named(name))
        .map(|decl| (*decl).clone())
        .collect::<Vec<_>>();
    matches.sort();
    match matches.len() {
        1 => Ok(matches.remove(0)),
        0 => {
            let last = name.rsplit("::").next().unwrap_or(name);
            let mut candidates = decls
                .iter()
                .filter(|decl| decl.path().rsplit("::").next() == Some(last))
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            candidates.sort();
            Err(ValueError::UnknownName {
                kind,
                name: name.to_owned(),
                candidates,
            })
        }
        _ => Err(ValueError::AmbiguousName {
            name: name.to_owned(),
            candidates: matches.iter().map(ToString::to_string).collect(),
        }),
    }
}

fn cell_nodes(
    cells: &[krs_ir::FixedCell<krs_ir_levels::DefinitionSortRef, krs_ir_levels::SymbolId>],
) -> Vec<CellNode> {
    cells
        .iter()
        .map(|cell| CellNode {
            field: cell.field().unwrap_or(cell.name()).to_owned(),
            symbol: kore_symbol_name(&format!("<{}>", cell.name())),
            multiplicity: cell.multiplicity(),
            collection: cell.collection_type(),
            unobservable: cell.is_unobservable(),
            children: match cell.content() {
                krs_ir::FixedCellContent::Children { children } => cell_nodes(children),
                krs_ir::FixedCellContent::Term { .. } => Vec::new(),
            },
            content: match cell.content() {
                krs_ir::FixedCellContent::Term { sort, arguments } => {
                    Some((sort.clone(), arguments.clone()))
                }
                krs_ir::FixedCellContent::Children { .. } => None,
            },
        })
        .collect()
}

/// The index of the KORE definition `text` (main module `MAIN`), whose KRS declarations are the
/// constructors `ctors` (symbol, `t::S::` name, fields), and no sort or cell.
#[cfg(test)]
pub(crate) fn index_of(text: &str, ctors: &[(&str, &str, &[&str])]) -> ValueIndex {
    index_at(text, ctors, None)
}

/// [`index_of`], with the declared sort `t::T` a token sort that is the result sort of every
/// constructor in `ctors`: the index of a definition KRS refuses (a token sort has no
/// constructors), for the checks that what the encoder writes stays one the decoder reads where
/// a token's text has a second reading at its own sort.
#[cfg(test)]
pub(crate) fn token_sort_index(
    text: &str,
    ctors: &[(&str, &str, &[&str])],
) -> (ValueIndex, SortRef) {
    let sort = SortRef::Declared(Decl("t::T".into()));
    let mut index = index_at(text, ctors, Some(&sort));
    index.token_sorts.insert(sort.clone());
    (index, sort)
}

/// [`index_of`], where the constructors' result sort is `t::T` (KORE `SortT`) and `Map` (KORE
/// `SortMap`) is at most it, by the definition's subsort axioms.
#[cfg(test)]
pub(crate) fn map_sort_index(text: &str, ctors: &[(&str, &str, &[&str])]) -> (ValueIndex, SortRef) {
    let sort = SortRef::Declared(Decl("t::T".into()));
    let mut index = index_at(text, ctors, Some(&sort));
    index.kore_by_sort.insert(sort.clone(), "SortT".to_owned());
    index.kore_by_sort.insert(
        SortRef::Builtin(krs_ir::BuiltinSort::Map),
        "SortMap".to_owned(),
    );
    (index, sort)
}

/// The index of `text` with the KRS declarations `ctors`, each `(symbol, name, fields)` declared
/// at `t::S::<name>` with the result sort `result`.
#[cfg(test)]
fn index_at(text: &str, ctors: &[(&str, &str, &[&str])], result: Option<&SortRef>) -> ValueIndex {
    use k_rust::backend::{Backend, BackendOptions};

    let mut backend = Backend::new(text, "MAIN", BackendOptions::default()).unwrap();
    let definition = backend.select_definition(None).unwrap();
    let symbols = BackendSymbols::scan(&definition);
    let sort_graph = definition.sort_graph().clone();
    let mut ctors_by_symbol = HashMap::new();
    let mut ctors_by_decl = HashMap::new();
    for (symbol, name, fields) in ctors {
        let info = Arc::new(CtorInfo {
            decl: Decl(format!("t::S::{name}").into()),
            symbol: (*symbol).to_owned(),
            fields: fields.iter().map(|field| Arc::from(*field)).collect(),
            field_types: vec![None; fields.len()],
            result: result.cloned().map(InputType::of),
            function: false,
            parameters: 0,
        });
        ctors_by_symbol.insert((*symbol).to_owned(), info.clone());
        ctors_by_decl.insert(info.decl.clone(), info);
    }
    ValueIndex {
        ctors_by_symbol,
        ctors_by_decl,
        sorts_by_kore: HashMap::new(),
        kore_by_sort: HashMap::new(),
        sorts_by_symbol: HashMap::new(),
        token_sorts: BTreeSet::new(),
        sort_graph,
        sort_hooks: HashMap::new(),
        kast_sort_hooks: HashMap::new(),
        known_symbols: symbols.known,
        free_constructors: symbols.free_constructors,
        equational_partial: symbols.equational_partial,
        hooked_functions: symbols.hooked_functions,
        collection_builders: symbols.collection_builders,
        equation_heads: symbols.equation_heads,
        overloads: crate::overloads::Overloads::new(definition.axioms()),
        equation_head_data: EquationHeadData::new(definition),
        result_sorts: symbols.result_sorts,
        collections: symbols.collections,
        builders: symbols.builders,
        cells: Vec::new(),
        top: String::new(),
    }
}

#[cfg(test)]
mod tests {
    use k_rust::kore::ast::{Pattern, Symbol};
    use k_rust::kore::parser::parse_pattern;

    use super::{Decl, Float, Value, ValueIndex, WellKnownSymbol, index_of};

    /// `c` is a constructor an `anywhere` rule rewrites, `c(a) => c(b)`: `c(b)`, which no
    /// equation reduces, is a value of `c`; `c(a)`, which the rule still reduces, is none.
    const ANYWHERE: &str = r"[]
        module MAIN
            sort SortS{} []
            symbol a{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
            symbol b{}() : SortS{} [constructor{}(), functional{}(), injective{}()]
            symbol c{}(SortS{}) : SortS{} [anywhere{}(), function{}(), value-production{}()]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, a{}()), \top{R}())),
                \equals{SortS{}, R}(c{}(X0:SortS{}), \and{SortS{}}(c{}(b{}()), \top{SortS{}}()))
            ) [anywhere{}()]
        endmodule []";

    /// The index of [`ANYWHERE`], whose KRS declarations are `t::S::A`, `t::S::B` and `t::S::C`.
    fn anywhere_index() -> ValueIndex {
        index_of(
            ANYWHERE,
            &[("a", "A", &[][..]), ("b", "B", &[]), ("c", "C", &["x"])],
        )
    }

    #[test]
    fn an_anywhere_constructors_application_is_a_value_only_where_no_equation_reduces_it() {
        let index = anywhere_index();
        let decode = |text: &str| index.decode(&parse_pattern(text).unwrap()).unwrap();
        assert!(
            matches!(decode("c{}(b{}())"), Value::Ctor(_)),
            "{:?}",
            decode("c{}(b{}())")
        );
        assert!(
            matches!(decode("c{}(a{}())"), Value::Opaque(_)),
            "{:?}",
            decode("c{}(a{}())")
        );
        assert!(matches!(decode("a{}()"), Value::Ctor(_)));
    }

    /// A K sequence of a million items, a chain one level per item, flattens on an 8 MiB thread,
    /// a main thread's default on Linux, in order, whether `kseq` nests it to the right or
    /// `append` nests it to the left.
    #[test]
    fn a_million_item_sequence_decodes_on_an_8_mib_thread() {
        std::thread::Builder::new()
            .stack_size(8 << 20)
            .spawn(|| {
                const ITEMS: usize = 1_000_000;
                let index = anywhere_index();
                let items = [
                    parse_pattern("inj{SortS{}, SortKItem{}}(a{}())").unwrap(),
                    parse_pattern("inj{SortS{}, SortKItem{}}(b{}())").unwrap(),
                ];
                let decoded = items.each_ref().map(|item| index.decode(item).unwrap());
                let dotk = || Pattern::Application {
                    symbol: Symbol {
                        name: WellKnownSymbol::DotK.as_str().to_owned(),
                        sort_parameters: Vec::new(),
                    },
                    arguments: Vec::new(),
                };
                let pair =
                    |name: WellKnownSymbol, head: Pattern, tail: Pattern| Pattern::Application {
                        symbol: Symbol {
                            name: name.as_str().to_owned(),
                            sort_parameters: Vec::new(),
                        },
                        arguments: vec![head, tail],
                    };
                let mut right = dotk();
                for item in (0..ITEMS).rev() {
                    right = pair(WellKnownSymbol::KSeq, items[item % 2].clone(), right);
                }
                let mut left = dotk();
                for item in 0..ITEMS {
                    let single = pair(WellKnownSymbol::KSeq, items[item % 2].clone(), dotk());
                    left = pair(WellKnownSymbol::Append, left, single);
                }
                for sequence in [right, left] {
                    let Value::Seq(read) = index.decode(&sequence).unwrap() else {
                        panic!("a sequence of items decodes to its items");
                    };
                    assert_eq!(read.len(), ITEMS);
                    for (position, item) in read.iter().enumerate() {
                        assert_eq!(item, &decoded[position % 2], "item {position}");
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn a_float_is_its_value_not_its_spelling() {
        let one_and_a_half = Float::parse("1.5").unwrap();
        for spelling in ["1.5d", "0.15e1", "1.5p53x11", "1.50000000000000000"] {
            assert_eq!(
                Float::parse(spelling).unwrap(),
                one_and_a_half,
                "{spelling}"
            );
        }
        assert_eq!(Float::from_f64(1.5), one_and_a_half);
        assert_eq!(one_and_a_half.to_f64(), Some(1.5));
        assert_eq!(one_and_a_half.to_f32(), None);
        // The format and the sign of zero are part of the value.
        assert_ne!(Float::parse("1.5f").unwrap(), one_and_a_half);
        assert_eq!(Float::from_f32(1.5).to_f32(), Some(1.5));
        assert_ne!(Float::from_f64(0.0), Float::from_f64(-0.0));
        for special in [
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MIN_POSITIVE / 4.0,
        ] {
            let float = Float::from_f64(special);
            let back = float.to_f64().unwrap();
            assert!(back.to_bits() == special.to_bits() || (back.is_nan() && special.is_nan()));
        }
        assert!(Float::parse("one").is_err());
    }

    #[test]
    fn a_name_is_a_path_or_a_suffix_of_whole_segments() {
        let decl = Decl("sm83::machine::Register::A".into());
        for name in [
            "A",
            "Register::A",
            "machine::Register::A",
            "sm83::machine::Register::A",
        ] {
            assert!(decl.is_named(name), "{name}");
        }
        for name in ["r::A", "ster::A", "Register", "B"] {
            assert!(!decl.is_named(name), "{name}");
        }
    }
}
