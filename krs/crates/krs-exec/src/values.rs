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
//! constructor, and builtins have one canonical form each, so two ground values are equal exactly
//! when the terms they describe are.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use k_rust::{
    k_rust_backend::{
        builtin::canonical_float_text, definition::BackendDefinition, term::HeadRole,
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
use krs_ir_levels::{DefinitionIr, DefinitionSentence, SymbolIdentity};
use num_bigint::BigInt;

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

/// A K literal of an IEEE value whose Rust exponent form is `exponent_form`.
fn ieee_literal(
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

/// A constructor production of the definition.
#[derive(Debug)]
struct CtorInfo {
    decl: Decl,
    /// The KORE symbol name.
    symbol: String,
    fields: Vec<Arc<str>>,
    parameters: usize,
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
    pub(crate) children: Vec<CellNode>,
}

/// The backend's symbol table as decoding and encoding read it.
struct BackendSymbols {
    known: HashSet<String>,
    free_constructors: HashSet<String>,
    collections: HashMap<String, (Collection, Role)>,
    builders: [CollectionSymbols; 3],
}

impl BackendSymbols {
    fn scan(backend: &BackendDefinition) -> Self {
        let mut known = HashSet::new();
        let mut free_constructors = HashSet::new();
        let mut collections = HashMap::new();
        let mut builders: [CollectionSymbols; 3] = Default::default();
        for (name, symbol) in backend.symbols() {
            let name = name.to_string();
            known.insert(name.clone());
            if symbol.attributes.head_role() == HeadRole::FreeConstructor {
                free_constructors.insert(name.clone());
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
            let result = match &symbol.result_sort {
                k_rust::k_rust_backend::term::Sort::Application { name, .. } => name.to_string(),
                k_rust::k_rust_backend::term::Sort::Variable(_) => continue,
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
        Self {
            known,
            free_constructors,
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
    ctors_by_decl: HashMap<Decl, Arc<CtorInfo>>,
    sorts_by_kore: HashMap<String, SortRef>,
    kore_by_sort: HashMap<SortRef, String>,
    /// Hooks of the backend's sorts, by KORE name.
    sort_hooks: HashMap<String, String>,
    /// Hooks of the backend's sorts, by KAST name, for the KAST conversion of an encoded value.
    kast_sort_hooks: HashMap<String, String>,
    known_symbols: HashSet<String>,
    free_constructors: HashSet<String>,
    collections: HashMap<String, (Collection, Role)>,
    builders: [CollectionSymbols; 3],
    cells: Vec<CellNode>,
    top: String,
}

const fn collection_slot(collection: Collection) -> usize {
    match collection {
        Collection::List => 0,
        Collection::Set => 1,
        Collection::Map => 2,
    }
}

fn kore_sort_name(k_name: &str) -> String {
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

impl ValueIndex {
    /// Index the KRS declarations of `definition` against the backend's view of its compiled KORE.
    pub(crate) fn new(
        definition: &DefinitionIr,
        backend: &BackendDefinition,
        kast_sort_hooks: &HashMap<String, String>,
    ) -> Self {
        let mut ctors_by_symbol = HashMap::new();
        let mut ctors_by_decl = HashMap::new();
        let mut sorts_by_kore = HashMap::new();
        let mut cells = Vec::new();
        for sort in BuiltinSort::ALL {
            sorts_by_kore.insert(kore_sort_name(sort.k_name()), SortRef::Builtin(sort));
        }
        for module in definition.modules() {
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::SyntaxSort(sort) => {
                        if let Some(decl) = decl_of(sort.symbol()) {
                            sorts_by_kore.insert(
                                kore_sort_name(sort.symbol().emitted_name()),
                                SortRef::Declared(decl),
                            );
                        }
                    }
                    DefinitionSentence::Production(production) => {
                        let Some(decl) = decl_of(production.symbol()) else {
                            continue;
                        };
                        let fields = production
                            .items()
                            .iter()
                            .filter_map(|item| match item.kind() {
                                krs_ir::GrammarProductionItemKind::NonTerminal {
                                    field, ..
                                } => Some(Arc::from(field.as_str())),
                                _ => None,
                            })
                            .collect();
                        let info = Arc::new(CtorInfo {
                            decl: decl.clone(),
                            symbol: kore_symbol_name(production.symbol().emitted_name()),
                            fields,
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
            ctors_by_symbol,
            ctors_by_decl,
            sorts_by_kore,
            kore_by_sort,
            sort_hooks,
            kast_sort_hooks: kast_sort_hooks.clone(),
            known_symbols: symbols.known,
            free_constructors: symbols.free_constructors,
            collections: symbols.collections,
            builders: symbols.builders,
            cells,
            top: kore_symbol_name(k_rust::kast::GeneratedCell::Top.label()),
        }
    }

    /// The constructor named by `name`: its full path or a `::`-aligned suffix of it
    /// (`Register::A`).
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::UnknownName`] or [`ValueError::AmbiguousName`].
    pub fn decl(&self, name: &str) -> Result<Decl, ValueError> {
        resolve("constructor", name, self.ctors_by_decl.keys())
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
    /// # Errors
    ///
    /// Returns a name error, [`ValueError::Fields`] when the names are not exactly the
    /// declared fields, or [`ValueError::Unencodable`] for a parametric production, whose
    /// sort arguments this builder does not take.
    pub fn ctor<'a>(
        &self,
        name: &str,
        fields: impl IntoIterator<Item = (&'a str, Value)>,
    ) -> Result<Value, ValueError> {
        let decl = self.decl(name)?;
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
        if let Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } = pattern
        {
            let name = symbol.name.as_str();
            if name == WellKnownSymbol::DotK.as_str() {
                return Ok(arguments.is_empty());
            }
            if name == WellKnownSymbol::KSeq.as_str() || name == WellKnownSymbol::Append.as_str() {
                let [head, tail] = arguments.as_slice() else {
                    return Err(ValueError::Malformed(format!("{pattern}")));
                };
                if name == WellKnownSymbol::KSeq.as_str() {
                    items.push(self.decode(head)?);
                    return self.sequence(tail, items);
                }
                return Ok(self.sequence(head, items)? && self.sequence(tail, items)?);
            }
        }
        Ok(false)
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
        let (Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        }) = pattern
        else {
            return false;
        };
        match self.collections.get(&symbol.name) {
            Some(&(kind, Role::Unit)) if kind == collection => arguments.is_empty(),
            Some(&(kind, Role::Element)) if kind == collection => {
                let expected = if collection == Collection::Map { 2 } else { 1 };
                if arguments.len() != expected {
                    return false;
                }
                elements.push(arguments.iter().collect());
                true
            }
            Some(&(kind, Role::Concat)) if kind == collection => arguments
                .iter()
                .all(|argument| self.collection_elements(argument, collection, elements)),
            _ => false,
        }
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

    /// The KAST term of a value, as the configuration assembler takes a value bound without
    /// the parser.
    pub(crate) fn to_kast(&self, value: &Value) -> Result<KastTerm, ValueError> {
        let pattern = self.encode(value)?;
        Converter::new(&self.kast_sort_hooks)
            .convert(&pattern)
            .map_err(|error| ValueError::Unencodable(error.to_string()))
    }
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

fn resolve<'d>(
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
            children: match cell.content() {
                krs_ir::FixedCellContent::Children { children } => cell_nodes(children),
                krs_ir::FixedCellContent::Term { .. } => Vec::new(),
            },
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{Decl, Float};

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
