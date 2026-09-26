//! Immutable backend terms with cached synthetic attributes (`variables`, `evaluated`,
//! `constructor_like`): the layer-1 representation every algorithm shares; a responsibility, not
//! an algorithm; `Counter::TermConstructed` per construction; no worklist.
//!
//! The invariants every `Term` satisfies, which the Lean term model (`lean/KRust/TermAttributes.lean`,
//! `WF` and `TotalOrder`) assumes and `tests/backend/term_order.rs` checks:
//!
//! ```toml algorithm-representation
//! id = "representation.backend.term"
//! name = "immutable backend term with a cached structural hash"
//! type = "k_rust_backend::term::Term"
//! sites = ["Term", "TermData", "Term::new", "Term::map", "Term::set", "Term::with_evaluated_cache", "calculate_hash", "ceil_free", "key_header", "share_one_key_header", "fold_children", "k_cells", "Term::eq", "Term::cmp"]
//! invariant = "Term::new is the only place a TermData is built, and a TermData is never mutated after it is shared: Term and TermData keep their fields private. Term::new sets the stored hash to calculate_hash of the kind, so Eq for Term (pointer equality, or equal hash and equal kind) is structural equality of the kind, and Ord for Term is the derived order on the kind. Term::new also sets the stored ceil_free attribute to ceil_free of the kind, which reads only the kind and the children's stored ceil_free, so the stored value of every Term is ceilFree of the Lean model applied to it; likewise has_macro_or_alias and k_cells, from the children's stored values, are hasMacro and kCells of the Lean model. Only Term::map builds a Map kind: after merging the entries of a same-definition rest, it sorts the entries by (key, value) and removes adjacent equal pairs. Only Term::set builds a Set kind: after merging the elements of a same-definition rest, it sorts the elements and removes adjacent equal ones. with_evaluated_cache rebuilds a term from a copy of its kind and changes only the evaluated attribute. Hence every map and set, at every depth of every Term, is sorted with adjacent entries or elements distinct."
//! tests = ["crates/k-rust-backend/tests/backend/term_order.rs"]
//! lean = ["KRust.TermAttributes.ceilFree_sound", "KRust.TermAttributes.map_keys_pairwise_distinct", "KRust.TermAttributes.set_pairwise_distinct"]
//! ```
//!
//! Execution, search and proof check every configuration they reach for a macro or alias symbol
//! that preprocessing should have removed. The stored `has_macro_or_alias` attribute answers "is
//! there one" in O(1), and the preorder walk that names the first one runs only when there is:
//!
//! ```toml algorithm
//! id = "backend.term.macro_or_alias"
//! name = "search for a macro or alias symbol that survived into an executable term"
//! sites = ["Term::macro_or_alias_symbol", "Term::first_macro_or_alias_symbol", "Term::visit_symbols", "has_macro_or_alias"]
//! variable = "t = term nodes"
//! counters = []
//! no_counter = "the search has no dedicated counter; its callers run it once per configuration they reach"
//! span = "none"
//! lean = ["KRust.TermAttributes.hasMacro_iff", "KRust.TermAttributes.macro_shortcut_eq"]
//!
//! [[cost]]
//! mode = "no surviving symbol (stored has_macro_or_alias false)"
//! bound = "O(1)"
//!
//! [[cost]]
//! mode = "a surviving symbol"
//! bound = "O(t)"
//! ```

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
    sync::{Arc, OnceLock},
};

use k_rust_kore::kore::ast::KoreString;
use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use num_bigint::BigInt;

use crate::smt::SmtType;

pub mod names;

pub type Name = Arc<str>;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Sort {
    Application { name: Name, arguments: Vec<Sort> },
    Variable(Name),
}

impl PartialOrd for Sort {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Sort {
    /// The order of the variants, then of the names, then of the arguments; two handles of
    /// one name allocation are equal names without reading them.
    fn cmp(&self, other: &Self) -> Ordering {
        let names = |left: &Name, right: &Name| {
            if Arc::ptr_eq(left, right) {
                Ordering::Equal
            } else {
                left.cmp(right)
            }
        };
        match (self, other) {
            (
                Self::Application { name, arguments },
                Self::Application {
                    name: other_name,
                    arguments: other_arguments,
                },
            ) => names(name, other_name).then_with(|| arguments.cmp(other_arguments)),
            (Self::Variable(name), Self::Variable(other_name)) => names(name, other_name),
            (Self::Application { .. }, Self::Variable(_)) => Ordering::Less,
            (Self::Variable(_), Self::Application { .. }) => Ordering::Greater,
        }
    }
}

impl Sort {
    pub fn application(name: impl Into<Name>, arguments: Vec<Self>) -> Self {
        Self::Application {
            name: name.into(),
            arguments,
        }
    }

    pub fn simple(name: impl Into<Name>) -> Self {
        Self::application(name, Vec::new())
    }

    /// A builtin sort, sharing one `Name` allocation per variant for the life of the process.
    pub fn builtin(sort: BuiltinSort) -> Self {
        Self::Application {
            name: builtin_name(sort),
            arguments: Vec::new(),
        }
    }

    /// True for the nullary application of the builtin's KORE name.
    pub fn is_builtin(&self, sort: BuiltinSort) -> bool {
        matches!(
            self,
            Self::Application { name, arguments }
                if arguments.is_empty() && name.as_ref() == sort.kore_name()
        )
    }
}

/// One `Name` per `BuiltinSort` variant, created on first use and indexed by the variant's
/// position in `BuiltinSort::ALL`.
fn builtin_name(sort: BuiltinSort) -> Name {
    static NAMES: OnceLock<Vec<Name>> = OnceLock::new();
    let names = NAMES.get_or_init(|| {
        BuiltinSort::ALL
            .iter()
            .map(|sort| Name::from(sort.kore_name()))
            .collect()
    });
    let index = BuiltinSort::ALL
        .iter()
        .position(|candidate| *candidate == sort)
        .expect("every builtin sort is listed in BuiltinSort::ALL");
    names[index].clone()
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum VariableKind {
    Element,
    Set,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable {
    pub kind: VariableKind,
    pub sort: Sort,
    pub name: Name,
}

impl Variable {
    pub fn new(name: impl Into<Name>, sort: Sort) -> Self {
        Self {
            kind: VariableKind::Element,
            sort,
            name: name.into(),
        }
    }

    pub fn set(name: impl Into<Name>, sort: Sort) -> Self {
        Self {
            kind: VariableKind::Set,
            sort,
            name: name.into(),
        }
    }

    pub fn with_name(&self, name: impl Into<Name>) -> Self {
        Self {
            kind: self.kind,
            sort: self.sort.clone(),
            name: name.into(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FunctionType {
    Partial,
    Total,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SymbolType {
    Constructor,
    Function(FunctionType),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SymbolAttributes {
    pub symbol_type: SymbolType,
    /// The source symbol carries the KORE `anywhere` attribute.
    pub anywhere: bool,
    /// The source symbol carries the KORE `function` attribute, as distinct from a symbol that is
    /// total only because it is `functional`.
    pub declared_function: bool,
    pub binder: bool,
    pub injective: bool,
    pub associative: bool,
    pub idempotent: bool,
    pub macro_or_alias: bool,
    pub has_evaluators: bool,
    pub smt: Option<SmtType>,
    pub hook: Option<Name>,
    pub collection: Option<CollectionMetadata>,
}

impl SymbolAttributes {
    pub fn constructor() -> Self {
        Self {
            symbol_type: SymbolType::Constructor,
            anywhere: false,
            declared_function: false,
            binder: false,
            injective: false,
            associative: false,
            idempotent: false,
            macro_or_alias: false,
            has_evaluators: true,
            smt: None,
            hook: None,
            collection: None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol {
    pub name: Name,
    pub sort_variables: Vec<Name>,
    pub argument_sorts: Vec<Sort>,
    pub result_sort: Sort,
    pub attributes: SymbolAttributes,
}

impl Symbol {
    /// True when the symbol's name is the well-known symbol's spelling.
    pub fn is(&self, symbol: WellKnownSymbol) -> bool {
        self.name.as_ref() == symbol.as_str()
    }

    pub fn constructor(
        name: impl Into<Name>,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
    ) -> Self {
        Self {
            name: name.into(),
            sort_variables: Vec::new(),
            argument_sorts,
            result_sort,
            attributes: SymbolAttributes::constructor(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CollectionSymbols {
    pub unit: Name,
    pub element: Name,
    pub concat: Name,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MapDefinition {
    pub symbols: CollectionSymbols,
    pub key_sort: Name,
    pub value_sort: Name,
    pub map_sort: Name,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ListDefinition {
    pub symbols: CollectionSymbols,
    pub element_sort: Name,
    pub list_sort: Name,
}

pub type SetDefinition = ListDefinition;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CollectionMetadata {
    Map(Arc<MapDefinition>),
    List(Arc<ListDefinition>),
    Set(Arc<SetDefinition>),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermKind {
    And(Term, Term),
    Application {
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Term>,
    },
    DomainValue {
        sort: Sort,
        value: KoreString,
    },
    Variable(Variable),
    Injection {
        source: Sort,
        target: Sort,
        term: Term,
    },
    Map {
        definition: Arc<MapDefinition>,
        entries: Vec<(Term, Term)>,
        rest: Option<Term>,
    },
    List {
        definition: Arc<ListDefinition>,
        heads: Vec<Term>,
        rest: Option<(Term, Vec<Term>)>,
    },
    Set {
        definition: Arc<SetDefinition>,
        elements: Vec<Term>,
        rest: Option<Term>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermAttributes {
    pub variables: BTreeSet<Variable>,
    pub evaluated: bool,
    pub constructor_like: bool,
    pub concrete_after_normalization: bool,
    pub can_be_evaluated: bool,
    /// See [`TermAttributes::ceil_free`]; set only by `Term::new`, from the kind.
    ceil_free: bool,
    /// See [`TermAttributes::has_macro_or_alias`]; set only by `Term::new`, from the kind.
    has_macro_or_alias: bool,
    /// See [`TermAttributes::k_cells`]; set only by `Term::new`, from the kind.
    k_cells: u8,
    hash: u64,
}

impl Default for TermAttributes {
    fn default() -> Self {
        Self {
            variables: BTreeSet::new(),
            evaluated: true,
            constructor_like: false,
            concrete_after_normalization: false,
            can_be_evaluated: true,
            ceil_free: false,
            has_macro_or_alias: false,
            k_cells: 0,
            hash: 0,
        }
    }
}

impl TermAttributes {
    /// Whether `definedness::ceil_term` of this term is empty for every definition, by
    /// construction: see `ceil_free`, which `Term::new` stores here.
    pub fn ceil_free(&self) -> bool {
        self.ceil_free
    }

    /// Whether some application in this term has a symbol with `macro_or_alias`: exactly when
    /// `Term::first_macro_or_alias_symbol` finds one. See `has_macro_or_alias`, which `Term::new`
    /// stores here.
    pub fn has_macro_or_alias(&self) -> bool {
        self.has_macro_or_alias
    }

    /// The number of `<k>` cells of this term that are not nested in a `<k>` cell, saturated at
    /// 2. See `k_cells`, which `Term::new` stores here.
    pub fn k_cells(&self) -> u8 {
        self.k_cells
    }
}

#[derive(Debug)]
struct TermData {
    attributes: TermAttributes,
    kind: TermKind,
}

#[derive(Clone, Debug)]
pub struct Term(Arc<TermData>);

impl Term {
    pub fn and(left: Self, right: Self) -> Self {
        let mut attributes = combine_attributes([&left, &right]);
        attributes.constructor_like = false;
        attributes.concrete_after_normalization = false;
        Self::new(TermKind::And(left, right), attributes)
    }

    pub fn application(
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Self>,
    ) -> Self {
        if symbol.is(WellKnownSymbol::Inj)
            && let ([source, target], [argument]) =
                (sort_arguments.as_slice(), arguments.as_slice())
        {
            return Self::injection(source.clone(), target.clone(), argument.clone());
        }

        if let Some(collection) = &symbol.attributes.collection {
            return Self::collection_application(
                symbol.clone(),
                sort_arguments,
                arguments,
                collection.clone(),
            );
        }

        Self::application_raw(symbol, sort_arguments, arguments)
    }

    fn application_raw(
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Self>,
    ) -> Self {
        let mut attributes = combine_attributes(arguments.iter());
        let constructor = symbol.attributes.symbol_type == SymbolType::Constructor;
        attributes.evaluated = constructor && attributes.evaluated;
        attributes.constructor_like = constructor && attributes.constructor_like;
        attributes.concrete_after_normalization = (constructor
            || (symbol.attributes.anywhere && !symbol.attributes.declared_function))
            && attributes.concrete_after_normalization;
        attributes.can_be_evaluated =
            symbol.attributes.has_evaluators && attributes.can_be_evaluated;
        Self::new(
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            },
            attributes,
        )
    }

    fn collection_application(
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Self>,
        collection: CollectionMetadata,
    ) -> Self {
        match collection {
            CollectionMetadata::Map(definition) => {
                if symbol.name == definition.symbols.unit && arguments.is_empty() {
                    return Self::map(definition, Vec::new(), None);
                }
                if symbol.name == definition.symbols.element
                    && let [key, value] = arguments.as_slice()
                {
                    return Self::map(definition, vec![(key.clone(), value.clone())], None);
                }
                if symbol.name == definition.symbols.concat
                    && let [left, right] = arguments.as_slice()
                {
                    let (mut entries, left_rest) = map_parts(&definition, left);
                    let (right_entries, right_rest) = map_parts(&definition, right);
                    entries.extend(right_entries);
                    let rest = match (left_rest, right_rest) {
                        (None, rest) | (rest, None) => rest,
                        (Some(left), Some(right)) => Some(Self::application_raw(
                            symbol,
                            sort_arguments,
                            vec![left, right],
                        )),
                    };
                    return Self::map(definition, entries, rest);
                }
            }
            CollectionMetadata::List(definition) => {
                if symbol.name == definition.symbols.unit && arguments.is_empty() {
                    return Self::list(definition, Vec::new(), None);
                }
                if symbol.name == definition.symbols.element
                    && let [element] = arguments.as_slice()
                {
                    return Self::list(definition, vec![element.clone()], None);
                }
                if symbol.name == definition.symbols.concat
                    && let [left, right] = arguments.as_slice()
                {
                    return combine_lists(
                        definition,
                        symbol,
                        sort_arguments,
                        left.clone(),
                        right.clone(),
                    );
                }
            }
            CollectionMetadata::Set(definition) => {
                if symbol.name == definition.symbols.unit && arguments.is_empty() {
                    return Self::set(definition, Vec::new(), None);
                }
                if symbol.name == definition.symbols.element
                    && let [element] = arguments.as_slice()
                {
                    return Self::set(definition, vec![element.clone()], None);
                }
                if symbol.name == definition.symbols.concat
                    && let [left, right] = arguments.as_slice()
                {
                    return combine_sets(
                        definition,
                        symbol,
                        sort_arguments,
                        left.clone(),
                        right.clone(),
                    );
                }
            }
        }
        Self::application_raw(symbol, sort_arguments, arguments)
    }

    pub fn domain_value(sort: Sort, value: impl Into<KoreString>) -> Self {
        let value = value.into();
        let value = if is_int_sort(&sort) {
            canonical_int_text(value)
        } else {
            value
        };
        let attributes = TermAttributes {
            constructor_like: true,
            concrete_after_normalization: true,
            ..TermAttributes::default()
        };
        Self::new(TermKind::DomainValue { sort, value }, attributes)
    }

    pub fn variable(variable: Variable) -> Self {
        let attributes = TermAttributes {
            variables: BTreeSet::from([variable.clone()]),
            ..TermAttributes::default()
        };
        Self::new(TermKind::Variable(variable), attributes)
    }

    pub fn injection(source: Sort, target: Sort, term: Self) -> Self {
        if let TermKind::Injection {
            source: inner_source,
            target: inner_target,
            term: inner,
        } = term.kind()
            && &source == inner_target
        {
            return Self::injection(inner_source.clone(), target, inner.clone());
        }
        Self::new(
            TermKind::Injection {
                source,
                target,
                term: term.clone(),
            },
            term.attributes().clone(),
        )
    }

    pub fn map(
        definition: Arc<MapDefinition>,
        mut entries: Vec<(Self, Self)>,
        rest: Option<Self>,
    ) -> Self {
        let (nested_entries, rest) = match rest {
            Some(rest) => match rest.kind() {
                TermKind::Map {
                    definition: nested,
                    entries,
                    rest,
                } if nested == &definition => (entries.clone(), rest.clone()),
                _ => (Vec::new(), Some(rest)),
            },
            None => (Vec::new(), None),
        };
        entries.extend(nested_entries);
        entries.sort();
        entries.dedup();
        if entries.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        let attributes = combine_attributes(
            entries
                .iter()
                .flat_map(|(key, value)| [key, value])
                .chain(rest.iter()),
        );
        Self::new(
            TermKind::Map {
                definition,
                entries,
                rest,
            },
            attributes,
        )
    }

    pub fn list(
        definition: Arc<ListDefinition>,
        mut heads: Vec<Self>,
        rest: Option<(Self, Vec<Self>)>,
    ) -> Self {
        let rest = match rest {
            Some((middle, tails)) => match middle.kind() {
                TermKind::List {
                    definition: nested,
                    heads: nested_heads,
                    rest: nested_rest,
                } if nested == &definition => {
                    heads.extend(nested_heads.iter().cloned());
                    match nested_rest {
                        Some((nested_middle, nested_tails)) => {
                            let mut combined_tails = nested_tails.clone();
                            combined_tails.extend(tails);
                            Some((nested_middle.clone(), combined_tails))
                        }
                        None => {
                            heads.extend(tails);
                            None
                        }
                    }
                }
                _ => Some((middle, tails)),
            },
            None => None,
        };
        if heads.is_empty()
            && let Some((middle, tails)) = &rest
            && tails.is_empty()
        {
            return middle.clone();
        }
        let attributes = combine_attributes(
            heads.iter().chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            ),
        );
        Self::new(
            TermKind::List {
                definition,
                heads,
                rest,
            },
            attributes,
        )
    }

    pub fn set(
        definition: Arc<SetDefinition>,
        mut elements: Vec<Self>,
        rest: Option<Self>,
    ) -> Self {
        let (nested_elements, rest) = match rest {
            Some(rest) => match rest.kind() {
                TermKind::Set {
                    definition: nested,
                    elements,
                    rest,
                } if nested == &definition => (elements.clone(), rest.clone()),
                _ => (Vec::new(), Some(rest)),
            },
            None => (Vec::new(), None),
        };
        elements.extend(nested_elements);
        elements.sort();
        elements.dedup();
        if elements.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        let attributes = combine_attributes(elements.iter().chain(rest.iter()));
        Self::new(
            TermKind::Set {
                definition,
                elements,
                rest,
            },
            attributes,
        )
    }

    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }

    pub fn attributes(&self) -> &TermAttributes {
        &self.0.attributes
    }

    /// Return this term with the simplifier's fixed-point cache set.
    ///
    /// Construction deliberately leaves equation-headed applications unevaluated. The
    /// simplifier sets this bit only after scanning the compatible equations for a closed,
    /// normalized application and finding every one inapplicable independently of the current
    /// path condition.
    pub(crate) fn with_evaluated_cache(&self) -> Self {
        if self.attributes().evaluated {
            return self.clone();
        }
        let mut attributes = self.attributes().clone();
        attributes.evaluated = true;
        Self::new(self.kind().clone(), attributes)
    }

    /// Whether two handles share the same immutable term allocation.
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// Transform the immediate children and preserve this term when every child is unchanged.
    ///
    /// Constructors recompute their synthetic attributes when a child changes. Keeping the
    /// original allocation otherwise avoids both that work and structural equality walks in
    /// callers that descend to a fixed point.
    pub(crate) fn try_map_children<E>(
        &self,
        mut transform: impl FnMut(&Self) -> Result<Self, E>,
    ) -> Result<Self, E> {
        let mapped = match self.kind() {
            TermKind::And(left, right) => {
                let new_left = transform(left)?;
                let new_right = transform(right)?;
                if left.ptr_eq(&new_left) && right.ptr_eq(&new_right) {
                    return Ok(self.clone());
                }
                Self::and(new_left, new_right)
            }
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                let new_arguments = arguments
                    .iter()
                    .map(&mut transform)
                    .collect::<Result<Vec<_>, _>>()?;
                if arguments
                    .iter()
                    .zip(&new_arguments)
                    .all(|(old, new)| old.ptr_eq(new))
                {
                    return Ok(self.clone());
                }
                Self::application(symbol.clone(), sort_arguments.clone(), new_arguments)
            }
            TermKind::Injection {
                source,
                target,
                term,
            } => {
                let new_term = transform(term)?;
                if term.ptr_eq(&new_term) {
                    return Ok(self.clone());
                }
                Self::injection(source.clone(), target.clone(), new_term)
            }
            TermKind::Map {
                definition,
                entries,
                rest,
            } => {
                let new_entries = entries
                    .iter()
                    .map(|(key, value)| Ok((transform(key)?, transform(value)?)))
                    .collect::<Result<Vec<_>, E>>()?;
                let new_rest = rest.as_ref().map(&mut transform).transpose()?;
                if entries.iter().zip(&new_entries).all(
                    |((old_key, old_value), (new_key, new_value))| {
                        old_key.ptr_eq(new_key) && old_value.ptr_eq(new_value)
                    },
                ) && options_ptr_eq(rest.as_ref(), new_rest.as_ref())
                {
                    return Ok(self.clone());
                }
                Self::map(definition.clone(), new_entries, new_rest)
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } => {
                let new_heads = heads
                    .iter()
                    .map(&mut transform)
                    .collect::<Result<Vec<_>, _>>()?;
                let new_rest = rest
                    .as_ref()
                    .map(|(middle, tails)| {
                        Ok((
                            transform(middle)?,
                            tails
                                .iter()
                                .map(&mut transform)
                                .collect::<Result<Vec<_>, E>>()?,
                        ))
                    })
                    .transpose()?;
                let rest_unchanged = match (rest, &new_rest) {
                    (None, None) => true,
                    (Some((old_middle, old_tails)), Some((new_middle, new_tails))) => {
                        old_middle.ptr_eq(new_middle)
                            && old_tails
                                .iter()
                                .zip(new_tails)
                                .all(|(old, new)| old.ptr_eq(new))
                    }
                    _ => false,
                };
                if heads
                    .iter()
                    .zip(&new_heads)
                    .all(|(old, new)| old.ptr_eq(new))
                    && rest_unchanged
                {
                    return Ok(self.clone());
                }
                Self::list(definition.clone(), new_heads, new_rest)
            }
            TermKind::Set {
                definition,
                elements,
                rest,
            } => {
                let new_elements = elements
                    .iter()
                    .map(&mut transform)
                    .collect::<Result<Vec<_>, _>>()?;
                let new_rest = rest.as_ref().map(&mut transform).transpose()?;
                if elements
                    .iter()
                    .zip(&new_elements)
                    .all(|(old, new)| old.ptr_eq(new))
                    && options_ptr_eq(rest.as_ref(), new_rest.as_ref())
                {
                    return Ok(self.clone());
                }
                Self::set(definition.clone(), new_elements, new_rest)
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => return Ok(self.clone()),
        };
        Ok(mapped)
    }

    /// Visit application symbols in preorder, including applications nested in collections.
    pub fn visit_symbols(&self, visitor: &mut impl FnMut(&Symbol)) {
        match self.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => {
                visitor(symbol);
                for argument in arguments {
                    argument.visit_symbols(visitor);
                }
            }
            TermKind::And(left, right) => {
                left.visit_symbols(visitor);
                right.visit_symbols(visitor);
            }
            TermKind::Injection { term, .. } => term.visit_symbols(visitor),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    key.visit_symbols(visitor);
                    value.visit_symbols(visitor);
                }
                if let Some(rest) = rest {
                    rest.visit_symbols(visitor);
                }
            }
            TermKind::List { heads, rest, .. } => {
                for head in heads {
                    head.visit_symbols(visitor);
                }
                if let Some((middle, tails)) = rest {
                    middle.visit_symbols(visitor);
                    for tail in tails {
                        tail.visit_symbols(visitor);
                    }
                }
            }
            TermKind::Set { elements, rest, .. } => {
                for element in elements {
                    element.visit_symbols(visitor);
                }
                if let Some(rest) = rest {
                    rest.visit_symbols(visitor);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }

    /// Return the first preprocessing symbol that survived into an internal executable term.
    ///
    /// The stored `has_macro_or_alias` attribute is false exactly when the walk would find
    /// nothing (`hasMacro_iff` of `lean/KRust/TermAttributes.lean`, for the attribute and the
    /// walk as modelled there), so the walk runs only when it will report a symbol, and the
    /// symbol it reports is unchanged (`macro_shortcut_eq`).
    pub fn macro_or_alias_symbol(&self) -> Option<Name> {
        if !self.attributes().has_macro_or_alias() {
            return None;
        }
        self.first_macro_or_alias_symbol()
    }

    /// The first symbol with `macro_or_alias` in the preorder of `visit_symbols`: the walk that
    /// `macro_or_alias_symbol` guards (`firstMacro` of the Lean model).
    pub(crate) fn first_macro_or_alias_symbol(&self) -> Option<Name> {
        let mut found = None;
        self.visit_symbols(&mut |symbol| {
            if found.is_none() && symbol.attributes.macro_or_alias {
                found = Some(symbol.name.clone());
            }
        });
        found
    }

    /// Whether this term is concrete once equation normalization has reached a fixed point.
    ///
    /// K emits overloaded productions and productions with anywhere equations without the
    /// `constructor` attribute.  Once equation normalization has reached a fixed point, a
    /// variable-free application of one of those symbols is nevertheless a concrete program
    /// fragment: it must not make an otherwise ground configuration eligible for narrowing.
    /// Ordinary function applications remain symbolic even when they are ground.
    pub fn concrete_after_normalization(&self) -> bool {
        self.attributes().concrete_after_normalization
    }

    /// Whether two normalized concrete terms are structurally distinct.
    ///
    /// Distinct rigid heads cannot denote the same normalized program value. Equal heads expose
    /// their arguments only when the symbol is a constructor or is declared injective. This keeps
    /// ordinary functions and non-injective symbolic applications out of structural decisions.
    pub fn structurally_distinct_after_normalization(&self, other: &Self) -> bool {
        if self == other
            || !self.concrete_after_normalization()
            || !other.concrete_after_normalization()
        {
            return false;
        }
        match (self.kind(), other.kind()) {
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort != right_sort || left_value != right_value,
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    arguments: right_arguments,
                },
            ) => {
                if left_symbol.name != right_symbol.name || left_sorts != right_sorts {
                    return true;
                }
                (left_symbol.attributes.symbol_type == SymbolType::Constructor
                    || left_symbol.attributes.injective)
                    && left_arguments
                        .iter()
                        .zip(right_arguments)
                        .any(|(left, right)| left.structurally_distinct_after_normalization(right))
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right,
                },
            ) if left_source == right_source && left_target == right_target => {
                left.structurally_distinct_after_normalization(right)
            }
            _ => false,
        }
    }

    pub fn sort(&self) -> Sort {
        match self.kind() {
            TermKind::And(_, right) => right.sort(),
            TermKind::Application {
                symbol,
                sort_arguments,
                ..
            } => {
                let substitution = symbol
                    .sort_variables
                    .iter()
                    .cloned()
                    .zip(sort_arguments.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                substitute_sort(&symbol.result_sort, &substitution)
            }
            TermKind::DomainValue { sort, .. } | TermKind::Variable(Variable { sort, .. }) => {
                sort.clone()
            }
            TermKind::Injection { target, .. } => target.clone(),
            TermKind::Map { definition, .. } => Sort::simple(definition.map_sort.clone()),
            TermKind::List { definition, .. } | TermKind::Set { definition, .. } => {
                Sort::simple(definition.list_sort.clone())
            }
        }
    }

    fn new(kind: TermKind, mut attributes: TermAttributes) -> Self {
        measure::bump(Counter::TermConstructed);
        attributes.ceil_free = ceil_free(&kind);
        attributes.has_macro_or_alias = has_macro_or_alias(&kind);
        attributes.k_cells = k_cells(&kind);
        attributes.hash = calculate_hash(&kind);
        Self(Arc::new(TermData { attributes, kind }))
    }
}

/// The `ceil_free` attribute of a node with this kind, from its children's stored attributes, in
/// time linear in the number of children.
///
/// Meaning: when it is true, `definedness::ceil_term_recursive` returns no predicate for the term,
/// whatever the definition. Each arm follows from the arm of `ceil_term_recursive` for the same
/// kind, which emits a predicate of its own only in these cases:
/// - an application of a `Partial` function emits its ceil (or a ceil equation's predicates);
///   any other application only collects its arguments' predicates;
/// - `And`, an injection and a list only collect their children's predicates;
/// - a domain value and an element variable emit nothing; a set variable emits its ceil;
/// - a map or a set emits a not-in predicate per key or element when it has a rest, and a
///   disequality for each pair of keys (elements) that `normalized_ground_terms_are_distinct`
///   does not separate.
///
/// For the pairs, the attribute accepts only keys that share one `KeyHeader`: all domain values,
/// or all `inj{S, T}` of a domain value for one `S` and `T`. Two distinct such keys are separated
/// by `structurally_distinct_after_normalization` alone, so the matcher that
/// `normalized_ground_terms_are_distinct` falls back on is never needed. Keys with different
/// headers, such as `inj{Int, KItem}(1)` and `inj{String, KItem}("a")`, fall to that matcher, and
/// the attribute is false for them. Distinctness of the keys themselves comes from the
/// constructors: `Term::set` sorts and deduplicates its elements, so they are pairwise distinct;
/// `Term::map` sorts its entries by `(key, value)` but deduplicates pairs, not keys, so `k |-> 1`
/// and `k |-> 2` can both survive, adjacent, and the attribute checks that adjacent keys differ.
/// Those constructor invariants and the order they rely on are checked by
/// `tests/backend/term_order.rs` (`constructed_collections_are_sorted`,
/// `ord_for_term_is_transitive`, `ord_for_term_equal_is_eq`).
///
/// This is the function `ceilFree` of `lean/KRust/TermAttributes.lean`, which proves the meaning
/// above (`ceilFree_sound`); `tests::lean_bridge` compares it with the Lean definition, and the
/// `debug_assert!` in `definedness::ceil_term_recursive` recomputes the walk wherever it is true.
fn ceil_free(kind: &TermKind) -> bool {
    let free = |term: &Term| term.attributes().ceil_free;
    match kind {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            symbol.attributes.symbol_type != SymbolType::Function(FunctionType::Partial)
                && arguments.iter().all(free)
        }
        TermKind::And(left, right) => free(left) && free(right),
        TermKind::Injection { term, .. } => free(term),
        TermKind::DomainValue { .. } => true,
        TermKind::Variable(variable) => variable.kind == VariableKind::Element,
        TermKind::Map { entries, rest, .. } => {
            rest.is_none()
                && entries.iter().all(|(key, value)| free(key) && free(value))
                && share_one_key_header(entries.iter().map(|(key, _)| key))
                && entries.windows(2).all(|pair| pair[0].0 != pair[1].0)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().all(free)
                && rest
                    .as_ref()
                    .is_none_or(|(middle, tails)| free(middle) && tails.iter().all(free))
        }
        TermKind::Set { elements, rest, .. } => {
            rest.is_none() && elements.iter().all(free) && share_one_key_header(elements.iter())
        }
    }
}

/// Fold `step` over the immediate subterms of a node with this kind, in the order
/// `Term::visit_symbols` and `rule::find_k_cells` visit them: the arguments; left then right; the
/// injected term; each key then its value, then the rest; the heads, then the middle and the
/// tails; the elements, then the rest.
fn fold_children<B>(kind: &TermKind, init: B, mut step: impl FnMut(B, &Term) -> B) -> B {
    match kind {
        TermKind::Application { arguments, .. } => arguments.iter().fold(init, step),
        TermKind::And(left, right) => {
            let init = step(init, left);
            step(init, right)
        }
        TermKind::Injection { term, .. } => step(init, term),
        TermKind::Map { entries, rest, .. } => {
            let init = entries.iter().fold(init, |acc, (key, value)| {
                let acc = step(acc, key);
                step(acc, value)
            });
            rest.iter().fold(init, step)
        }
        TermKind::List { heads, rest, .. } => {
            let init = heads.iter().fold(init, &mut step);
            match rest {
                Some((middle, tails)) => {
                    let init = step(init, middle);
                    tails.iter().fold(init, step)
                }
                None => init,
            }
        }
        TermKind::Set { elements, rest, .. } => {
            let init = elements.iter().fold(init, &mut step);
            rest.iter().fold(init, step)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => init,
    }
}

/// The `has_macro_or_alias` attribute of a node with this kind: the symbol's `macro_or_alias` at
/// an application, or any child's stored attribute. This is `hasMacro` of
/// `lean/KRust/TermAttributes.lean`; `tests::lean_bridge` compares the stored attribute with it at
/// every subterm.
fn has_macro_or_alias(kind: &TermKind) -> bool {
    let own =
        matches!(kind, TermKind::Application { symbol, .. } if symbol.attributes.macro_or_alias);
    fold_children(kind, own, |found, child| {
        found || child.attributes().has_macro_or_alias
    })
}

/// The `k_cells` attribute of a node with this kind: 1 at a `<k>` cell whatever its arguments
/// hold, because `rule::find_k_cells` does not descend below a `<k>` cell; otherwise the sum of
/// the children's stored counts, saturated at 2. This is `kCells` of
/// `lean/KRust/TermAttributes.lean`, which proves it equal to the number of `<k>` cells not nested
/// in one, saturated at 2 (`kCells_eq`); `tests::lean_bridge` compares the stored attribute with
/// it at every subterm.
fn k_cells(kind: &TermKind) -> u8 {
    if let TermKind::Application { symbol, .. } = kind
        && symbol.is(WellKnownSymbol::KCell)
    {
        return 1;
    }
    fold_children(kind, 0, |count, child| {
        (count + child.attributes().k_cells).min(2)
    })
}

/// The class of a collection key for which `structurally_distinct_after_normalization` decides
/// distinctness from another key of the same class (`keyHeader` in the Lean model).
#[derive(PartialEq)]
enum KeyHeader<'a> {
    DomainValue,
    Injection { source: &'a Sort, target: &'a Sort },
}

fn key_header(key: &Term) -> Option<KeyHeader<'_>> {
    match key.kind() {
        TermKind::DomainValue { .. } => Some(KeyHeader::DomainValue),
        TermKind::Injection {
            source,
            target,
            term,
        } if matches!(term.kind(), TermKind::DomainValue { .. }) => {
            Some(KeyHeader::Injection { source, target })
        }
        _ => None,
    }
}

/// Every key has a header, and all share the first key's (`oneHeader` in the Lean model).
fn share_one_key_header<'a>(mut keys: impl Iterator<Item = &'a Term>) -> bool {
    let Some(first) = keys.next() else {
        return true;
    };
    let Some(header) = key_header(first) else {
        return false;
    };
    keys.all(|key| key_header(key).as_ref() == Some(&header))
}

fn options_ptr_eq(left: Option<&Term>, right: Option<&Term>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => left.ptr_eq(right),
        _ => false,
    }
}

fn is_int_sort(sort: &Sort) -> bool {
    sort.is_builtin(BuiltinSort::Int)
}

fn canonical_int_text(value: KoreString) -> KoreString {
    let Ok(text) = value.as_utf8() else {
        return value;
    };
    let bytes = text.as_bytes();
    let canonical = match bytes {
        [b'0'] => true,
        [b'-', b'1'..=b'9', rest @ ..] | [b'1'..=b'9', rest @ ..] => {
            rest.iter().all(u8::is_ascii_digit)
        }
        _ => false,
    };
    if canonical {
        return value;
    }
    text.parse::<BigInt>()
        .map_or(value, |integer| integer.to_string().into())
}

fn map_parts(definition: &Arc<MapDefinition>, term: &Term) -> (Vec<(Term, Term)>, Option<Term>) {
    match term.kind() {
        TermKind::Map {
            definition: found,
            entries,
            rest,
        } if found == definition => (entries.clone(), rest.clone()),
        _ => (Vec::new(), Some(term.clone())),
    }
}

fn combine_lists(
    definition: Arc<ListDefinition>,
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    left: Term,
    right: Term,
) -> Term {
    match (left.kind(), right.kind()) {
        (
            TermKind::List {
                definition: left_definition,
                heads: left_heads,
                rest: left_rest,
            },
            TermKind::List {
                definition: right_definition,
                heads: right_heads,
                rest: right_rest,
            },
        ) if left_definition == &definition && right_definition == &definition => {
            match (left_rest, right_rest) {
                (None, None) => {
                    let mut heads = left_heads.clone();
                    heads.extend(right_heads.iter().cloned());
                    Term::list(definition, heads, None)
                }
                (None, Some(rest)) => {
                    let mut heads = left_heads.clone();
                    heads.extend(right_heads.iter().cloned());
                    Term::list(definition, heads, Some(rest.clone()))
                }
                (Some((middle, tails)), None) => {
                    let mut tails = tails.clone();
                    tails.extend(right_heads.iter().cloned());
                    Term::list(
                        definition,
                        left_heads.clone(),
                        Some((middle.clone(), tails)),
                    )
                }
                (Some(_), Some(_)) => {
                    Term::application_raw(symbol, sort_arguments, vec![left, right])
                }
            }
        }
        (
            TermKind::List {
                definition: found,
                heads,
                rest: None,
            },
            _,
        ) if found == &definition => {
            Term::list(definition, heads.clone(), Some((right, Vec::new())))
        }
        (
            _,
            TermKind::List {
                definition: found,
                heads,
                rest: None,
            },
        ) if found == &definition => {
            Term::list(definition, Vec::new(), Some((left, heads.clone())))
        }
        _ => Term::application_raw(symbol, sort_arguments, vec![left, right]),
    }
}

fn combine_sets(
    definition: Arc<SetDefinition>,
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    left: Term,
    right: Term,
) -> Term {
    let (mut elements, left_rest) = set_parts(&definition, &left);
    let (right_elements, right_rest) = set_parts(&definition, &right);
    elements.extend(right_elements);
    let rest = match (left_rest, right_rest) {
        (None, rest) | (rest, None) => rest,
        (Some(left), Some(right)) => Some(Term::application_raw(
            symbol,
            sort_arguments,
            vec![left, right],
        )),
    };
    Term::set(definition, elements, rest)
}

fn set_parts(definition: &Arc<SetDefinition>, term: &Term) -> (Vec<Term>, Option<Term>) {
    match term.kind() {
        TermKind::Set {
            definition: found,
            elements,
            rest,
        } if found == definition => (elements.clone(), rest.clone()),
        _ => (Vec::new(), Some(term.clone())),
    }
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Name, Sort>) -> Sort {
    match sort {
        Sort::Variable(name) => substitution
            .get(name)
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        Sort::Application { name, arguments } => Sort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_sort(argument, substitution))
                .collect(),
        },
    }
}

fn combine_attributes<'a>(terms: impl IntoIterator<Item = &'a Term>) -> TermAttributes {
    let mut terms = terms.into_iter();
    let Some(first) = terms.next() else {
        // These flags are conjunctions over child terms.  Their identity is true, which is
        // essential for nullary constructors and empty builtin collections to be recognized as
        // concrete constructor-like values.
        return TermAttributes {
            constructor_like: true,
            concrete_after_normalization: true,
            ..TermAttributes::default()
        };
    };
    let mut combined = first.attributes().clone();
    for term in terms {
        let attributes = term.attributes();
        combined
            .variables
            .extend(attributes.variables.iter().cloned());
        combined.evaluated &= attributes.evaluated;
        combined.constructor_like &= attributes.constructor_like;
        combined.concrete_after_normalization &= attributes.concrete_after_normalization;
        combined.can_be_evaluated &= attributes.can_be_evaluated;
    }
    combined.hash = 0;
    combined
}

fn calculate_hash(kind: &TermKind) -> u64 {
    let mut hasher = DefaultHasher::new();
    kind.hash(&mut hasher);
    hasher.finish()
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.attributes.hash == other.0.attributes.hash && self.0.kind == other.0.kind)
    }
}

impl Eq for Term {}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        // A shared term equals itself; without this, comparing two handles of one large term
        // (a substitution binding copied into several solutions) walks it in full.
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.0.kind.cmp(&other.0.kind)
    }
}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.attributes.hash);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn constructor() -> Arc<Symbol> {
        Arc::new(Symbol::constructor("con1", vec![sort()], sort()))
    }

    fn collection_symbols() -> CollectionSymbols {
        CollectionSymbols {
            unit: "unit".into(),
            element: "element".into(),
            concat: "concat".into(),
        }
    }

    #[test]
    fn caches_free_variables_and_constructor_attributes() {
        let variable = Variable::new("X", sort());
        let term = Term::application(
            constructor(),
            Vec::new(),
            vec![Term::variable(variable.clone())],
        );
        assert_eq!(term.attributes().variables, BTreeSet::from([variable]));
        assert!(!term.attributes().constructor_like);

        let concrete = Term::application(
            constructor(),
            Vec::new(),
            vec![Term::domain_value(sort(), "value")],
        );
        assert!(concrete.attributes().constructor_like);
        assert!(concrete.attributes().evaluated);
    }

    #[test]
    fn nullary_constructors_are_constructor_like() {
        let term = Term::application(
            Arc::new(Symbol::constructor("constant", Vec::new(), sort())),
            Vec::new(),
            Vec::new(),
        );

        assert!(term.attributes().constructor_like);
        assert!(term.attributes().evaluated);
    }

    #[test]
    fn collapses_nested_injections() {
        let a = Sort::simple("A");
        let b = Sort::simple("B");
        let c = Sort::simple("C");
        let value = Term::domain_value(a.clone(), "value");
        let nested = Term::injection(
            b.clone(),
            c.clone(),
            Term::injection(a.clone(), b, value.clone()),
        );
        assert_eq!(nested, Term::injection(a, c, value));
    }

    #[test]
    fn clones_share_immutable_storage() {
        let term = Term::domain_value(sort(), "value");
        assert!(Arc::ptr_eq(&term.0, &term.clone().0));
    }

    #[test]
    fn int_domain_values_are_canonical_at_construction() {
        let int_sort = Sort::simple("SortInt");
        for (source, expected) in [("+3", "3"), ("007", "7"), ("-0", "0"), ("-12", "-12")] {
            let term = Term::domain_value(int_sort.clone(), source);
            let TermKind::DomainValue { value, .. } = term.kind() else {
                unreachable!()
            };
            assert_eq!(value, expected, "{source}");
        }

        let canonical = KoreString::from("12");
        let canonical_term = Term::domain_value(int_sort.clone(), canonical.clone());
        let TermKind::DomainValue { value, .. } = canonical_term.kind() else {
            unreachable!()
        };
        assert!(std::ptr::eq(value.as_bytes(), canonical.as_bytes()));

        let signed = Term::domain_value(int_sort.clone(), "+3");
        let unsigned = Term::domain_value(int_sort, "3");
        assert_eq!(signed, unsigned);
        assert_eq!(
            calculate_hash(signed.kind()),
            calculate_hash(unsigned.kind())
        );
    }

    #[test]
    fn domain_value_equality_and_hash_preserve_raw_bytes() {
        let sort = Sort::builtin(BuiltinSort::String);
        let raw = Term::domain_value(sort.clone(), vec![0xff, 0x80]);
        let same = Term::domain_value(sort.clone(), vec![0xff, 0x80]);
        let utf8 = Term::domain_value(sort, "ÿ\u{80}");

        assert_eq!(raw, same);
        assert_eq!(calculate_hash(raw.kind()), calculate_hash(same.kind()));
        assert_ne!(raw, utf8);
    }

    #[test]
    fn canonicalizes_internal_collections() {
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        let map_definition = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let nested_map = Term::map(
            map_definition.clone(),
            vec![(two.clone(), one.clone())],
            None,
        );
        let map = Term::map(
            map_definition,
            vec![(one.clone(), two.clone()), (one.clone(), two.clone())],
            Some(nested_map),
        );
        let TermKind::Map { entries, .. } = map.kind() else {
            panic!("expected an internal map")
        };
        assert_eq!(entries.len(), 2);
        assert!(entries.windows(2).all(|pair| pair[0] < pair[1]));

        let set_definition = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let set = Term::set(
            set_definition,
            vec![two.clone(), one.clone(), one.clone()],
            None,
        );
        let TermKind::Set { elements, .. } = set.kind() else {
            panic!("expected an internal set")
        };
        assert_eq!(elements, &[one, two]);
    }

    #[test]
    fn builtin_sort_equals_simple_of_its_kore_name() {
        for sort in BuiltinSort::ALL {
            assert_eq!(
                Sort::builtin(sort),
                Sort::simple(sort.kore_name()),
                "{sort:?}"
            );
            assert!(Sort::builtin(sort).is_builtin(sort), "{sort:?}");
            assert!(Sort::simple(sort.kore_name()).is_builtin(sort), "{sort:?}");
        }
        let Sort::Application { name: first, .. } = Sort::builtin(BuiltinSort::Int) else {
            unreachable!()
        };
        let Sort::Application { name: second, .. } = Sort::builtin(BuiltinSort::Int) else {
            unreachable!()
        };
        assert!(
            Arc::ptr_eq(&first, &second),
            "builtin names share one allocation"
        );
    }

    #[test]
    fn is_builtin_rejects_a_parametric_application_of_the_same_name() {
        let parametric = Sort::application(
            BuiltinSort::Map.kore_name(),
            vec![Sort::builtin(BuiltinSort::K)],
        );
        assert!(!parametric.is_builtin(BuiltinSort::Map));
        assert!(!Sort::Variable("SortMap".into()).is_builtin(BuiltinSort::Map));
        assert!(!Sort::builtin(BuiltinSort::Set).is_builtin(BuiltinSort::Map));
        let symbol = Symbol::constructor("inj", Vec::new(), Sort::builtin(BuiltinSort::K));
        assert!(symbol.is(WellKnownSymbol::Inj));
        assert!(!symbol.is(WellKnownSymbol::KSeq));
    }
}
