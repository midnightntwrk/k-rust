//! Immutable backend terms with cached synthetic attributes (`variables`, `evaluated`,
//! `constructor_like`): the layer-1 representation every algorithm shares; a responsibility, not
//! an algorithm; `Counter::TermConstructed` per construction; no worklist.
//!
//! Storage and collection canonicalization invariants are checked by `tests/backend/term_order.rs`.
//! The Lean attribute bridge checks `ceil_free`, macro presence and k-cell count separately;
//! it does not certify the collision exclusion for value shape:
//!
//! ```toml algorithm-representation
//! id = "representation.backend.term"
//! name = "immutable backend term with a cached structural hash"
//! type = "k_rust_backend::term::Term"
//! sites = ["Term", "TermData", "Term::new", "Term::allocate", "synthesize_attributes",
//!     "set_kind_attributes", "marked_attributes", "Term::map", "Term::set",
//!     "Term::with_evaluated_cache", "Term::marked_evaluated", "calculate_hash", "ceil_free",
//!     "key_header", "share_one_key_header", "fold_children", "k_cells", "Term::eq", "Term::cmp"]
//! invariant = """\
//! Term::allocate is the only place a TermData is built, and a TermData is never mutated after it is \
//! shared: Term and TermData keep their fields private. Term::allocate sets the stored hash to \
//! calculate_hash of the kind, so Eq for Term (pointer equality, or equal hash and equal kind) \
//! is structural equality of the kind, and Ord for Term is the derived order on the kind. \
//! Term::allocate also sets the stored ceil_free attribute to ceil_free of the kind, which reads \
//! only the kind and the children's stored ceil_free, so the stored value of every Term is \
//! ceilFree of the Lean model applied to it; likewise has_macro_or_alias and k_cells, from the \
//! children's stored values, are hasMacro and kCells of the Lean model. Only Term::map builds a \
//! Map kind: after merging the entries of a same-definition rest, it verifies nondecreasing (key, \
//! value) order or sorts, retaining repeated keys and bindings. Only Term::set builds a Set kind: \
//! after merging the elements of a same-definition rest, it sorts and retains repeated elements. \
//! Allocation synthesizes shape from the completed kind and every immediate child: a repeated \
//! map key or set element anywhere below a term excludes constructor_like and \
//! concrete_after_normalization; a collision root also excludes structural evaluated. \
//! with_evaluated_cache rebuilds through the same allocator from its immutable source: the kind \
//! is the source's, and an Application keeps every other stored attribute of the source, which \
//! equals the structural and kind-derived value for that kind (checked against recomputation in \
//! debug); other kinds recompute them. Only evaluated is overridden, with a collision root taking \
//! precedence. The Lean ceilFree proofs concern the separate conservative ceil_free attribute, \
//! not this hereditary shape exclusion."""
//! tests = ["crates/k-rust-backend/tests/backend/term_order.rs", "crates/k-rust-backend/src/tests/definedness.rs"]
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
    collections::{BTreeMap, BTreeSet},
    hash::{Hash, Hasher},
    sync::{Arc, OnceLock},
};

use k_rust_kore::kore::ast::KoreString;
use k_rust_kore::measure::{self, Counter};
use k_rust_kore::names::{BuiltinSort, WellKnownSymbol};
use num_bigint::BigInt;
use rustc_hash::FxHasher;

use crate::smt::SmtType;

pub mod head;
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

/// Axioms that identify applications with different arguments.
/// Freeness is decided only by [`SymbolAttributes::head_role`].
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AlgebraicAxioms {
    assoc: bool,
    comm: bool,
    idem: bool,
    unit: bool,
}

impl AlgebraicAxioms {
    #[must_use]
    pub const fn assoc() -> Self {
        Self {
            assoc: true,
            comm: false,
            idem: false,
            unit: false,
        }
    }
    #[must_use]
    pub const fn comm() -> Self {
        Self {
            assoc: false,
            comm: true,
            idem: false,
            unit: false,
        }
    }
    #[must_use]
    pub const fn idem() -> Self {
        Self {
            assoc: false,
            comm: false,
            idem: true,
            unit: false,
        }
    }
    #[must_use]
    pub const fn unit() -> Self {
        Self {
            assoc: false,
            comm: false,
            idem: false,
            unit: true,
        }
    }
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        !self.assoc && !self.comm && !self.idem && !self.unit
    }
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self {
            assoc: self.assoc || other.assoc,
            comm: self.comm || other.comm,
            idem: self.idem || other.idem,
            unit: self.unit || other.unit,
        }
    }
}

/// What the declaration and identifying axioms imply about applications, computed by [`SymbolAttributes::head_role`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HeadRole {
    /// `constructor` or `sortInjection`, with no algebraic facts, neither `anywhere` without
    /// a declared `function` nor a macro or alias: applications with different roots or different arguments denote different
    /// values.
    FreeConstructor,
    /// `anywhere` and not a declared `function`: an application denotes the value of its normal
    /// form under the definition's equations, and its root is that value's root only when the
    /// application is a normal form. The equations identify applications with different
    /// arguments, so the role carries no injectivity.
    EquationHead,
    /// A computed or injective symbol. `declared` is the KORE `function` attribute, as distinct from a symbol
    /// that is total only because it is `functional`; `injective` is the declared attribute,
    /// dropped with `anywhere` or algebraic axioms, which may identify applications
    /// with different arguments.
    Function {
        declared: bool,
        injective: bool,
        /// A failed as-written argument match can refute the application match only when no
        /// algebraic axiom identifies applications with different arguments.
        refutable_arguments: bool,
    },
    /// `macro` or `alias`: preprocessing replaces every application, so an application that is
    /// still present denotes a value the backend does not know.
    Residual,
    /// Neither free nor computed: no individuating declaration distinguishes its applications,
    /// or an algebraic axiom identifies applications with different arguments.
    /// Only syntactic identity decides.
    Uninterpreted,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SymbolAttributes {
    /// Whether applications are constructed or computed, and whether a computed one is total.
    /// Algorithms read freeness from [`Self::head_role`]; the readers of this field that remain
    /// are listed there.
    pub symbol_type: SymbolType,
    /// The source symbol carries the KORE `constructor` attribute. `SymbolType::Constructor`
    /// also covers `sortInjection` declarations, which embed source-sort values rather than
    /// adding constructor roots.
    declared_constructor: bool,
    /// The source symbol carries the KORE `anywhere` attribute. Read through [`Self::head_role`].
    anywhere: bool,
    /// The source symbol carries the KORE `function` attribute, as distinct from a symbol that is
    /// total only because it is `functional`. Read through [`Self::head_role`].
    declared_function: bool,
    pub binder: bool,
    /// The source symbol carries the KORE `injective` attribute. Read through
    /// [`Self::head_role`], which keeps it only without `anywhere` or algebraic axioms.
    injective: bool,
    algebraic: AlgebraicAxioms,
    pub macro_or_alias: bool,
    pub has_evaluators: bool,
    pub smt: Option<SmtType>,
    pub hook: Option<Name>,
    pub collection: Option<CollectionMetadata>,
}

/// Every field of [`SymbolAttributes`], all visible inside the crate: the one way to build
/// attributes from a declaration with each field named (the internalizer,
/// `definition::symbol_attributes`), and, in tests, the declaration read back as written
/// (`SymbolAttributes::declaration`, for the Lean bridge, whose `Sym` reads the flags raw).
///
/// The conversion into [`SymbolAttributes`] and `SymbolAttributes::declaration` name every field
/// of both structs without `..`, so a new field of [`SymbolAttributes`] does not compile until it
/// is added here, and the Lean bridge (`tests::lean_bridge::term_json::symbol_json`) destructures
/// this struct without `..`, so it does not compile until the field reaches the model's `Sym`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SymbolDeclaration {
    pub(crate) symbol_type: SymbolType,
    pub(crate) declared_constructor: bool,
    pub(crate) anywhere: bool,
    pub(crate) declared_function: bool,
    pub(crate) binder: bool,
    pub(crate) injective: bool,
    pub(crate) algebraic: AlgebraicAxioms,
    pub(crate) macro_or_alias: bool,
    pub(crate) has_evaluators: bool,
    pub(crate) smt: Option<SmtType>,
    pub(crate) hook: Option<Name>,
    pub(crate) collection: Option<CollectionMetadata>,
}

impl From<SymbolDeclaration> for SymbolAttributes {
    fn from(declaration: SymbolDeclaration) -> Self {
        let SymbolDeclaration {
            symbol_type,
            declared_constructor,
            anywhere,
            declared_function,
            binder,
            injective,
            algebraic,
            macro_or_alias,
            has_evaluators,
            smt,
            hook,
            collection,
        } = declaration;
        Self {
            symbol_type,
            declared_constructor,
            anywhere,
            declared_function,
            binder,
            injective,
            algebraic,
            macro_or_alias,
            has_evaluators,
            smt,
            hook,
            collection,
        }
    }
}

impl SymbolAttributes {
    /// The instance-sort check applies to symbols declared with the KORE `constructor`
    /// attribute, including declarations that also carry `sortInjection`.
    pub(crate) fn declares_constructor(&self) -> bool {
        self.declared_constructor
    }

    pub fn constructor() -> Self {
        Self {
            symbol_type: SymbolType::Constructor,
            declared_constructor: true,
            anywhere: false,
            declared_function: false,
            binder: false,
            injective: false,
            algebraic: AlgebraicAxioms::default(),
            macro_or_alias: false,
            has_evaluators: true,
            smt: None,
            hook: None,
            collection: None,
        }
    }

    /// These attributes with the KORE `anywhere` attribute set to `anywhere`.
    ///
    /// The flag is private, so a struct literal cannot set it; the builder is the way:
    ///
    /// ```compile_fail
    /// use k_rust_backend::term::SymbolAttributes;
    /// let _ = SymbolAttributes { anywhere: true, ..SymbolAttributes::constructor() };
    /// ```
    ///
    /// ```
    /// use k_rust_backend::term::SymbolAttributes;
    /// let _ = SymbolAttributes::constructor().with_anywhere(true);
    /// ```
    #[must_use]
    pub fn with_anywhere(mut self, anywhere: bool) -> Self {
        self.anywhere = anywhere;
        self
    }

    /// These attributes with the identifying axioms supplied by the definition.
    #[must_use]
    pub fn with_algebraic_axioms(mut self, algebraic: AlgebraicAxioms) -> Self {
        self.algebraic = algebraic;
        self
    }

    /// The identifying axioms. Freeness is read only through [`Self::head_role`].
    #[must_use]
    pub fn algebraic_axioms(&self) -> AlgebraicAxioms {
        self.algebraic
    }

    /// These attributes with the KORE `function` attribute set to `declared`.
    #[must_use]
    pub fn with_declared_function(mut self, declared: bool) -> Self {
        self.declared_function = declared;
        self
    }

    /// These attributes with the KORE `injective` attribute set to `injective`.
    #[must_use]
    pub fn with_injective(mut self, injective: bool) -> Self {
        self.injective = injective;
        self
    }

    /// The role of the symbol, decided from its declaration and identifying axioms:
    /// a `macro` or `alias` symbol is [`HeadRole::Residual`];
    /// otherwise a symbol with algebraic facts that is a constructor or lacks a declared
    /// function is [`HeadRole::Uninterpreted`];
    /// otherwise an `anywhere` symbol that is not a declared function is an
    /// [`HeadRole::EquationHead`], whatever its `constructor` attribute, because the definition's
    /// own equations identify its applications, which contradicts freeness;
    /// otherwise a `constructor` or `sortInjection` symbol is a [`HeadRole::FreeConstructor`];
    /// otherwise a declared function or injective symbol is a [`HeadRole::Function`], whose
    /// injectivity counts only without `anywhere` or algebraic axioms;
    /// otherwise it is [`HeadRole::Uninterpreted`].
    ///
    /// No algorithm reads the `anywhere`, `declared_function` or `injective` flags; outside this
    /// module they are private:
    ///
    /// ```compile_fail
    /// use k_rust_backend::term::Symbol;
    /// fn read(symbol: &Symbol) {
    ///     let _ = symbol.attributes.injective;
    /// }
    /// ```
    ///
    /// ```
    /// use k_rust_backend::term::Symbol;
    /// fn read(symbol: &Symbol) {
    ///     let _ = symbol.attributes.head_role();
    /// }
    /// ```
    ///
    /// Freeness is read here and nowhere else. The public `symbol_type` field stays, for the
    /// readers that ask whether an application is computed or total rather than free, and a
    /// read of it spelled `symbol_type == SymbolType::Constructor` would bypass this role. The
    /// readers of `symbol_type` that remain:
    /// - `synthesize_attributes` (the possible normalized shape, excluding uninterpreted roots
    ///   through this role) and `ceil_free` (partiality), here;
    /// - partiality or totality: `definedness::ceil_term_node`, `smt::symbol_exactness`,
    ///   `simplify` (`is_total_application`, `occurs_under_total_context`),
    ///   `rule::computed_attributes` (undefined symbols), `definition::inhabited_sorts` (value
    ///   builders);
    /// - computed rather than constructed: `rewrite::recover` (`recover_indeterminate_match`,
    ///   `is_functional_pattern`, `contains_function_pattern`),
    ///   `matching::collections::list_update_cannot_match`, the matcher's `is_function`;
    /// - the declaration as written: `verify::verify_function_head` (an equation's left-hand
    ///   side headed by a symbol declared constructor) and
    ///   `builtin::substitution::KVarSorts::of` (every symbol declared constructor builds values
    ///   whose sort may hold a `KVar`, whatever its role, so the `KVar`-free sorts stay an
    ///   under-approximation).
    #[inline]
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub fn head_role(&self) -> HeadRole {
        if self.macro_or_alias {
            return HeadRole::Residual;
        }
        // Loading rejects algebraic constructors. Public builders may combine raw facts,
        // so even a simultaneous function flag must not make such a constructor free.
        if !self.algebraic.is_empty()
            && (!self.declared_function || self.symbol_type == SymbolType::Constructor)
        {
            return HeadRole::Uninterpreted;
        }
        if self.anywhere && !self.declared_function {
            return HeadRole::EquationHead;
        }
        match self.symbol_type {
            SymbolType::Constructor => HeadRole::FreeConstructor,
            SymbolType::Function(_) => {
                if self.declared_function {
                    HeadRole::Function {
                        declared: true,
                        injective: self.injective && !self.anywhere && self.algebraic.is_empty(),
                        refutable_arguments: self.algebraic.is_empty(),
                    }
                } else if self.injective {
                    HeadRole::Function {
                        declared: false,
                        injective: true,
                        refutable_arguments: true,
                    }
                } else {
                    HeadRole::Uninterpreted
                }
            }
        }
    }

    /// The declaration as written, every field including the flags [`Self::head_role`] folds,
    /// for the Lean bridge only. No algorithm reads the flags, so this is test-only.
    #[cfg(test)]
    pub(crate) fn declaration(&self) -> SymbolDeclaration {
        let Self {
            symbol_type,
            declared_constructor,
            anywhere,
            declared_function,
            binder,
            injective,
            algebraic,
            macro_or_alias,
            has_evaluators,
            smt,
            hook,
            collection,
        } = self.clone();
        SymbolDeclaration {
            symbol_type,
            declared_constructor,
            anywhere,
            declared_function,
            binder,
            injective,
            algebraic,
            macro_or_alias,
            has_evaluators,
            smt,
            hook,
            collection,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Symbol {
    pub name: Name,
    pub sort_variables: Vec<Name>,
    pub argument_sorts: Vec<Sort>,
    pub result_sort: Sort,
    pub attributes: SymbolAttributes,
}

/// A symbol hashes as its name. Equal symbols have equal names, so this agrees with `Eq`; a
/// definition declares one symbol per name, so the name already tells its symbols apart, and
/// every term construction (`Term::new` hashes the application's symbol) is spared hashing
/// the signature and attributes.
impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
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
    /// See [`TermAttributes::ceil_free`]; set only by `Term::allocate`, from the kind.
    ceil_free: bool,
    /// See [`TermAttributes::has_macro_or_alias`]; set only by `Term::allocate`, from the kind.
    has_macro_or_alias: bool,
    /// See [`TermAttributes::k_cells`]; set only by `Term::allocate`, from the kind.
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
    /// construction: see `ceil_free`, which `Term::allocate` stores here.
    pub fn ceil_free(&self) -> bool {
        self.ceil_free
    }

    /// Whether some application in this term has a symbol with `macro_or_alias`: exactly when
    /// `Term::first_macro_or_alias_symbol` finds one. See `has_macro_or_alias`, which `Term::allocate`
    /// stores here.
    pub fn has_macro_or_alias(&self) -> bool {
        self.has_macro_or_alias
    }

    /// The number of `<k>` cells of this term that are not nested in a `<k>` cell, saturated at
    /// 2. See `k_cells`, which `Term::allocate` stores here.
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
        Self::new(TermKind::And(left, right))
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
        Self::new(TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        })
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
        Self::new(TermKind::DomainValue { sort, value })
    }

    pub fn variable(variable: Variable) -> Self {
        Self::new(TermKind::Variable(variable))
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
        Self::new(TermKind::Injection {
            source,
            target,
            term,
        })
    }

    /// The map binding the keys of `entries` and of `rest`, its entries sorted by `(key, value)`.
    ///
    /// Map concatenation is nilpotent on keys: `(K |-> V1) (K |-> V2)` is `\bottom` whether or
    /// not `V1` and `V2` are equal, because a map binds each key once (the update is `M[K <- V]`).
    /// So this constructor keeps a key bound twice, with the same value or not, and the repeat
    /// stays visible to definedness (`ceil_term` emits `\not(K = K)`), to matching
    /// (`FailReason::DuplicateKeys`), to the hooks, and to the simplifier, which reports the map
    /// as `\bottom`. A caller that builds a map from bindings that may repeat a key with intent
    /// to overwrite (`MAP.updateAll`) resolves the repeats itself.
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
        if !entries.windows(2).all(|pair| pair[0] <= pair[1]) {
            entries.sort();
        }
        if entries.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        Self::new(TermKind::Map {
            definition,
            entries,
            rest,
        })
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
        Self::new(TermKind::List {
            definition,
            heads,
            rest,
        })
    }

    /// The set holding `elements` and the elements of `rest`, sorted.
    ///
    /// Set concatenation is nilpotent: `SetItem(X) SetItem(X)` is `\bottom`, not `SetItem(X)`;
    /// the union is `|Set`. So this constructor keeps an element that occurs twice, as
    /// `Term::map` keeps a repeated key, and the repeat stays visible to definedness
    /// (`ceil_term` emits `\not(X = X)` for it), to matching (`FailReason::DuplicateKeys`) and
    /// to the hooks (a hooked application with such an argument is `\bottom`), and to the
    /// simplifier, which reports the set as `\bottom` where it is built. A caller that
    /// builds a set from a collection that may repeat an element (`SET.list2set`) removes the
    /// repeats itself.
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
        if elements.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        Self::new(TermKind::Set {
            definition,
            elements,
            rest,
        })
    }

    /// The least element this internal set holds twice, if any. Such a set is `\bottom`
    /// (`Term::set`); the elements are sorted, so a repeat is adjacent.
    pub(crate) fn repeated_set_element(&self) -> Option<&Self> {
        let TermKind::Set { elements, .. } = self.kind() else {
            return None;
        };
        elements
            .windows(2)
            .find(|pair| pair[0] == pair[1])
            .map(|pair| &pair[0])
    }

    /// The least key this internal map binds twice, with the same or a different value, if
    /// any. Such a map is `\bottom` (`Term::map`); the entries are sorted, so a repeat is
    /// adjacent.
    pub(crate) fn repeated_map_key(&self) -> Option<&Self> {
        let TermKind::Map { entries, .. } = self.kind() else {
            return None;
        };
        entries
            .windows(2)
            .find(|pair| pair[0].0 == pair[1].0)
            .map(|pair| &pair[0].0)
    }

    /// The least element (set) or key (map) this internal collection holds twice, if any: the
    /// syntactic repeat that makes it `\bottom` (`Term::set`, `Term::map`).
    pub(crate) fn repeated_collection_key(&self) -> Option<&Self> {
        self.repeated_set_element()
            .or_else(|| self.repeated_map_key())
    }

    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }

    pub fn attributes(&self) -> &TermAttributes {
        &self.0.attributes
    }

    /// Return this term with the simplifier's fixed-point cache set.
    ///
    /// Construction deliberately leaves equation-headed applications unevaluated. The only
    /// caller is `simplify::simplify_root`, and the bit it sets on an application carries this
    /// invariant: the application is ground, its arguments carry the bit, and no equation of the
    /// definition applies to it, on any path. The [`head::NormalFormCertificate`] it must pass
    /// states the last part. It is built from complete equation selection
    /// (`BackendDefinition::equation_selection_complete`) and from the function and
    /// simplification scans (`simplify::scan::scan_term_theory`), each of which ended
    /// `NotApplicable`: every equation selection offers the head, or a bare variable, was
    /// tried, and each attempt was one of:
    ///
    /// - a failed equation match (`MatchResult::refutation`); or
    /// - a collection match that has no solution (`CollectionMatches::NoSolution`).
    ///
    /// Both are failed matches of the left-hand side against a ground term. They read no path
    /// condition, and a ground term is its only instance, so the equation applies to no instance.
    /// An attempt that would weaken this carries no failed match, so it cannot be
    /// `NotApplicable` in a term-theory scan, and it withholds the certificate:
    ///
    /// - an undecided `requires` blocks the scan;
    /// - a `requires` refuted under the path condition is context dependent;
    /// - an equation that matched but that the evaluator does not use is `Unused`. That covers a
    ///   `concrete` or `symbolic` rejection, a binding outside the left-hand side, and a
    ///   predicate right-hand side. The equation still holds, so the term may equal its
    ///   right-hand side.
    ///
    /// Equations the selection does not offer fail to match the application, with two
    /// exceptions: a simplification axiom whose left-hand side is an `\and` of term patterns
    /// (filed in the predicate theory, so the term simplifier never tries it), and a term-theory
    /// entry indexed `TermIndex::And`. A definition holding either gives no `SelectionComplete`
    /// and so no certificate. So "no offered equation matched" means "no equation of the
    /// definition matched". A budget stop or an unsupported hook leaves a child or the root
    /// unmarked. Structural distinctness reads the bit as "normal form".
    ///
    /// The structural conditions (the term is a ground application of an equation head or an
    /// overloaded symbol whose arguments carry the bit) are the caller's
    /// (`simplify::cacheable_equation_head`) and are checked here in debug builds. Under
    /// `check-normal-forms` the term is checked against every term equation of the definition
    /// (`term::head::check`), which panics when one surely matches it at its root.
    pub(crate) fn with_evaluated_cache(
        &self,
        definition: &crate::definition::BackendDefinition,
        _certificate: head::NormalFormCertificate,
    ) -> Self {
        #[cfg(feature = "check-normal-forms")]
        head::check::assert_no_equation_matches(
            definition,
            self,
            head::check::Claim::EvaluatedMark,
        );
        debug_assert!(
            self.attributes().variables.is_empty(),
            "the evaluated mark is certified only on a ground term"
        );
        debug_assert!(
            matches!(
                self.kind(),
                TermKind::Application { symbol, arguments, .. }
                    if (symbol.attributes.head_role() == HeadRole::EquationHead
                        || definition.overloads.is_overloaded(&symbol.name))
                        && arguments.iter().all(|argument| argument.attributes().evaluated)
            ),
            "the evaluated mark is certified only on an equation-head or overloaded application \
             whose arguments carry the mark"
        );
        self.marked_evaluated()
    }

    /// Return this term with the `evaluated` bit set, without the simplifier's certificate: a
    /// unit-test fixture, including marks the simplifier never sets, for the mark's readers.
    #[cfg(test)]
    pub(crate) fn with_evaluated_mark_for_test(&self) -> Self {
        self.marked_evaluated()
    }

    fn marked_evaluated(&self) -> Self {
        if self.attributes().evaluated {
            return self.clone();
        }
        Self::allocate(TermAllocation::Marked(self))
    }

    /// Whether two handles share the same immutable term allocation.
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    #[cfg(feature = "measure")]
    pub fn allocation_identity(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
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

    /// Whether two ground terms are structurally distinct: `true` is a proof that they denote
    /// different values, for any ground terms, however they were built.
    ///
    /// Only heads whose application is known to be a normal form decide: a domain value, a
    /// free-constructor application ([`HeadRole::FreeConstructor`]: its declaration admits no
    /// equation that identifies its applications), a sort injection, and
    /// an application of an `anywhere` production that the simplifier certified as a normal form
    /// by setting its `evaluated` bit ([`Self::with_evaluated_cache`]: every equation that may
    /// apply to it was scanned and found inapplicable independently of the path condition, and
    /// its arguments are certified too). Distinct normal forms are distinct values, so two
    /// such heads that differ refute the equality, and equal heads of a free symbol refute it
    /// when some pair of arguments is distinct. The argument does not depend on the `injective`
    /// attribute.
    ///
    /// An `anywhere` application without the certificate decides nothing, even when it is
    /// ground: [`Self::concrete_after_normalization`] is a shape, not evidence that no equation
    /// applies, and an anywhere equation `wrap(s(z)) = wrap(z)` makes the ground `wrap(s(z))`
    /// equal to `wrap(z)` and possibly to a term with another head. Terms containing ordinary
    /// function applications, variables, or collections are never decided here, nor are
    /// applications of a macro or alias, whose value is an expansion the definition does not
    /// describe.
    ///
    /// Two injections from different source sorts decide nothing here; see
    /// [`Self::structurally_distinct_with`] for a caller that can compare the sorts.
    pub fn structurally_distinct_after_normalization(&self, other: &Self) -> bool {
        self.structurally_distinct_with(other, &|_, _| InjectionComparison::Undecided)
            .is_some()
    }

    /// R-ground: restrict symbolic apartness to two concrete terms before minting [`head::Distinct`].
    /// Every subterm of a concrete term is concrete, so this preserves the ground decider's answers.
    #[must_use]
    pub(crate) fn structurally_distinct_with(
        &self,
        other: &Self,
        injections: &dyn Fn(&Self, &Self) -> InjectionComparison,
    ) -> Option<head::Distinct> {
        if !self.concrete_after_normalization() || !other.concrete_after_normalization() {
            return None;
        }
        self.apart_with(other, injections)
            .map(head::Distinct::of_concrete)
    }

    /// A: no value of one term is a value of the other on any valuation.
    /// Only fixed roots classified with [`head::CertifiedOnly`] decide: different application roots accepted by `distinct_roots_decide`, different domain values, separated injection sorts, or an apart argument pair of one free symbol.
    /// Variables, functions, conjunctions, residual macros and uncertified equation heads decide nothing at their position; another argument pair may still decide.
    /// Collections are not separated by this comparison table.
    /// Symbolic equation heads have no certificate, because [`Self::with_evaluated_cache`] requires groundness.
    /// The injection callback receives two injections and may separate their denotations or supply operands whose equality is equivalent to theirs.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(crate) fn apart_with(
        &self,
        other: &Self,
        injections: &dyn Fn(&Self, &Self) -> InjectionComparison,
    ) -> Option<head::Apart> {
        if self == other {
            return None;
        }
        let fixed = |term| match head::classify_value(term, &mut head::CertifiedOnly) {
            head::Head::Fixed(fixed) => Some(fixed),
            // A variable, a conjunction, a function, an equation head without the certificate,
            // or a macro or alias: its value's root is not the term's.
            head::Head::Open(_) | head::Head::Residual => None,
        };
        let left = fixed(self)?;
        let right = fixed(other)?;
        match head::compare_roots(left, right) {
            head::RootComparison::Distinct(witness) => {
                distinct_roots_decide(left.root(), right.root())
                    .then(|| head::Apart::of_roots(witness))
            }
            head::RootComparison::SameApplication(same) => same
                .pairs()
                .find_map(|(left, right)| left.apart_with(right, injections))
                .map(|argument| head::Apart::through_argument(same, argument)),
            // Applications of one symbol with different arities are ill-formed.
            head::RootComparison::ArityMismatch => None,
            head::RootComparison::DomainValues => head::Apart::of_domain_values(left, right),
            head::RootComparison::Injections => {
                let (
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
                ) = (self.kind(), other.kind())
                else {
                    unreachable!("two injection roots are injections");
                };
                if left_source == right_source && left_target == right_target {
                    // One injection is injective, so disjoint operands have disjoint images.
                    return left.apart_with(right, injections);
                }
                let comparison = injections(self, other);
                match &comparison {
                    InjectionComparison::Distinct => head::Apart::of_injection_sorts(&comparison),
                    // The injections are equal exactly when these terms are, so a witness for
                    // the terms is one for the injections.
                    InjectionComparison::Compare(left, right) => left.apart_with(right, injections),
                    InjectionComparison::Undecided => None,
                }
            }
            head::RootComparison::Collections(_) => None,
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

    fn new(kind: TermKind) -> Self {
        Self::allocate(TermAllocation::Structural(kind))
    }

    #[deny(clippy::wildcard_enum_match_arm)]
    fn allocate(allocation: TermAllocation<'_>) -> Self {
        let (kind, attributes) = match allocation {
            TermAllocation::Structural(kind) => {
                let (mut attributes, _) = synthesize_attributes(&kind);
                set_kind_attributes(&kind, &mut attributes);
                #[cfg(debug_assertions)]
                validate_attributes(&kind, &attributes, EvaluatedCache::Structural);
                (kind, attributes)
            }
            TermAllocation::Marked(source) => {
                let kind = source.kind().clone();
                let attributes = marked_attributes(source, &kind);
                #[cfg(debug_assertions)]
                validate_attributes(&kind, &attributes, EvaluatedCache::Marked);
                (kind, attributes)
            }
        };
        measure::bump(Counter::TermConstructed);
        Self(Arc::new(TermData { attributes, kind }))
    }
}

/// Every attribute other than shape is a function of the kind alone: it reads the kind and the
/// immediate children's stored attributes.
fn set_kind_attributes(kind: &TermKind, attributes: &mut TermAttributes) {
    attributes.ceil_free = ceil_free(kind);
    attributes.has_macro_or_alias = has_macro_or_alias(kind);
    attributes.k_cells = k_cells(kind);
    attributes.hash = calculate_hash(kind);
}

/// The attributes of `source`'s kind (a copy of `kind`) with the evaluated cache set.
///
/// A source reaching this point was allocated from the identical kind, either structurally or
/// by an earlier mark, which changes only `evaluated`; so its stored attributes other than
/// `evaluated` are the structural ones of `kind`. An application is never a collection-collision
/// root (only a map or set is), and its inherited exclusions are already in those attributes,
/// so it keeps them and only gains the mark. Other kinds resynthesize their shape, and a
/// collision root keeps `evaluated` false whatever the mark.
fn marked_attributes(source: &Term, kind: &TermKind) -> TermAttributes {
    if matches!(kind, TermKind::Application { .. }) {
        let mut attributes = source.attributes().clone();
        #[cfg(debug_assertions)]
        {
            let (mut structural, collision_root) = synthesize_attributes(kind);
            set_kind_attributes(kind, &mut structural);
            assert!(!collision_root);
            assert_eq!(
                attributes, structural,
                "a marked source carries its kind's attributes"
            );
        }
        attributes.evaluated = true;
        attributes
    } else {
        let (mut attributes, collision_root) = synthesize_attributes(kind);
        attributes.evaluated = !collision_root;
        set_kind_attributes(kind, &mut attributes);
        attributes
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
///   disequality for each pair of keys (elements) that `elements_are_apart`
///   does not separate.
///
/// For the pairs, the attribute accepts only keys that share one `KeyHeader`: all domain values,
/// or all `inj{S, T}` of a domain value for one `S` and `T`. Two distinct such keys are separated
/// by `structurally_distinct_after_normalization` alone, so the matcher that
/// `elements_are_apart` falls back on is never needed. Keys with different
/// headers, such as `inj{Int, KItem}(1)` and `inj{String, KItem}("a")`, may need the sort graph's injection comparison, which the attribute does not consult.
/// The attribute is false for them. Distinctness of the keys themselves comes from the sorted
/// order the constructors keep and a check here: `Term::set` sorts its elements and keeps a
/// repeated one (concatenation is nilpotent, so the repeat makes the set `\bottom`); `Term::map`
/// sorts its entries by `(key, value)` and keeps a repeated key, with the same value or not
/// (the map is `\bottom` then too). Repeats are adjacent in both, and the attribute checks that
/// adjacent elements (keys) differ.
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
            rest.is_none()
                && elements.iter().all(free)
                && share_one_key_header(elements.iter())
                && elements.windows(2).all(|pair| pair[0] != pair[1])
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

/// Whether [`Term::apart_with`] decides two fixed roots that differ: two
/// applications, or an application and an injection, whose values have different roots. A
/// domain value against another root, and every collection, stay undecided there.
#[deny(clippy::wildcard_enum_match_arm)]
fn distinct_roots_decide(left: head::FixedRoot, right: head::FixedRoot) -> bool {
    /// `Some(true)` for an application, `Some(false)` for an injection, `None` otherwise.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn application(root: head::FixedRoot) -> Option<bool> {
        match root {
            head::FixedRoot::FreeConstructor | head::FixedRoot::EquationHead(_) => Some(true),
            head::FixedRoot::Injection => Some(false),
            head::FixedRoot::DomainValue | head::FixedRoot::Collection(_) => None,
        }
    }
    match (application(left), application(right)) {
        (Some(left), Some(right)) => left || right,
        (None, _) | (_, None) => false,
    }
}

/// How two injections with different source sorts into one position compare; see
/// [`Term::apart_with`].
pub(crate) enum InjectionComparison {
    /// No value of one injection is a value of the other.
    Distinct,
    /// The injections are equal exactly when these two terms are.
    Compare(Term, Term),
    /// Nothing is known.
    Undecided,
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
    let mut shape = ChildShape::new();
    for term in terms {
        shape.add(term);
    }
    shape.0
}

/// The conjunctive shape of a node's immediate children, accumulated once per child.
struct ChildShape(TermAttributes);

impl ChildShape {
    /// The flags are conjunctions over child terms. Their identity is true, which is essential
    /// for nullary constructors and empty builtin collections to be recognized as concrete
    /// constructor-like values.
    fn new() -> Self {
        Self(TermAttributes {
            constructor_like: true,
            concrete_after_normalization: true,
            ..TermAttributes::default()
        })
    }

    #[inline]
    fn add(&mut self, child: &Term) {
        let attributes = child.attributes();
        if !attributes.variables.is_empty() {
            if self.0.variables.is_empty() {
                self.0.variables.clone_from(&attributes.variables);
            } else {
                self.0
                    .variables
                    .extend(attributes.variables.iter().cloned());
            }
        }
        self.0.evaluated &= attributes.evaluated;
        self.0.constructor_like &= attributes.constructor_like;
        self.0.concrete_after_normalization &= attributes.concrete_after_normalization;
        self.0.can_be_evaluated &= attributes.can_be_evaluated;
    }
}

#[cfg(debug_assertions)]
#[derive(Clone, Copy)]
enum EvaluatedCache {
    Structural,
    Marked,
}

/// Ordinary construction supplies only a kind. Cache reconstruction supplies an immutable
/// source, never caller-selected attributes or a kind that could disagree with that source.
enum TermAllocation<'a> {
    Structural(TermKind),
    Marked(&'a Term),
}

/// Derive shape from the completed kind. Strict children contribute conjunctively; a local
/// disjoint-collection collision excludes every value shape and requires root simplification.
/// The second result records that root outcome so a cache mark cannot override it.
#[deny(clippy::wildcard_enum_match_arm)]
fn synthesize_attributes(kind: &TermKind) -> (TermAttributes, bool) {
    let mut collision_root = false;
    let mut attributes = match kind {
        TermKind::And(left, right) => {
            let mut attributes = combine_attributes([left, right]);
            attributes.constructor_like = false;
            attributes.concrete_after_normalization = false;
            attributes
        }
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let mut attributes = combine_attributes(arguments.iter());
            // Only a free constructor root supplies a structural normal form and freeness.
            let role = symbol.attributes.head_role();
            let free = role == HeadRole::FreeConstructor;
            attributes.evaluated &= free;
            attributes.constructor_like &= free;
            // Concreteness describes a possible normalized shape, not a definedness claim.
            attributes.concrete_after_normalization &= (symbol.attributes.symbol_type
                == SymbolType::Constructor
                || (symbol.attributes.anywhere && !symbol.attributes.declared_function))
                && role != HeadRole::Uninterpreted;
            attributes.can_be_evaluated &= symbol.attributes.has_evaluators;
            attributes
        }
        TermKind::DomainValue { .. } => TermAttributes {
            constructor_like: true,
            concrete_after_normalization: true,
            ..TermAttributes::default()
        },
        TermKind::Variable(variable) => TermAttributes {
            variables: BTreeSet::from([variable.clone()]),
            ..TermAttributes::default()
        },
        TermKind::Injection { term, .. } => term.attributes().clone(),
        TermKind::Map { entries, rest, .. } => {
            // Entries are sorted by key, so a repeated key follows its first binding; the
            // collision test shares the single pass over the children.
            let mut shape = ChildShape::new();
            let mut previous_key = None;
            for (key, value) in entries {
                collision_root |= previous_key == Some(key);
                previous_key = Some(key);
                shape.add(key);
                shape.add(value);
            }
            if let Some(rest) = rest {
                shape.add(rest);
            }
            shape.0
        }
        TermKind::List { heads, rest, .. } => combine_attributes(
            heads.iter().chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            ),
        ),
        TermKind::Set { elements, rest, .. } => {
            // Elements are sorted, so a repeated element follows its first occurrence.
            let mut shape = ChildShape::new();
            let mut previous = None;
            for element in elements {
                collision_root |= previous == Some(element);
                previous = Some(element);
                shape.add(element);
            }
            if let Some(rest) = rest {
                shape.add(rest);
            }
            shape.0
        }
    };
    if collision_root {
        attributes.evaluated = false;
        attributes.constructor_like = false;
        attributes.concrete_after_normalization = false;
    }
    (attributes, collision_root)
}

/// Immediate children already passed allocation validation. Local checks therefore establish
/// the hereditary exclusion without walking descendants or consulting semantic definedness.
#[cfg(debug_assertions)]
#[deny(clippy::wildcard_enum_match_arm)]
fn validate_attributes(kind: &TermKind, attributes: &TermAttributes, cache: EvaluatedCache) {
    assert!(!attributes.constructor_like || attributes.concrete_after_normalization);
    assert!(!attributes.concrete_after_normalization || attributes.variables.is_empty());
    let mut child_evaluated = true;
    let mut check_child = |child: &Term| {
        assert!(!attributes.constructor_like || child.attributes().constructor_like);
        assert!(!attributes.concrete_after_normalization || child.concrete_after_normalization());
        child_evaluated &= child.attributes().evaluated;
    };
    let (root_evaluated, collision_root) = match kind {
        TermKind::And(left, right) => {
            check_child(left);
            check_child(right);
            assert!(!attributes.constructor_like && !attributes.concrete_after_normalization);
            (true, false)
        }
        TermKind::Application {
            symbol, arguments, ..
        } => {
            for child in arguments {
                check_child(child);
            }
            (
                symbol.attributes.head_role() == HeadRole::FreeConstructor,
                false,
            )
        }
        TermKind::DomainValue { .. } => (true, false),
        TermKind::Variable(_) => {
            assert!(!attributes.constructor_like && !attributes.concrete_after_normalization);
            (true, false)
        }
        TermKind::Injection { term, .. } => {
            check_child(term);
            (true, false)
        }
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                check_child(key);
                check_child(value);
            }
            if let Some(child) = rest {
                check_child(child);
            }
            let collision = entries.windows(2).any(|pair| pair[0].0 == pair[1].0);
            (!collision, collision)
        }
        TermKind::List { heads, rest, .. } => {
            for child in heads {
                check_child(child);
            }
            if let Some((middle, tails)) = rest {
                check_child(middle);
                for child in tails {
                    check_child(child);
                }
            }
            (true, false)
        }
        TermKind::Set { elements, rest, .. } => {
            for child in elements {
                check_child(child);
            }
            if let Some(child) = rest {
                check_child(child);
            }
            let collision = elements.windows(2).any(|pair| pair[0] == pair[1]);
            (!collision, collision)
        }
    };
    if collision_root {
        assert!(
            !attributes.evaluated
                && !attributes.constructor_like
                && !attributes.concrete_after_normalization
        );
    }
    match cache {
        EvaluatedCache::Structural => {
            assert_eq!(attributes.evaluated, root_evaluated && child_evaluated)
        }
        EvaluatedCache::Marked => assert_eq!(attributes.evaluated, !collision_root),
    }
}

fn calculate_hash(kind: &TermKind) -> u64 {
    let mut hasher = FxHasher::default();
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
    fn collision_roots_exclude_concrete_shape_at_creation() {
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        let set = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let map = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let symbolic = Term::variable(Variable::new("K", sort()));
        for collision in [
            Term::set(set.clone(), vec![symbolic.clone(); 2], None),
            Term::map(map.clone(), vec![(symbolic, one.clone()); 2], None),
            Term::set(set, vec![one.clone(), one.clone()], None),
            Term::map(map.clone(), vec![(one.clone(), one.clone()); 2], None),
            Term::map(
                map,
                vec![
                    (one.clone(), one),
                    (two.clone(), two.clone()),
                    (two.clone(), Term::domain_value(sort(), "3")),
                ],
                None,
            ),
        ] {
            assert!(!collision.attributes().evaluated);
            assert!(!collision.attributes().constructor_like);
            assert!(
                !collision.concrete_after_normalization(),
                "collision retains a positive shape: {collision:?}"
            );
        }
    }

    fn assert_collision_shape(term: &Term) {
        assert!(!term.attributes().constructor_like, "{term:?}");
        assert!(!term.concrete_after_normalization(), "{term:?}");
    }

    #[test]
    fn collisions_propagate_through_every_immediate_child_position() {
        let value = Term::domain_value(sort(), "1");
        let map = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let set = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let list = Arc::new(ListDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "List".into(),
        });
        let mut anywhere = Symbol::constructor("anywhere", vec![sort()], sort());
        anywhere.attributes.anywhere = true;
        let anywhere = Arc::new(anywhere);
        let collisions = [
            Term::set(set.clone(), vec![value.clone(); 2], None),
            Term::map(map.clone(), vec![(value.clone(), value.clone()); 2], None),
        ];
        for collision in collisions {
            let contexts = [
                Term::and(collision.clone(), value.clone()),
                Term::and(value.clone(), collision.clone()),
                Term::application(constructor(), vec![], vec![collision.clone()]),
                Term::application(anywhere.clone(), vec![], vec![collision.clone()]),
                Term::injection(sort(), Sort::simple("Target"), collision.clone()),
                Term::list(list.clone(), vec![collision.clone()], None),
                Term::list(
                    list.clone(),
                    vec![value.clone()],
                    Some((collision.clone(), vec![value.clone()])),
                ),
                Term::list(
                    list.clone(),
                    vec![value.clone()],
                    Some((value.clone(), vec![collision.clone()])),
                ),
                Term::map(map.clone(), vec![(collision.clone(), value.clone())], None),
                Term::map(map.clone(), vec![(value.clone(), collision.clone())], None),
                Term::map(
                    map.clone(),
                    vec![(Term::domain_value(sort(), "2"), value.clone())],
                    Some(collision.clone()),
                ),
                Term::set(set.clone(), vec![collision.clone()], None),
                Term::set(
                    set.clone(),
                    vec![Term::domain_value(sort(), "2")],
                    Some(collision.clone()),
                ),
            ];
            assert_collision_shape(&collision);
            let marked = collision.with_evaluated_mark_for_test();
            assert!(
                !marked.attributes().evaluated,
                "a collision root overrides a cache mark"
            );
            assert_collision_shape(&marked);
            for context in contexts {
                assert_collision_shape(&context);
                assert_collision_shape(&context.with_evaluated_mark_for_test());
            }
        }
    }

    #[test]
    fn flattening_concat_substitution_and_child_replacement_create_collisions() {
        let value = Term::domain_value(sort(), "1");
        let other = Term::domain_value(sort(), "2");
        let map = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let set = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let singleton_set = Term::set(set.clone(), vec![value.clone()], None);
        let singleton_map = Term::map(map.clone(), vec![(value.clone(), value.clone())], None);
        assert_collision_shape(&Term::set(
            set.clone(),
            vec![value.clone()],
            Some(singleton_set.clone()),
        ));
        assert_collision_shape(&Term::map(
            map.clone(),
            vec![(value.clone(), other.clone())],
            Some(singleton_map.clone()),
        ));
        for (metadata, singleton) in [
            (CollectionMetadata::Map(map.clone()), singleton_map),
            (CollectionMetadata::Set(set.clone()), singleton_set),
        ] {
            let mut concat =
                Symbol::constructor("concat", vec![singleton.sort(); 2], singleton.sort());
            concat.attributes.collection = Some(metadata);
            assert_collision_shape(&Term::application(
                Arc::new(concat),
                vec![],
                vec![singleton.clone(), singleton],
            ));
        }
        let x = Variable::new("X", sort());
        let y = Variable::new("Y", sort());
        let bindings = BTreeMap::from([(x.clone(), value.clone()), (y.clone(), value.clone())]);
        for symbolic in [
            Term::set(
                set.clone(),
                vec![Term::variable(x.clone()), Term::variable(y.clone())],
                None,
            ),
            Term::map(
                map.clone(),
                vec![
                    (Term::variable(x), value.clone()),
                    (Term::variable(y), other.clone()),
                ],
                None,
            ),
        ] {
            assert_collision_shape(&crate::substitution::substitute(&symbolic, &bindings));
        }
        for distinct in [
            Term::set(set, vec![value.clone(), other.clone()], None),
            Term::map(
                map,
                vec![
                    (value.clone(), value.clone()),
                    (other.clone(), value.clone()),
                ],
                None,
            ),
        ] {
            assert!(distinct.concrete_after_normalization());
            let unchanged = distinct
                .try_map_children::<()>(|child| Ok(child.clone()))
                .unwrap();
            assert!(distinct.ptr_eq(&unchanged));
            let replaced = distinct
                .try_map_children::<()>(|child| {
                    Ok(if child == &other {
                        value.clone()
                    } else {
                        child.clone()
                    })
                })
                .unwrap();
            assert_collision_shape(&replaced);
        }
    }

    #[test]
    fn valid_collection_shapes_and_anywhere_certificates_keep_their_contracts() {
        let value = Term::domain_value(sort(), "1");
        let map = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let set = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let key = |name| {
            Term::application(
                Arc::new(Symbol::constructor(name, vec![], sort())),
                vec![],
                vec![],
            )
        };
        for keys in [
            vec![],
            vec![value.clone()],
            vec![value.clone(), Term::domain_value(sort(), "2")],
            vec![key("a"), key("b")],
        ] {
            let map = Term::map(
                map.clone(),
                keys.iter()
                    .map(|key| (key.clone(), value.clone()))
                    .collect(),
                None,
            );
            let set = Term::set(set.clone(), keys.clone(), None);
            for collection in [map, set] {
                assert!(collection.attributes().constructor_like);
                assert!(collection.concrete_after_normalization());
                assert!(collection.attributes().evaluated);
                if keys
                    .first()
                    .is_some_and(|key| matches!(key.kind(), TermKind::Application { .. }))
                {
                    assert!(
                        !collection.attributes().ceil_free(),
                        "concrete keys need not share a conservative KeyHeader"
                    );
                }
            }
        }
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[] module MAIN
            sort SomeSort{} [hasDomainValues{}()]
            symbol tag{}(SomeSort{}) : SomeSort{} [anywhere{}(), functional{}()]
        endmodule []"#,
        )
        .unwrap();
        let definition =
            crate::definition::BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let ground = Term::application(definition.symbols["tag"].clone(), vec![], vec![value]);
        assert!(ground.concrete_after_normalization());
        assert!(!ground.attributes().constructor_like);
        assert!(!ground.attributes().evaluated);
        let certified = crate::simplify::simplify(
            &definition,
            &ground,
            crate::simplify::SimplificationOptions::default(),
        )
        .unwrap()
        .unwrap()
        .term;
        assert!(certified.attributes().evaluated);
        assert!(certified.concrete_after_normalization());
        assert!(!certified.attributes().constructor_like);
        assert!(certified.ptr_eq(&certified.with_evaluated_mark_for_test()));
        let wrapped = Term::application(constructor(), vec![], vec![certified]);
        assert!(
            wrapped.attributes().evaluated,
            "a child certificate survives structural synthesis"
        );
        assert!(wrapped.concrete_after_normalization());
        assert!(!wrapped.attributes().constructor_like);
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
    fn sequential_values_and_wrappers_have_distinct_hashes() {
        let sort = Sort::builtin(BuiltinSort::Int);
        let wrapper = Arc::new(Symbol::constructor(
            "hashWrapper",
            vec![sort.clone()],
            sort.clone(),
        ));
        let mut hashes = std::collections::HashSet::new();
        for value in 0..10_000 {
            let child = Term::domain_value(sort.clone(), value.to_string());
            let wrapped = Term::application(wrapper.clone(), Vec::new(), vec![child.clone()]);
            assert!(hashes.insert(child.attributes().hash));
            assert!(hashes.insert(wrapped.attributes().hash));
        }
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
        // An identical binding is kept too: a map binds a key once, so this map is bottom.
        assert_eq!(entries.len(), 3);
        assert!(entries.windows(2).all(|pair| pair[0] <= pair[1]));
        assert_eq!(map.repeated_map_key(), Some(&one));
        assert!(!map.attributes().ceil_free());
        assert!(!map.attributes().evaluated);

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
        // A repeated element is kept: set concatenation is nilpotent, so this set is bottom.
        assert_eq!(elements, &[one.clone(), one.clone(), two]);
        assert!(!set.attributes().ceil_free());
        assert_eq!(set.repeated_collection_key(), Some(&one));
        assert!(!set.attributes().evaluated);
        assert!(!set.attributes().constructor_like);
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

    /// Builders retain raw facts; every call recomputes the role, including combinations
    /// that the loader rejects. Neither builder order nor a function flag restores freeness
    /// while an algebraic constructor's identifying axioms are present.
    #[test]
    fn algebraic_constructor_builders_cannot_restore_a_fixed_role() {
        for axioms in [
            AlgebraicAxioms::assoc(),
            AlgebraicAxioms::comm(),
            AlgebraicAxioms::idem(),
            AlgebraicAxioms::unit(),
        ] {
            for declared in [false, true] {
                for attributes in [
                    SymbolAttributes::constructor()
                        .with_declared_function(declared)
                        .with_algebraic_axioms(axioms),
                    SymbolAttributes::constructor()
                        .with_algebraic_axioms(axioms)
                        .with_declared_function(declared),
                ] {
                    assert_eq!(attributes.head_role(), HeadRole::Uninterpreted);
                    assert_eq!(
                        attributes
                            .clone()
                            .with_anywhere(true)
                            .with_injective(true)
                            .head_role(),
                        HeadRole::Uninterpreted
                    );
                    let mut symbol = Symbol::constructor("g", Vec::new(), Sort::simple("SortS"));
                    symbol.attributes = attributes.clone();
                    let term = Term::application(Arc::new(symbol), Vec::new(), Vec::new());
                    assert!(matches!(
                        head::classify_pattern(head::PatternReading::AsWritten, &term),
                        head::Head::Open(head::Open::Uninterpreted)
                    ));
                    assert!(matches!(
                        head::classify_value(&term, &mut head::NoEvidence),
                        head::Head::Open(head::Open::Uninterpreted)
                    ));
                    assert!(!term.concrete_after_normalization());
                    assert!(!term.attributes().constructor_like);
                    assert_eq!(
                        attributes
                            .with_algebraic_axioms(AlgebraicAxioms::default())
                            .head_role(),
                        HeadRole::FreeConstructor
                    );
                }
            }
        }
    }

    /// The role of each declared flag combination (`SymbolAttributes::head_role`): the
    /// `instance_normal.rs` fixture's `wrap` (`anywhere`, `functional`, `injective`) is an
    /// equation head, and the combinations on which the flags disagreed get one answer each.
    #[test]
    fn head_role_decides_each_declared_combination() {
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol wrap{}(SortNat{}) : SortNat{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol anywhereConstructor{}(SortNat{}) : SortNat{}
                    [constructor{}(), anywhere{}(), functional{}(), injective{}()]
                symbol constructorMacro{}(SortNat{}) : SortNat{}
                    [constructor{}(), functional{}(), injective{}(), macro{}()]
                symbol functionalMacro{}(SortNat{}) : SortNat{}
                    [functional{}(), injective{}(), macro{}()]
                symbol anywhereAlias{}(SortNat{}) : SortNat{}
                    [anywhere{}(), functional{}(), alias'Kywd'{}()]
                symbol anywhereFunction{}(SortNat{}) : SortNat{}
                    [anywhere{}(), function{}(), total{}(), injective{}()]
                symbol injectiveFunction{}(SortNat{}) : SortNat{}
                    [function{}(), total{}(), injective{}()]
                symbol injectiveFunctional{}(SortNat{}) : SortNat{}
                    [functional{}(), injective{}()]
                symbol functionalOnly{}(SortNat{}) : SortNat{} [functional{}()]
                symbol algebraic{}(SortNat{}) : SortNat{} [functional{}(), assoc{}()]
                symbol algebraicFunction{}(SortNat{}) : SortNat{}
                    [function{}(), total{}(), injective{}(), comm{}()]
            endmodule []"#,
        )
        .expect("role definition should parse");
        let definition = crate::definition::BackendDefinition::internalize(&syntax, "MAIN")
            .expect("role definition should internalize");
        let role = |name: &str| definition.symbols[name].attributes.head_role();

        assert_eq!(role("functionalOnly"), HeadRole::Uninterpreted);
        assert_eq!(role("algebraic"), HeadRole::Uninterpreted);
        assert_eq!(
            role("algebraicFunction"),
            HeadRole::Function {
                declared: true,
                injective: false,
                refutable_arguments: false
            }
        );
        assert_eq!(role("z"), HeadRole::FreeConstructor);
        assert_eq!(role("wrap"), HeadRole::EquationHead);
        // B1: `anywhere` equations identify applications, whatever the `constructor` attribute.
        assert_eq!(role("anywhereConstructor"), HeadRole::EquationHead);
        // B2: a macro or alias is residual, whatever its type and its `anywhere` attribute.
        assert_eq!(role("constructorMacro"), HeadRole::Residual);
        assert_eq!(role("functionalMacro"), HeadRole::Residual);
        assert_eq!(role("anywhereAlias"), HeadRole::Residual);
        // B3: `injective` counts only for a function without `anywhere`.
        assert_eq!(
            role("anywhereFunction"),
            HeadRole::Function {
                declared: true,
                injective: false,
                refutable_arguments: true
            }
        );
        assert_eq!(
            role("injectiveFunction"),
            HeadRole::Function {
                declared: true,
                injective: true,
                refutable_arguments: true
            }
        );
        assert_eq!(
            role("injectiveFunctional"),
            HeadRole::Function {
                declared: false,
                injective: true,
                refutable_arguments: true
            }
        );
    }
}
