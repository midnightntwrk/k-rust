//! What the reference models do with an application of each symbol: the one statement every rule
//! of the check reads when it asks whether an application may be a normal form, whether it is
//! defined in every model, or which elements it can hold (the unit design's "Revision after
//! review 1", R1.2).
//!
//! Two facts are primary for a symbol `h : S1 ... Sn -> S`:
//!
//! - what the innermost relation `->E` does with a *stuck* application (one no hook or equation
//!   rewrites): only a declared partial function's is `\bottom` (rule 3); every other stuck
//!   application is a normal form;
//! - how the model `M'` of the closure's construction (`closure.rs`) interprets an application
//!   whose arguments hold a *new* element (a normal form containing an untainted equation-head
//!   application) and that no untainted equation rewrites: formally (the application is itself
//!   a new element of `S` that contains its arguments), as `\bottom`, as one fixed *old* element
//!   of `S`, by its hook, or not at all (a *pin*).
//!
//! Everything else is derived from those two: which sorts have a normal form (vacuous overlaps),
//! which sorts have an element in every model (where `M'` may collapse), which applications are
//! never normal forms (vacuous join cases), and which sorts' elements can hold which equation
//! heads (the closure's T-obs).

use rustc_hash::FxHashSet;

use crate::{
    definition::BackendDefinition,
    matching::ClosedSort,
    term::{FunctionType, HeadRole, Sort, Symbol, SymbolType},
};

/// The class of a symbol other than the sort injection (R1.2).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Class {
    /// A free constructor.
    Constructor,
    /// A collection symbol: element, concatenation or unit.
    Collection,
    /// An equation head.
    EquationHead,
    /// A hooked symbol that is not a collection symbol; `total` when declared total.
    Hooked { total: bool },
    /// A declared partial function without a hook.
    PartialFunction,
    /// Any other total symbol: a declared total function, a `functional` uninterpreted symbol, a
    /// total `injective` symbol that is not a declared function, a total residual. `collapsible`
    /// when it is not injective, has no algebraic axiom and is not a residual: then nothing but
    /// its totality constrains its value on new arguments.
    Total { collapsible: bool },
    /// Any other partial symbol: a partial uninterpreted or residual symbol, a partial
    /// `injective` symbol that is not a declared function.
    OtherPartial,
}

impl Class {
    pub(crate) fn of(symbol: &Symbol) -> Self {
        let attributes = &symbol.attributes;
        if attributes.collection.is_some() {
            return Self::Collection;
        }
        let role = attributes.head_role();
        let total = attributes.symbol_type != SymbolType::Function(FunctionType::Partial);
        match role {
            HeadRole::FreeConstructor => return Self::Constructor,
            HeadRole::EquationHead => return Self::EquationHead,
            HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {}
        }
        if attributes.hook.is_some() {
            return Self::Hooked { total };
        }
        match role {
            HeadRole::FreeConstructor | HeadRole::EquationHead => unreachable!("decided above"),
            HeadRole::Function { declared: true, .. } if !total => Self::PartialFunction,
            HeadRole::Function { injective, .. } if total => Self::Total {
                collapsible: !injective && attributes.algebraic_axioms().is_empty(),
            },
            HeadRole::Uninterpreted if total => Self::Total {
                collapsible: attributes.algebraic_axioms().is_empty(),
            },
            HeadRole::Residual if total => Self::Total { collapsible: false },
            HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {
                Self::OtherPartial
            }
        }
    }

    /// Whether `->E` makes a stuck application `\bottom` (rule 3): only a declared partial
    /// function's, hooked or not. Every other stuck application is a normal form.
    pub(crate) fn stuck_is_bottom(self) -> bool {
        matches!(self, Self::PartialFunction | Self::Hooked { total: false })
    }

    /// Whether an application of normal forms is never a normal form: it is rewritten, or it is
    /// `\bottom` (rule 1 for a hook, rule 3 for a function).
    pub(crate) fn never_normal(self) -> bool {
        self.stuck_is_bottom()
    }

    /// Whether every application of this symbol to elements is an element in every model of the
    /// definition: a constructor, a collection unit or element, and every symbol declared total
    /// or `functional`, by its functional axiom (precondition P2). An equation head counts only
    /// when declared total: its definedness is otherwise exactly the claim under test.
    fn builds_defined(self, symbol: &Symbol) -> bool {
        match self {
            Self::Constructor => true,
            Self::Collection | Self::EquationHead | Self::Hooked { .. } | Self::Total { .. } => {
                symbol.attributes.symbol_type != SymbolType::Function(FunctionType::Partial)
            }
            Self::PartialFunction | Self::OtherPartial => false,
        }
    }
}

/// How `M'` interprets an application whose arguments hold a new element and that no untainted
/// equation rewrites (R1.2, third column).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OnNewArguments {
    /// The application itself, a new element of its sort that contains its arguments: the sort's
    /// elements can hold the argument sorts' equation heads.
    Formal,
    /// `\bottom`, one fixed old element of the sort, a literal, or the hook's builtin meaning:
    /// nothing new is held.
    Opaque,
    /// No interpretation exists in general: a total injective (or algebraic) symbol into a
    /// hooked sort, which must map each new element to a fresh literal. The equation heads
    /// its argument sorts can hold get no claim (R1.4).
    Pinned,
}

/// The sort sets the table's columns are read with.
pub(crate) struct Sorts {
    /// Sorts with a normal form: an over-approximation (a sort outside it has no normal form).
    normal_form: FxHashSet<Sort>,
    /// Sorts with an element in every model: an under-approximation.
    surely_inhabited: FxHashSet<Sort>,
}

impl Sorts {
    pub(crate) fn of(definition: &BackendDefinition) -> Self {
        let symbols = definition
            .symbols()
            .values()
            .map(|symbol| &**symbol)
            .filter(|symbol| !symbol.is(k_rust_kore::names::WellKnownSymbol::Inj))
            .collect::<Vec<&Symbol>>();
        let normal_form = least_sorts(
            definition,
            true,
            !super::switches::active().drop_supersort_inhabitation,
            symbols
                .iter()
                .filter(|symbol| !Class::of(symbol).stuck_is_bottom()),
        );
        let surely_inhabited = least_sorts(
            definition,
            false,
            true,
            symbols
                .iter()
                .filter(|symbol| Class::of(symbol).builds_defined(symbol)),
        );
        Self {
            normal_form,
            surely_inhabited,
        }
    }

    /// Whether `sort` may have a normal form. A sort with a parameter, an instance of a parametric
    /// symbol, and a sort the order does not know are counted as having one.
    pub(crate) fn has_normal_form(&self, sort: &Sort) -> bool {
        self.normal_form.contains(sort)
    }

    /// Whether `sort` has an element in every model of the definition.
    pub(crate) fn surely_inhabited(&self, sort: &Sort) -> bool {
        self.surely_inhabited.contains(sort)
    }

    /// R1.2's third column for `symbol`.
    pub(crate) fn on_new_arguments(
        &self,
        definition: &BackendDefinition,
        symbol: &Symbol,
    ) -> OnNewArguments {
        let builtin = fixed_carrier(definition, &symbol.result_sort);
        match Class::of(symbol) {
            Class::Constructor | Class::EquationHead => OnNewArguments::Formal,
            // A collection's element edges are the collection sort's (`SortReach`); its symbols
            // build the collection value, which holds its elements opaquely otherwise.
            Class::Collection | Class::Hooked { .. } | Class::PartialFunction => {
                OnNewArguments::Opaque
            }
            Class::Total { collapsible } => {
                if collapsible && self.surely_inhabited(&symbol.result_sort) {
                    OnNewArguments::Opaque
                } else if builtin {
                    OnNewArguments::Pinned
                } else {
                    OnNewArguments::Formal
                }
            }
            Class::OtherPartial if builtin => OnNewArguments::Opaque,
            Class::OtherPartial => OnNewArguments::Formal,
        }
    }
}

/// The least set of sorts closed under: a sort with a hook or domain values, a collection sort,
/// the result sort of a symbol of `builders` whose argument sorts are in the set, and a supersort
/// of a sort in the set (when `supersorts`; always outside a test switch). With
/// `parameters_count`, a sort with parameters is in the set, and an open sort (one with a sort
/// variable) counts as in it; otherwise neither is.
fn least_sorts<'s>(
    definition: &BackendDefinition,
    parameters_count: bool,
    supersorts: bool,
    builders: impl Iterator<Item = &'s &'s Symbol>,
) -> FxHashSet<Sort> {
    let mut set = definition
        .sorts()
        .iter()
        .filter(|(_, info)| {
            (parameters_count && !info.parameters.is_empty())
                || info.hook.is_some()
                || info.has_domain_values
        })
        .map(|(name, _)| Sort::simple(name.clone()))
        .collect::<FxHashSet<_>>();
    for symbol in definition.symbols().values() {
        if let Some(collection) = &symbol.attributes.collection {
            let sort = match collection {
                crate::term::CollectionMetadata::Map(map) => map.map_sort.clone(),
                crate::term::CollectionMetadata::List(list)
                | crate::term::CollectionMetadata::Set(list) => list.list_sort.clone(),
            };
            set.insert(Sort::simple(sort));
        }
    }
    let builders = builders.collect::<Vec<_>>();
    let open = |sort: &Sort| ClosedSort::new(sort.clone()).is_err();
    loop {
        let before = set.len();
        for symbol in &builders {
            if open(&symbol.result_sort) || set.contains(&symbol.result_sort) {
                continue;
            }
            if symbol
                .argument_sorts
                .iter()
                .all(|argument| (parameters_count && open(argument)) || set.contains(argument))
            {
                set.insert(symbol.result_sort.clone());
            }
        }
        if supersorts {
            for (supersort, below) in definition.sort_graph().closures() {
                if !set.contains(supersort.sort())
                    && below.iter().any(|sort| set.contains(sort.sort()))
                {
                    set.insert(supersort.sort().clone());
                }
            }
        }
        if set.len() == before {
            return set;
        }
    }
}

/// Whether `sort` is a fixed carrier: declared with a hook, so that its elements are the
/// builtin's values in every model, and no formal term can be added to it. A sort with domain
/// values but no hook is not one: its domain values are some of its elements, and applications
/// of its constructors and equation heads are others.
pub(crate) fn fixed_carrier(definition: &BackendDefinition, sort: &Sort) -> bool {
    match sort {
        Sort::Application { name, .. } => definition
            .sorts()
            .get(name)
            .is_some_and(|info| info.hook.is_some()),
        Sort::Variable(_) => false,
    }
}
