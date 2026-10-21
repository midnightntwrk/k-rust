//! Definition-independent signature facts shared by both observation sides.

use std::collections::BTreeMap;

use k_rust::backend::{Backend, BackendError};
use k_rust_backend::definition::{BackendDefinition, SortInfo};
use k_rust_backend::matching::SortGraph;
use k_rust_backend::term::{Name, Sort, Symbol};

use crate::feasibility::free_constructor;

/// The part of a symbol declaration shared observation decisions rely on: its sorts, whether it is a
/// free constructor, and its hook.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolShape {
    /// The symbol's sort parameters.
    pub sort_variables: Vec<Name>,
    /// The argument sorts.
    pub argument_sorts: Vec<Sort>,
    /// The result sort.
    pub result_sort: Sort,
    /// Whether the symbol is a constructor of K's free term algebra
    /// (`feasibility::free_constructor`).
    pub free: bool,
    /// The builtin hook, whose meaning does not depend on the definition.
    pub hook: Option<Name>,
}

/// The constructor, sort, subsort and hook structure of a definition: what observation classification and
/// shared relations assume means the same on both sides.
///
/// The full symbol table is not compared: withdrawing claims strips `total`, `functional`,
/// `injective`, `smt-hook` and `smtlib` from productions, so the tables of a withdrawn side
/// differ from the baseline's without any change to this projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignatureProjection {
    /// The declared sorts.
    pub sorts: BTreeMap<Name, SortInfo>,
    /// The subsort closure, which gives injections their meaning.
    pub sort_graph: SortGraph,
    /// The shape of every symbol, by name.
    pub symbols: BTreeMap<Name, SymbolShape>,
}

impl SignatureProjection {
    fn of(definition: &BackendDefinition) -> Self {
        Self {
            sorts: definition.sorts().clone(),
            sort_graph: definition.sort_graph().clone(),
            symbols: definition
                .symbols()
                .iter()
                .map(|(name, symbol)| (name.clone(), SymbolShape::of(symbol)))
                .collect(),
        }
    }
}

impl SymbolShape {
    fn of(symbol: &Symbol) -> Self {
        Self {
            sort_variables: symbol.sort_variables.clone(),
            argument_sorts: symbol.argument_sorts.clone(),
            result_sort: symbol.result_sort.clone(),
            free: free_constructor(symbol),
            hook: symbol.attributes.hook.clone(),
        }
    }
}

/// What observation evaluation needs to know about one side's definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionFacts {
    /// The signature projection compared between the sides.
    pub signature: SignatureProjection,
}

/// The facts of the default module of `backend`. Backend errors propagate to the caller.
pub fn definition_facts(backend: &mut Backend) -> Result<DefinitionFacts, BackendError> {
    backend.with_solver(None, |definition, _| {
        Ok(DefinitionFacts {
            signature: SignatureProjection::of(definition),
        })
    })
}
