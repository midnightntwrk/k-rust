//! The declarations the emitted definition states about its sorts, read from the frontend's
//! definition before it is emitted, in the KORE sorts the backend reads.
//!
//! A hooked application evaluates in a loaded definition by the kind of its sorts' domain values,
//! by which sorts have domain values, and by the subsort order
//! ([`k_rust_backend::builtin::DeclarationFacts`]). The emitted definition states each of these
//! from the main module's declarations:
//! - a sort head is declared with `hasDomainValues` exactly when the sort catalog admits domain
//!   values for it ([`SortCatalog::head_admits_domain_values`]), and with the hook its sort
//!   declaration carries;
//! - the kind follows from those two facts by the rule the backend applies
//!   ([`DomainKind::of_declared_sort`]);
//! - the subsort axioms are those `emitted_subsort_pair` states.
//!
//! So an evaluation over these facts ([`k_rust_backend::builtin::evaluate_declared`]) decides an
//! application as an evaluation of the same application in the emitted definition, once loaded,
//! decides it.

use std::cell::OnceCell;

use k_rust_backend::{
    builtin::DeclarationFacts,
    term::{DomainKind, Sort as BackendSort},
};

use super::module_to_kore::{emitted_subsort_pair, encode_kore_sort};
use crate::{
    definition::{AttributeKey, PartialOrder, ProductionCatalog, SortCatalog, SortHead},
    kast::{Sort, identifier},
    kore::ast::Sort as KoreSort,
};

/// The declarations of the sorts of one module, as the definition emitted with that module as
/// its main module states them.
pub(crate) struct EmittedDeclarations<'view, 'definition> {
    sorts: &'view SortCatalog<'definition>,
    productions: &'view ProductionCatalog<'definition>,
    /// The order the emitted subsort axioms state, built on the first subsort question; `None`
    /// when the axioms are cyclic, which emission reports.
    subsorts: OnceCell<Option<PartialOrder<Sort>>>,
}

impl<'view, 'definition> EmittedDeclarations<'view, 'definition> {
    pub(crate) fn new(
        sorts: &'view SortCatalog<'definition>,
        productions: &'view ProductionCatalog<'definition>,
    ) -> Self {
        Self {
            sorts,
            productions,
            subsorts: OnceCell::new(),
        }
    }

    /// The hook the declaration of `sort`'s head carries.
    pub(crate) fn hook(&self, sort: &Sort) -> Option<&str> {
        self.sorts
            .attributes_for(&SortHead::from(sort))
            .and_then(|attributes| attributes.string(AttributeKey::Hook))
    }
}

impl DeclarationFacts for EmittedDeclarations<'_, '_> {
    type Sort = BackendSort;

    fn domain_kind(&self, sort: &BackendSort) -> Option<DomainKind> {
        let frontend = frontend_sort(sort)?;
        DomainKind::of_declared_sort(
            sort,
            self.sorts
                .head_admits_domain_values(&SortHead::from(&frontend)),
            self.hook(&frontend),
        )
    }

    fn has_domain_values(&self, sort: &BackendSort) -> bool {
        frontend_sort(sort).is_some_and(|frontend| {
            self.sorts
                .head_admits_domain_values(&SortHead::from(&frontend))
        })
    }

    fn check_subsort(&self, sub: &BackendSort, sup: &BackendSort) -> bool {
        if sub == sup {
            return true;
        }
        let (Some(sub), Some(sup)) = (frontend_sort(sub), frontend_sort(sup)) else {
            return false;
        };
        self.subsorts
            .get_or_init(|| {
                PartialOrder::new(
                    self.productions
                        .productions()
                        .filter_map(|(_, production)| emitted_subsort_pair(production))
                        .map(|(child, parent)| (child.clone(), parent.clone())),
                )
                .ok()
            })
            .as_ref()
            .is_some_and(|order| order.less_than_eq(&sub, &sup))
    }
}

/// The KORE sort the emitted definition writes for `sort`, as the backend holds it.
pub(crate) fn backend_sort(sort: &Sort) -> BackendSort {
    fn convert(sort: &KoreSort) -> BackendSort {
        match sort {
            KoreSort::Application { name, arguments } => {
                BackendSort::application(name.as_str(), arguments.iter().map(convert).collect())
            }
            KoreSort::Variable(name) => BackendSort::Variable(name.as_str().into()),
        }
    }
    convert(&encode_kore_sort(sort))
}

/// The frontend sort the emitted KORE sort `sort` writes; `None` for a sort variable or a name
/// that no frontend sort encodes.
fn frontend_sort(sort: &BackendSort) -> Option<Sort> {
    let BackendSort::Application { name, arguments } = sort else {
        return None;
    };
    Some(Sort::with_parameters(
        &identifier::decode_sort_name(name).ok()?,
        arguments
            .iter()
            .map(frontend_sort)
            .collect::<Option<Vec<_>>>()?,
    ))
}
