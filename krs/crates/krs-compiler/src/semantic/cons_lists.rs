//! Bracket list notation over cons lists (F6).
//!
//! A cons list is a sort with one empty constructor and one cons constructor
//! whose second field is the list itself: a `#[k::syntax_list]` sort, or the
//! sort of a `#[k::cons_list]` constructors enum. In a term, `[]` denotes its
//! empty constructor and each level `[head, ..tail]` its cons constructor, so
//! the notation means exactly the nested constructor term an author would
//! otherwise write. The brackets do not say which list they build; the
//! position does: a constructor field, a cell, or a function argument has a
//! declared sort, and that sort is the list. Inference and lowering therefore
//! replace each level by the constructor of the cons list the position
//! expects, and every later phase (emission, coverage, overlap) sees that
//! constructor. A position whose expected sort is unknown or not a cons list
//! has no constructor the brackets could denote, and is an error rather than
//! a guess.

use std::collections::BTreeMap;

use krs_ir::{
    ApplicationRef, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorCellReference, DescriptorPayload, DescriptorProductionAttribute,
    DescriptorProductionItem, GrammarDescriptor, ListNotation, ProtocolHeadRuleListRest,
    ProvenanceKey, SemanticId, StableItemId,
};
use krs_ir_levels::{SemanticSortRef, SemanticTerm, SemanticVariable};

use super::catalog::{ProductionSignature, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::StructuredTermBuilder;
use super::origin::semantic_origin;
use super::overload::sort_name;

/// One side of a readable record's list cell (F6).
type DescriptorHeadRuleList = krs_ir::ProtocolHeadRuleList<krs_ir::DescriptorTerm>;

/// The constructors of one cons-list sort.
pub(super) struct ConsListConstructors {
    /// The two-field constructor `Cons(head, tail)`.
    pub(super) cons: StableItemId,
    /// The zero-field constructor.
    pub(super) empty: StableItemId,
    /// The sort of the cons constructor's first field, the list's elements.
    pub(super) element: SemanticSortRef,
}

impl StructuredTermBuilder<'_> {
    /// The constructors of `sort` when it is a cons list.
    pub(super) fn cons_list_of(&self, sort: &SemanticSortRef) -> Option<ConsListConstructors> {
        self.catalog.iter().find_map(|(id, signature)| {
            if signature.result_sort != *sort {
                return None;
            }
            let empty = signature.cons_list_empty.clone()?;
            let (_, element) = signature.fields.first()?;
            Some(ConsListConstructors {
                cons: id.clone(),
                empty,
                element: element.clone(),
            })
        })
    }

    /// The constructor that one level of list notation denotes at
    /// `expected_sort`, at the level's own key.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidListNotation`] when the
    /// position's sort is unknown or is not a cons list.
    pub(super) fn list_constructor(
        &self,
        reference: &DescriptorApplicationReference,
        notation: ListNotation,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<DescriptorApplicationReference, DescriptorLoweringError> {
        let Some(expected) = expected_sort else {
            return Err(self.invalid_list_notation(
                &reference.key,
                "list notation builds a cons list, but nothing gives this position a sort, so the brackets name no list; use them where a constructor field, a cell, a function parameter, or a result declares a cons-list sort".to_owned(),
            ));
        };
        let Some(list) = self.cons_list_of(expected) else {
            return Err(self.invalid_list_notation(
                &reference.key,
                format!(
                    "list notation builds a cons list, but this position has sort `{}`, which is not one: a cons list is a `#[k::syntax_list]` sort or the sort of a `#[k::cons_list]` constructors enum",
                    sort_name(expected)
                ),
            ));
        };
        Ok(DescriptorApplicationReference {
            key: reference.key.clone(),
            application: DescriptorApplicationRef::Declared(match notation {
                ListNotation::Cons => list.cons,
                ListNotation::Empty => list.empty,
            }),
        })
    }

    pub(super) fn invalid_list_notation(
        &self,
        key: &ProvenanceKey,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidListNotation {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self.authored_range(key),
        }
    }
}

/// Checks every `#[k::cons_list]` enum (F6): its cons takes the list itself
/// as its tail, the field that makes it a list; and no sort is built by two
/// cons lists, since list notation at that sort would not say which.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::InvalidConsList`] at the first tail of
/// another sort or the second cons list of a sort.
pub(super) fn check_cons_lists(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let mut lists = BTreeMap::<SemanticSortRef, StableItemId>::new();
    for descriptor in descriptors {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            continue;
        };
        let GrammarDescriptor::Production(production) = grammar.as_ref() else {
            continue;
        };
        let id = super::grammar::production_owner_id(descriptor, production)?;
        let Some(signature) = catalog.get(&id) else {
            continue;
        };
        if signature.cons_list_empty.is_none() {
            continue;
        }
        let error =
            |key: &ProvenanceKey, reason: String| DescriptorLoweringError::InvalidConsList {
                item: Box::new(id.clone()),
                reason,
                range: descriptor
                    .provenance()
                    .origin_for(key)
                    .and_then(krs_ir::OriginStack::exact_authored_range)
                    .map(Box::new),
            };
        let marker = production
            .attributes
            .iter()
            .find_map(|attribute| match attribute {
                DescriptorProductionAttribute::ConsList { key, .. } => Some(key),
                _ => None,
            });
        if let Some(marker) = marker {
            let tail = production
                .items
                .iter()
                .filter_map(|item| match item {
                    DescriptorProductionItem::NonTerminal { field, sort, .. } => {
                        Some((field, sort))
                    }
                    _ => None,
                })
                .nth(1);
            if let Some((field, sort)) = tail
                && semantic_sort_ref(&sort.sort) != signature.result_sort
            {
                return Err(error(
                    &sort.key,
                    format!(
                        "the tail `{field}` of `{}` has sort `{}`, but a cons list's tail is the list itself, `{}`",
                        id.item_name(),
                        sort_name(&semantic_sort_ref(&sort.sort)),
                        sort_name(&signature.result_sort)
                    ),
                ));
            }
            if let Some(previous) = lists.insert(signature.result_sort.clone(), id.clone()) {
                return Err(error(
                    marker,
                    format!(
                        "`{}` is built by two cons lists, `{}` and `{}`, so list notation at `{}` would not say which; keep `#[k::cons_list]` on one enum",
                        sort_name(&signature.result_sort),
                        previous.item_name(),
                        id.item_name(),
                        sort_name(&signature.result_sort)
                    ),
                ));
            }
        } else if let Some(previous) = lists.insert(signature.result_sort.clone(), id.clone()) {
            // A syntactic list is a closed sort, which its own check
            // reports; a second list notation of it would be ambiguous.
            return Err(DescriptorLoweringError::InvalidConsList {
                item: Box::new(id.clone()),
                reason: format!(
                    "`{}` is built by two cons lists, `{}` and `{}`, so list notation at `{}` would not say which",
                    sort_name(&signature.result_sort),
                    previous.item_name(),
                    id.item_name(),
                    sort_name(&signature.result_sort)
                ),
                range: None,
            });
        }
    }
    Ok(())
}

impl StructuredTermBuilder<'_> {
    /// The cons list a readable record's list cell holds: `stack: [a, ..]`
    /// reads the cell `stack` as list elements, so its declared sort, `sort`,
    /// must be a cons list.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidListNotation`] at the cell
    /// when it is not a leaf of a cons-list sort.
    pub(super) fn list_cell(
        &self,
        cell: &DescriptorCellReference,
        sort: Option<&SemanticSortRef>,
    ) -> Result<ConsListConstructors, DescriptorLoweringError> {
        sort.and_then(|sort| self.cons_list_of(sort)).ok_or_else(|| {
            let held = sort.map_or_else(
                || "a nested cell group".to_owned(),
                |sort| format!("`{}`", sort_name(sort)),
            );
            self.invalid_list_notation(
                &cell.key,
                format!(
                    "the cell `{}` holds {held}, which is not a cons list: a bracketed cell value is the computation cell's items, a List collection's instances, or the elements of a cell whose sort is a `#[k::syntax_list]` sort or a `#[k::cons_list]` enum's",
                    cell.cell.field
                ),
            )
        })
    }

    /// Infers one side of a list cell: its elements at the list's element
    /// sort and a named rest at the list's sort.
    pub(super) fn infer_list(
        &mut self,
        list: &DescriptorHeadRuleList,
        sort: &SemanticSortRef,
        constructors: &ConsListConstructors,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        for item in &list.items {
            self.infer(item, Some(&constructors.element), subject)?;
        }
        if let ProtocolHeadRuleListRest::Term(rest) = &list.rest {
            self.infer(rest, Some(sort), subject)?;
        }
        Ok(())
    }

    /// The variable an anonymous `..` of a list cell names: one rest of the
    /// cell's sort, declared once and shared by both sides of the rule, as
    /// the computation cell's `..` is.
    pub(super) fn shared_list_rest(
        &mut self,
        cell: &DescriptorCellReference,
        sort: &SemanticSortRef,
    ) -> Result<SemanticId, DescriptorLoweringError> {
        let field = cell
            .cell
            .field
            .strip_prefix("r#")
            .unwrap_or(&cell.cell.field);
        let id = SemanticId::new(format!("{}rest_{field}", krs_ir::ir::RESERVED_MARKER))?;
        if !self.wildcards.iter().any(|variable| *variable.id() == id) {
            self.wildcards
                .push(SemanticVariable::new(id.clone(), sort.clone()));
        }
        Ok(id)
    }

    /// Lowers one side of a list cell to the constructor term it denotes:
    /// each element consed, front last, onto the rest, which is the empty
    /// list, the shared rest variable, or the named rest. `side` names the
    /// side in the generated nodes' origins, which share the cell's key.
    pub(super) fn lower_list(
        &mut self,
        list: &DescriptorHeadRuleList,
        sort: &SemanticSortRef,
        constructors: &ConsListConstructors,
        cell: &DescriptorCellReference,
        side: &str,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        let items = list
            .items
            .iter()
            .map(|item| self.lower(item, Some(&constructors.element), subject))
            .collect::<Result<Vec<_>, _>>()?;
        let mut list_term = match &list.rest {
            ProtocolHeadRuleListRest::Exact => SemanticTerm::application(
                semantic_origin(descriptor, cell.key.clone(), &format!("list-empty-{side}"))?,
                sort.clone(),
                ApplicationRef::Declared(constructors.empty.clone()),
                Vec::new(),
            ),
            ProtocolHeadRuleListRest::Shared => SemanticTerm::variable(
                semantic_origin(descriptor, cell.key.clone(), &format!("list-rest-{side}"))?,
                sort.clone(),
                self.shared_list_rest(cell, sort)?,
            ),
            ProtocolHeadRuleListRest::Term(rest) => self.lower(rest, Some(sort), subject)?,
        };
        for (index, item) in items.into_iter().enumerate().rev() {
            list_term = SemanticTerm::application(
                semantic_origin(
                    descriptor,
                    cell.key.clone(),
                    &format!("list-cons-{side}-{index}"),
                )?,
                sort.clone(),
                ApplicationRef::Declared(constructors.cons.clone()),
                vec![item, list_term],
            );
        }
        Ok(list_term)
    }
}
