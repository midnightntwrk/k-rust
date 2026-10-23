//! Bracket list notation over cons lists (F6) and K's builtin `List`.
//!
//! A cons list is a sort with one empty constructor and one cons constructor
//! whose second field is the list itself: a `#[k::syntax_list]` sort, or the
//! sort of a `#[k::cons_list]` constructors enum. In a term, `[]` denotes its
//! empty constructor and each level `[head, ..tail]` its cons constructor, so
//! the notation means exactly the nested constructor term an author would
//! otherwise write. A cons list is built from its front, so a level taken
//! from the back, `[..init, last]`, has no constructor to denote.
//!
//! K's builtin `List` is the other list sort. Its concatenation `_List_` is
//! associative and total with unit `.List`, so elements and at most one list
//! term in a row have one meaning however they nest: at a `List` position,
//! `[a, ..mid, z]` is `ListItem(a) mid ListItem(z)`, the list whose first
//! element is `a`, whose last is `z`, and whose middle is `mid`. The brackets
//! name that `list::item`/`list::concat` term and nothing more: `[a, b]` is
//! `ListItem(a) ListItem(b)`, since a trailing `.List` adds nothing to a
//! concatenation, and `[]` is `.List`.
//!
//! The brackets do not say which list they build; the position does: a
//! constructor field, a cell, or a function argument has a declared sort,
//! and that sort is the list. Inference and lowering therefore replace each
//! level by the terms of the list the position expects, and every later
//! phase (emission, coverage, overlap) sees those terms. A position whose
//! expected sort is unknown or no list has nothing the brackets could
//! denote, and is an error rather than a guess.

use std::collections::BTreeMap;

use krs_ir::{
    ApplicationRef, CollectionOperandSort, Descriptor, DescriptorApplicationRef,
    DescriptorApplicationReference, DescriptorCellReference, DescriptorPayload,
    DescriptorProductionAttribute, DescriptorProductionItem, GrammarDescriptor, ListNotation,
    ListOperation, NodeOrigin, ProtocolHeadRuleListRest, ProvenanceKey, SemanticId, StableItemId,
};
use krs_ir_levels::{ListOperands, SemanticSortRef, SemanticTerm, SemanticVariable};

use super::catalog::{ProductionSignature, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::StructuredTermBuilder;
use super::origin::semantic_origin;
use super::overload::sort_name;

/// One side of a readable record's list cell (F6).
type DescriptorHeadRuleList = krs_ir::ProtocolHeadRuleList<krs_ir::DescriptorTerm>;

/// The constructors of one cons-list sort, or of the builtin `List`, which
/// is built with `list::item` and `list::concat`.
pub(super) struct ConsListConstructors {
    /// The two-field constructor `Cons(head, tail)`; `None` for the builtin
    /// `List`, which is built with `list::item` and `list::concat`.
    pub(super) cons: Option<StableItemId>,
    /// The zero-field constructor; `None` for the builtin `List`, whose
    /// empty list is `.List`.
    pub(super) empty: Option<StableItemId>,
    /// The sort of the cons constructor's first field, the list's elements;
    /// the builtin `List` itself for the builtin `List`, whose elements'
    /// sort only a typed collection declares.
    pub(super) element: SemanticSortRef,
}

/// A bracket list at the builtin `List`, flattened: the elements before its
/// rest, each with the key of its level, the rest, and the elements after
/// it. A closed list has no rest and no back.
struct BuiltinList<'t> {
    front: Vec<(ProvenanceKey, &'t krs_ir::DescriptorTerm)>,
    rest: Option<&'t krs_ir::DescriptorTerm>,
    back: Vec<(ProvenanceKey, &'t krs_ir::DescriptorTerm)>,
}

/// One element of a lowered builtin list: the `list::item` it is wrapped in
/// and the `list::concat` that joins it to its neighbors share its level's
/// key, under these origins.
struct BuiltinElement {
    item: NodeOrigin,
    concat: NodeOrigin,
    element: SemanticTerm,
}

const BUILTIN_LIST: SemanticSortRef = SemanticSortRef::Builtin(krs_ir::BuiltinSort::List);

/// Whether a position expects K's builtin `List`, where brackets are
/// `list::item`/`list::concat` terms.
pub(super) fn is_builtin_list(expected_sort: Option<&SemanticSortRef>) -> bool {
    expected_sort == Some(&BUILTIN_LIST)
}

/// The builtin `List` term of `front`, `rest`, and `back`, nested as an
/// author writes it: each front element's `list::item` joined to the rest of
/// the list, `list::concat(list::item(a), ..)`, and each back element's
/// appended to the list before it, `list::concat(.., list::item(z))`. The
/// last front element of a closed list is its `list::item` alone.
fn builtin_list_term(
    front: Vec<BuiltinElement>,
    rest: Option<SemanticTerm>,
    back: Vec<BuiltinElement>,
    empty: NodeOrigin,
) -> SemanticTerm {
    let item = |element: BuiltinElement| {
        (
            SemanticTerm::list(
                element.item,
                BUILTIN_LIST,
                ListOperands::Item {
                    element: element.element,
                },
            ),
            element.concat,
        )
    };
    let concat = |origin, left, right| {
        SemanticTerm::list(origin, BUILTIN_LIST, ListOperands::Concat { left, right })
    };
    let mut list = rest;
    for element in back {
        let (item, origin) = item(element);
        list = Some(match list {
            Some(init) => concat(origin, init, item),
            None => item,
        });
    }
    for element in front.into_iter().rev() {
        let (item, origin) = item(element);
        list = Some(match list {
            Some(tail) => concat(origin, item, tail),
            None => item,
        });
    }
    list.unwrap_or_else(|| SemanticTerm::list(empty, BUILTIN_LIST, ListOperands::Empty))
}

/// One level of a bracket list's spine (see `list_spine`).
struct SpineLevel<'t> {
    /// The cons constructor, at the level's key.
    constructor: DescriptorApplicationReference,
    /// The list sort the constructor builds.
    result_sort: SemanticSortRef,
    /// The sort of the constructor's head field.
    element: SemanticSortRef,
    /// The level's head.
    head: &'t krs_ir::DescriptorTerm,
}

/// A bracket list's spine: its levels, front first, and the term the last
/// level conses onto, with that term's sort.
struct ListSpine<'t> {
    levels: Vec<SpineLevel<'t>>,
    tail: &'t krs_ir::DescriptorTerm,
    tail_sort: SemanticSortRef,
}

/// Why a cons list has no level taken from its back.
const CONS_LIST_BACK: &str = "a cons list is matched and built from its front, so its back is no constructor pattern: `..` may only end its brackets; name the elements before the rest";

impl StructuredTermBuilder<'_> {
    /// The constructors of `sort` when it is a cons list.
    pub(super) fn cons_list_of(&self, sort: &SemanticSortRef) -> Option<ConsListConstructors> {
        // `[]` is the empty list wherever a List is expected.
        if *sort == SemanticSortRef::Builtin(krs_ir::BuiltinSort::List) {
            return Some(ConsListConstructors {
                cons: None,
                empty: None,
                element: sort.clone(),
            });
        }
        self.catalog.iter().find_map(|(id, signature)| {
            if signature.result_sort != *sort {
                return None;
            }
            let empty = signature.cons_list_empty.clone()?;
            let (_, element) = signature.fields.first()?;
            Some(ConsListConstructors {
                cons: Some(id.clone()),
                empty: Some(empty),
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
                "list notation builds a list, but nothing gives this position a sort, so the brackets name no list; use them where a constructor field, a cell, a function parameter, or a result declares the builtin `List` or a cons-list sort".to_owned(),
            ));
        };
        let Some(list) = self.cons_list_of(expected) else {
            return Err(self.invalid_list_notation(
                &reference.key,
                format!(
                    "list notation builds a list, but this position has sort `{}`, which is not one: a list is the builtin `List`, a `#[k::syntax_list]` sort, or the sort of a `#[k::cons_list]` constructors enum",
                    sort_name(expected)
                ),
            ));
        };
        let application = match (notation, list.cons, list.empty) {
            (ListNotation::Cons, Some(cons), _) => DescriptorApplicationRef::Declared(cons),
            (ListNotation::Snoc, Some(_), _) => {
                return Err(self.invalid_list_notation(&reference.key, CONS_LIST_BACK.to_owned()));
            }
            (ListNotation::Cons | ListNotation::Snoc, None, _) => {
                return Err(self.invalid_term(
                    "a bracket level at the builtin `List` is lowered as one list, never alone",
                ));
            }
            (ListNotation::Empty, _, Some(empty)) => DescriptorApplicationRef::Declared(empty),
            (ListNotation::Empty, _, None) => DescriptorApplicationRef::List(ListOperation::Empty),
        };
        Ok(DescriptorApplicationReference {
            key: reference.key.clone(),
            application,
        })
    }

    /// The levels of a bracket list's spine, `[e1, .., en, ..rest]`: each
    /// level's cons constructor at the sort its position expects, its
    /// signature, and its head, in order, then the tail the last level
    /// conses onto (the empty list, a rest, or any other term) and the
    /// tail's sort. Walking the spine in a loop keeps the stack depth of
    /// inference and lowering independent of the list's length: a level
    /// recurses only into its head.
    fn list_spine<'t>(
        &self,
        reference: &DescriptorApplicationReference,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
    ) -> Result<ListSpine<'t>, DescriptorLoweringError> {
        if reference.application == DescriptorApplicationRef::ListNotation(ListNotation::Snoc) {
            // A level taken from the back denotes nothing at a cons list.
            self.list_constructor(reference, ListNotation::Snoc, expected_sort)?;
            return Err(self.invalid_term("a cons list has no level taken from its back"));
        }
        let mut levels = Vec::new();
        let mut reference = reference.clone();
        let mut arguments = arguments;
        let mut expected = expected_sort.cloned();
        loop {
            let constructor =
                self.list_constructor(&reference, ListNotation::Cons, expected.as_ref())?;
            let DescriptorApplicationRef::Declared(id) = &constructor.application else {
                return Err(self.invalid_term("list notation chose no cons constructor"));
            };
            let signature = self.catalog.get(id).cloned().ok_or_else(|| {
                self.invalid_term(format!(
                    "declared application {id} has no grammar production"
                ))
            })?;
            let (krs_ir::Arguments::Positional(values), [(_, element), (_, tail_sort)]) =
                (arguments, signature.fields.as_slice())
            else {
                return Err(
                    self.invalid_term("a list notation level is a cons of a head and a tail")
                );
            };
            let [head, tail] = values.as_slice() else {
                return Err(
                    self.invalid_term("a list notation level is a cons of a head and a tail")
                );
            };
            let (element, tail_sort) = (element.clone(), tail_sort.clone());
            levels.push(SpineLevel {
                constructor,
                result_sort: signature.result_sort,
                element,
                head,
            });
            match tail.as_ref() {
                krs_ir::DescriptorTerm::Application {
                    reference: next,
                    arguments: next_arguments,
                    instance,
                    update: None,
                    ..
                } if instance.is_empty()
                    && next.application
                        == DescriptorApplicationRef::ListNotation(ListNotation::Cons) =>
                {
                    reference = next.clone();
                    arguments = next_arguments;
                    expected = Some(tail_sort);
                }
                tail => {
                    return Ok(ListSpine {
                        levels,
                        tail,
                        tail_sort,
                    });
                }
            }
        }
    }

    /// Infers a bracket list's spine (F6): each head at its list's element
    /// sort, in order, then the tail at the list's sort, as the nested
    /// constructor terms would be inferred.
    pub(super) fn infer_list_spine(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if is_builtin_list(expected_sort) {
            let list = self.builtin_list(reference, arguments)?;
            for (_, element) in list.front.iter().chain(&list.back) {
                let expected =
                    self.collection_operand_expected(element, CollectionOperandSort::Element);
                self.infer(element, expected.as_ref(), subject)?;
            }
            if let Some(rest) = list.rest {
                self.infer(rest, Some(&BUILTIN_LIST), subject)?;
            }
            return Ok(());
        }
        let spine = self.list_spine(reference, arguments, expected_sort)?;
        for level in &spine.levels {
            self.infer(level.head, Some(&level.element), subject)?;
        }
        self.infer(spine.tail, Some(&spine.tail_sort), subject)
    }

    /// Lowers a bracket list's spine (F6) to the nested cons constructor
    /// terms it denotes, lowering the heads in order and then the tail, the
    /// order the nested terms would be lowered in.
    pub(super) fn lower_list_spine(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        expected_sort: Option<&SemanticSortRef>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        if is_builtin_list(expected_sort) {
            return self.lower_builtin_list(reference, arguments, subject);
        }
        let spine = self.list_spine(reference, arguments, expected_sort)?;
        let heads = spine
            .levels
            .iter()
            .map(|level| self.lower(level.head, Some(&level.element), subject))
            .collect::<Result<Vec<_>, _>>()?;
        let mut list = self.lower(spine.tail, Some(&spine.tail_sort), subject)?;
        for (level, head) in spine.levels.into_iter().zip(heads).rev() {
            let DescriptorApplicationRef::Declared(id) = level.constructor.application else {
                unreachable!("a spine level is a declared cons constructor");
            };
            list = SemanticTerm::application(
                semantic_origin(self.descriptor, level.constructor.key, "term-application")?,
                level.result_sort,
                ApplicationRef::Declared(id),
                vec![head, list],
            );
        }
        Ok(list)
    }

    /// A bracket list at the builtin `List`, flattened ([`BuiltinList`]):
    /// its `cons` levels give the front elements, front first, its `snoc`
    /// levels the back elements, and the term the innermost level holds is
    /// its rest; the empty list ends a closed list. The levels are walked in
    /// a loop, so a list's length does not drive the stack depth.
    fn builtin_list<'t>(
        &self,
        reference: &DescriptorApplicationReference,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<BuiltinList<'t>, DescriptorLoweringError> {
        /// The level a term is, when it is one.
        fn level(
            term: &krs_ir::DescriptorTerm,
        ) -> Option<(
            &DescriptorApplicationReference,
            ListNotation,
            &krs_ir::Arguments<krs_ir::DescriptorStage>,
        )> {
            match term {
                krs_ir::DescriptorTerm::Application {
                    reference,
                    arguments,
                    instance,
                    update: None,
                    ..
                } if instance.is_empty() => match reference.application {
                    DescriptorApplicationRef::ListNotation(notation) => {
                        Some((reference, notation, arguments))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        let operands = |arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>| match arguments {
            krs_ir::Arguments::Positional(values) => match values.as_slice() {
                [first, second] => Ok((first.as_ref(), second.as_ref())),
                _ => Err(self.invalid_term("a list notation level has two operands")),
            },
            krs_ir::Arguments::Named(_) => {
                Err(self.invalid_term("a list notation level has two operands"))
            }
        };
        let mut list = BuiltinList {
            front: Vec::new(),
            rest: None,
            back: Vec::new(),
        };
        let mut key = reference.key.clone();
        let DescriptorApplicationRef::ListNotation(mut notation) = reference.application else {
            return Err(self.invalid_term("a builtin list starts at a list notation level"));
        };
        let mut arguments = arguments;
        loop {
            let (first, second) = operands(arguments)?;
            let next = match notation {
                ListNotation::Cons => {
                    list.front.push((key, first));
                    match level(second) {
                        Some((_, ListNotation::Empty, _)) => break,
                        Some(next) => next,
                        None => {
                            list.rest = Some(second);
                            break;
                        }
                    }
                }
                ListNotation::Snoc => {
                    list.back.push((key, second));
                    if let Some(next @ (_, ListNotation::Snoc, _)) = level(first) {
                        next
                    } else {
                        list.rest = Some(first);
                        break;
                    }
                }
                ListNotation::Empty => {
                    return Err(self.invalid_term("the empty list is no level of a list"));
                }
            };
            key = next.0.key.clone();
            notation = next.1;
            arguments = next.2;
        }
        list.back.reverse();
        Ok(list)
    }

    /// Lowers a bracket list at the builtin `List` to the
    /// `list::item`/`list::concat` term it denotes ([`builtin_list_term`]),
    /// lowering the front elements, the rest, and the back elements in the
    /// order they are written.
    fn lower_builtin_list(
        &mut self,
        reference: &DescriptorApplicationReference,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let list = self.builtin_list(reference, arguments)?;
        let front = self.lower_builtin_elements(&list.front, subject)?;
        let rest = list
            .rest
            .map(|rest| self.lower(rest, Some(&BUILTIN_LIST), subject))
            .transpose()?;
        let back = self.lower_builtin_elements(&list.back, subject)?;
        let empty = semantic_origin(
            self.descriptor,
            reference.key.clone(),
            "list-notation-empty",
        )?;
        Ok(builtin_list_term(front, rest, back, empty))
    }

    /// Lowers the elements of a builtin list, each at the element sort its
    /// typed collection declares, if any, with the origins of its level.
    fn lower_builtin_elements(
        &mut self,
        elements: &[(ProvenanceKey, &krs_ir::DescriptorTerm)],
        subject: bool,
    ) -> Result<Vec<BuiltinElement>, DescriptorLoweringError> {
        elements
            .iter()
            .map(|(key, element)| {
                let expected = self.collection_element_sort(element);
                Ok(BuiltinElement {
                    item: semantic_origin(self.descriptor, key.clone(), "list-notation-item")?,
                    concat: semantic_origin(self.descriptor, key.clone(), "list-notation-concat")?,
                    element: self.lower(element, expected.as_ref(), subject)?,
                })
            })
            .collect()
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
    /// The list a readable record's list cell holds: `stack: [a, ..]` reads
    /// the cell `stack` as list elements, so its declared sort, `sort`, must
    /// be the builtin `List` or a cons list.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorLoweringError::InvalidListNotation`] at the cell
    /// when it is not a leaf of a list sort.
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
                    "the cell `{}` holds {held}, which is not a list: a bracketed cell value is the computation cell's items, a List collection's instances, or the elements of a cell whose sort is the builtin `List`, a `#[k::syntax_list]` sort, or a `#[k::cons_list]` enum's",
                    cell.cell.field
                ),
            )
        })
    }

    /// Infers one side of a list cell: its elements at the list's element
    /// sort (at the builtin `List`, the sort its typed collection declares,
    /// if any) and a named rest at the list's sort. A cons list has no
    /// elements after its rest.
    pub(super) fn infer_list(
        &mut self,
        list: &DescriptorHeadRuleList,
        sort: &SemanticSortRef,
        constructors: &ConsListConstructors,
        cell: &DescriptorCellReference,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        if constructors.cons.is_some() && !list.back.is_empty() {
            return Err(self.invalid_list_notation(&cell.key, CONS_LIST_BACK.to_owned()));
        }
        let element = |builder: &mut Self, item: &krs_ir::DescriptorTerm| {
            if constructors.cons.is_some() {
                Some(constructors.element.clone())
            } else {
                builder.collection_operand_expected(item, CollectionOperandSort::Element)
            }
        };
        for item in &list.items {
            let expected = element(self, item);
            self.infer(item, expected.as_ref(), subject)?;
        }
        if let ProtocolHeadRuleListRest::Term(rest) = &list.rest {
            self.infer(rest, Some(sort), subject)?;
        }
        for item in &list.back {
            let expected = element(self, item);
            self.infer(item, expected.as_ref(), subject)?;
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

    /// Lowers one side of a list cell to the term it denotes. For a cons
    /// list, each element consed, front last, onto the rest, which is the
    /// empty list, the shared rest variable, or the named rest; for the
    /// builtin `List`, the `list::item`/`list::concat` term of the front
    /// elements, the rest, and the back elements ([`builtin_list_term`]).
    /// `side` names the side in the generated nodes' origins, which share
    /// the cell's key.
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
        let Some(cons) = &constructors.cons else {
            return self.lower_builtin_list_cell(list, cell, side, subject);
        };
        let items = list
            .items
            .iter()
            .map(|item| self.lower(item, Some(&constructors.element), subject))
            .collect::<Result<Vec<_>, _>>()?;
        let mut list_term = match &list.rest {
            ProtocolHeadRuleListRest::Exact => {
                let origin =
                    semantic_origin(descriptor, cell.key.clone(), &format!("list-empty-{side}"))?;
                match &constructors.empty {
                    Some(empty) => SemanticTerm::application(
                        origin,
                        sort.clone(),
                        ApplicationRef::Declared(empty.clone()),
                        Vec::new(),
                    ),
                    None => SemanticTerm::list(origin, sort.clone(), ListOperands::Empty),
                }
            }
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
                ApplicationRef::Declared(cons.clone()),
                vec![item, list_term],
            );
        }
        Ok(list_term)
    }

    /// Lowers one side of a builtin `List` cell, its elements at the sort
    /// its typed collection declares, if any.
    fn lower_builtin_list_cell(
        &mut self,
        list: &DescriptorHeadRuleList,
        cell: &DescriptorCellReference,
        side: &str,
        subject: bool,
    ) -> Result<SemanticTerm, DescriptorLoweringError> {
        let descriptor = self.descriptor;
        let elements = |builder: &mut Self, items: &[krs_ir::DescriptorTerm], part: &str| {
            items
                .iter()
                .enumerate()
                .map(|(index, item)| {
                    let expected = builder.collection_element_sort(item);
                    let origin = |role: &str| {
                        semantic_origin(
                            descriptor,
                            cell.key.clone(),
                            &format!("list-{role}-{side}-{part}{index}"),
                        )
                    };
                    Ok(BuiltinElement {
                        item: origin("item")?,
                        concat: origin("concat")?,
                        element: builder.lower(item, expected.as_ref(), subject)?,
                    })
                })
                .collect::<Result<Vec<_>, DescriptorLoweringError>>()
        };
        let front = elements(self, &list.items, "")?;
        let rest = match &list.rest {
            ProtocolHeadRuleListRest::Exact => None,
            ProtocolHeadRuleListRest::Shared => Some(SemanticTerm::variable(
                semantic_origin(descriptor, cell.key.clone(), &format!("list-rest-{side}"))?,
                BUILTIN_LIST,
                self.shared_list_rest(cell, &BUILTIN_LIST)?,
            )),
            ProtocolHeadRuleListRest::Term(rest) => {
                Some(self.lower(rest, Some(&BUILTIN_LIST), subject)?)
            }
        };
        let back = elements(self, &list.back, "back-")?;
        let empty = semantic_origin(descriptor, cell.key.clone(), &format!("list-empty-{side}"))?;
        Ok(builtin_list_term(front, rest, back, empty))
    }
}
