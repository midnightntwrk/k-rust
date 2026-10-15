//! The sort cell completion gives a variable written as the whole content of a cell.
//!
//! Cell completion (`kompile::passes::concretize_cells`) builds each authored cell
//! `L(#dots|#noDots, B, #dots|#noDots)` from the items of its body `B`.
//! An item of a cell sort fills the child of that sort.
//! A variable of no cell sort fills the child that can take it, and compilation gives the
//! variable that child's value sort: for a `multiplicity="*"` child, the collection sort
//! (`AccountCellMap`); for any other child, its cell sort.
//! The rule parser reads such a variable at `Bag` (it writes `#SemanticCastToBag(X)`), and the
//! empty bag `.Bag` is the child's unit, so neither holds a term of `Bag` once the cell is
//! completed.
//! When the cell has one content sort and it is made of cells (a cell sort or a collection of
//! cells), the one child is the child that takes the variable; a leaf cell's content is not
//! completed this way.
//! [`sort_cell_contents`] gives that variable the content sort, as completion does, so the
//! injector types the position as the compiled term has it. A body that is a rewrite gets the
//! same on each side that is such a variable. Every other body is unchanged: a cell-sorted item,
//! several items (`#cells`), or the empty bag, which has no sort and places no requirement.
//!
//! Cost: one walk of the sentence, and one production lookup per application and per
//! content-position variable.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::definition::{AttributeKey, ProductionItem, Sentence, SortHead};
use crate::kast::{Sort, Term, TermParts};

use super::super::SortInjector;
use super::is_authored_cell;

/// `term` with each variable that is the whole content of an authored cell of one content sort,
/// or a side of a rewrite that is, given that content sort when it has no cell sort.
// Invariant: each call recurses into the direct subterms of `term`; its depth bounds the
// recursion.
pub(super) fn sort_cell_contents(term: Term, injector: &SortInjector<'_, '_>) -> Term {
    let content = content_sort(&term, injector);
    let recurse = |term: Term| sort_cell_contents(term, injector);
    match term.into_parts() {
        TermParts::Annotated { term, metadata } => recurse(*term).with_metadata(metadata),
        TermParts::Apply { label, arguments } => {
            let mut arguments = arguments.into_iter().map(recurse).collect::<Vec<_>>();
            if let Some(content) = content {
                let body = std::mem::replace(&mut arguments[1], Term::Sequence(Vec::new()));
                arguments[1] = sort_content(body, &content, injector);
            }
            Term::Apply { label, arguments }
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(recurse(*left)),
            right: Box::new(recurse(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(recurse(*pattern)),
            alias: Box::new(recurse(*alias)),
        },
        TermParts::Sequence(items) => Term::Sequence(items.into_iter().map(recurse).collect()),
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
    }
}

/// The one content sort of `term` when it is an authored cell whose production has exactly
/// one nonterminal and that content is made of cells: a cell sort, or a collection of cells. A
/// leaf cell (`<k>`, `<n>`) holds a term of its content sort as written, which completion leaves
/// unchanged.
fn content_sort(term: &Term, injector: &SortInjector<'_, '_>) -> Option<Sort> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return None;
    };
    if !injector.has_production(term, label)
        || !is_authored_cell(injector, term, label, arguments).unwrap_or(false)
    {
        return None;
    }
    let Ok(Sentence::Production { items, .. }) = injector.production(term, label) else {
        return None;
    };
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "ProductionItem is not a sentence kind; only nonterminals are content"
    )]
    let mut nonterminals = items.iter().filter_map(|item| match item {
        ProductionItem::NonTerminal { sort, .. } => Some(sort),
        _ => None,
    });
    match (nonterminals.next(), nonterminals.next()) {
        (Some(content), None) if holds_cells(content, injector) => Some(content.clone()),
        _ => None,
    }
}

/// `body`, the content of a cell of content sort `content`: a variable of no cell sort takes
/// `content`, and so does each such variable side of a rewrite.
fn sort_content(body: Term, content: &Sort, injector: &SortInjector<'_, '_>) -> Term {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is syntax; only a variable or a rewrite of variables is re-sorted"
    )]
    match body.unannotated() {
        Term::Variable { .. } => sort_variable(body, content, injector),
        Term::Rewrite { .. } => {
            let metadata = body.metadata().cloned();
            let TermParts::Rewrite { left, right } = body.into_unannotated().into_parts() else {
                unreachable!("matched a rewrite")
            };
            let rewrite = Term::Rewrite {
                left: Box::new(side(*left, content, injector)),
                right: Box::new(side(*right, content, injector)),
            };
            match metadata {
                Some(metadata) => rewrite.with_metadata(metadata),
                None => rewrite,
            }
        }
        _ => body,
    }
}

fn side(term: Term, content: &Sort, injector: &SortInjector<'_, '_>) -> Term {
    if matches!(term.unannotated(), Term::Variable { .. }) {
        sort_variable(term, content, injector)
    } else {
        term
    }
}

/// `variable` with its own sort `content`, its annotation kept, unless its sort (its own, else
/// the one its annotation records) is a cell sort: such a variable fills the child of that sort.
fn sort_variable(variable: Term, content: &Sort, injector: &SortInjector<'_, '_>) -> Term {
    let Term::Variable { sort, .. } = variable.unannotated() else {
        unreachable!("a variable")
    };
    let written = sort.clone().or_else(|| {
        variable
            .metadata()
            .and_then(|metadata| metadata.sort.clone())
    });
    if written.is_some_and(|sort| is_cell_sort(&sort, injector)) {
        return variable;
    }
    let metadata = variable.metadata().cloned();
    let TermParts::Variable { name, .. } = variable.into_unannotated().into_parts() else {
        unreachable!("a variable")
    };
    let sorted = Term::Variable {
        name,
        sort: Some(content.clone()),
    };
    match metadata {
        Some(metadata) => sorted.with_metadata(metadata),
        None => sorted,
    }
}

/// Whether some production of `sort` is a cell.
fn is_cell_sort(sort: &Sort, injector: &SortInjector<'_, '_>) -> bool {
    has_production_with(sort, AttributeKey::Cell, injector)
}

/// Whether `sort`, a cell's content sort, is made of cells: a cell sort, or the collection sort of
/// a `multiplicity="*"` cell.
fn holds_cells(sort: &Sort, injector: &SortInjector<'_, '_>) -> bool {
    is_cell_sort(sort, injector)
        || has_production_with(sort, AttributeKey::CellCollection, injector)
}

fn has_production_with(sort: &Sort, key: AttributeKey, injector: &SortInjector<'_, '_>) -> bool {
    let productions = &injector.productions;
    productions
        .productions_for_sort(&SortHead::from(sort))
        .iter()
        .any(|id| productions.production(*id).attributes().has(key))
}
