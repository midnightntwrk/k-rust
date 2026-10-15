//! This definition-layer module has no separate measurement card: each constructor builds one
//! production of four items, and the `kompile.sort_helpers.generate` card of the passes that
//! call it counts their iteration.
//!
//! The signatures of the sort helpers: the sort predicate `isS` and the sort projection
//! `project:S` that compilation declares for a sort.
//!
//! Both are unary functions over `K`, `Bool ::= isS "(" K ")"` and `S ::= project:S "(" K ")"`.
//! Compilation declares them (`kompile::passes::generate_sort_helpers`), the rule grammar offers
//! them, and the typing view types a loaded rule that names one, each from the constructor here,
//! so the three cannot disagree on a signature. Each caller adds the attributes of its own role:
//! compilation the predicate's sort, the rule grammar its generated-syntax marker.
//! The field projections `project:L:F` have the same single constructor,
//! [`super::production_kind::FieldProjectionSource::projection_production`].

#![deny(clippy::wildcard_enum_match_arm)]

use super::totality::TotalityWitness;
use super::{AttributeKey, Attributes, ProductionItem, Sentence};
use crate::kast::{Label, Sort};
use crate::names::BuiltinSort;

/// The items of a unary sort helper named `name`: `name "(" K ")"`.
///
/// Both helpers take any `K` term: `isS(T)` tests whether `T` is a term of `S`, and
/// `project:S(T)` is `T` as a term of `S`.
pub(crate) fn sort_helper_items(name: &str) -> Vec<ProductionItem> {
    vec![
        ProductionItem::Terminal(name.to_owned()),
        ProductionItem::Terminal("(".into()),
        ProductionItem::NonTerminal {
            sort: Sort::builtin(BuiltinSort::K),
            name: None,
        },
        ProductionItem::Terminal(")".into()),
    ]
}

/// `Bool ::= isS "(" K ")"`, labelled [`Label::sort_predicate`] of `sort`, with `function` and
/// totality (its rules decide every argument) on top of `attributes`.
pub(crate) fn sort_predicate_production(sort: &Sort, mut attributes: Attributes) -> Sentence {
    let label = Label::sort_predicate(sort);
    attributes.mark(AttributeKey::Function);
    attributes.declare_total(TotalityWitness::covering_predicate());
    Sentence::Production {
        items: sort_helper_items(&label.name),
        label: Some(label),
        parameters: Vec::new(),
        sort: Sort::builtin(BuiltinSort::Bool),
        attributes,
    }
}

/// `S ::= project:S "(" K ")"` for `sort`, labelled `label` (the [`Label::projection`] of
/// `sort`), with `function` and `projection` on top of `attributes`.
pub(crate) fn sort_projection_production(
    sort: &Sort,
    label: Label,
    mut attributes: Attributes,
) -> Sentence {
    debug_assert_eq!(Label::projection(sort).as_ref(), Some(&label));
    attributes.mark(AttributeKey::Function);
    attributes.mark(AttributeKey::Projection);
    Sentence::Production {
        items: sort_helper_items(&label.name),
        label: Some(label),
        parameters: Vec::new(),
        sort: sort.clone(),
        attributes,
    }
}
