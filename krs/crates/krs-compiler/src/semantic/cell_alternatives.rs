//! `A | B` over a whole group cell, where a term stands among cells.
//!
//! On a left-hand side, `outer: P1 | P2` matches a configuration whose
//! `<outer>` cell matches either alternative. A group cell's entry is not a
//! term, though: it is a set of cells, which K places by their labels and
//! completes from the declaration, and a disjunction of two such sets is not a
//! cell that completion can place. A single rule cannot state the union of
//! two different products of children; one rule per alternative can, and so
//! can one record when the alternatives differ in one child only, since a
//! cell term distributes over `|` as a constructor does. So `|` at a group
//! entry, an optional group's `Some(..)`, or a group child of a cell term is
//! refused here, where it is written, with those two rewrites.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use krs_ir::{
    Descriptor, DescriptorCellDeclaration, DescriptorTerm, ProtocolCellContent, ProvenanceKey,
    StableItemId,
};

use super::error::DescriptorLoweringError;

/// Refuses `term`, written where the whole group cell `cell` of declaration
/// `group` stands, when it joins alternatives, also below an alias.
pub(super) fn reject_cell_alternatives(
    descriptor: &Descriptor,
    term: &DescriptorTerm,
    cell: &str,
    group: &StableItemId,
    declaration: &DescriptorCellDeclaration,
) -> Result<(), DescriptorLoweringError> {
    let children = declaration
        .fields
        .iter()
        .map(|field| {
            (
                field.rust_field.as_str(),
                matches!(field.content, ProtocolCellContent::Leaf { .. }),
            )
        })
        .collect::<Vec<_>>();
    let Some((key, reason)) = cell_alternatives(term, cell, group, &children) else {
        return Ok(());
    };
    Err(DescriptorLoweringError::InvalidPatternOr {
        item: Box::new(descriptor.id().clone()),
        reason,
        range: descriptor
            .provenance()
            .origin_for(key)
            .and_then(krs_ir::OriginStack::exact_authored_range)
            .map(Box::new),
    })
}

/// The `|` key and the reason when `term`, below any aliases, joins
/// alternatives of a whole group cell; `children` are the group's declared
/// children, each with whether it is a leaf.
fn cell_alternatives<'t>(
    term: &'t DescriptorTerm,
    cell: &str,
    group: &StableItemId,
    children: &[(&str, bool)],
) -> Option<(&'t ProvenanceKey, String)> {
    let mut term = term;
    while let DescriptorTerm::As { pattern, .. } = term {
        term = pattern;
    }
    let DescriptorTerm::Or { key, alternatives } = term else {
        return None;
    };
    let name = group.item_name();
    let mut reason = format!(
        "`|` cannot join alternatives of the whole `{cell}` cell: a group cell's entry is a set of cells, each placed by its label, and no single rule matches one set or another; write the alternatives inside the record, at the child they test (`{name} {{ child: A | B, .. }}`), or write one rule per alternative"
    );
    if let Some(child) = only_differing_leaf(alternatives.iter(), group, children) {
        let _ = write!(
            reason,
            "; the alternatives differ only in `{child}`: write `{name} {{ {child}: A | B, .. }}`"
        );
    }
    Some((key, reason))
}

/// The one leaf child in which group records `alternatives` differ, when
/// they are all bare records of `group` that agree on every other child. An
/// omitted child and `_` both match anything, and provenance keys are not
/// part of a pattern's meaning.
fn only_differing_leaf<'c, 't>(
    alternatives: impl Iterator<Item = &'t DescriptorTerm>,
    group: &StableItemId,
    children: &[(&'c str, bool)],
) -> Option<&'c str> {
    let mut records = Vec::new();
    for alternative in alternatives {
        let DescriptorTerm::Cell {
            declaration: record,
            fields,
            update: None,
            ..
        } = alternative
        else {
            return None;
        };
        if record != group {
            return None;
        }
        let mut written = BTreeMap::new();
        for field in fields {
            if !matches!(*field.value, DescriptorTerm::Wildcard { .. }) {
                written.insert(field.field.as_str(), without_keys(&field.value)?);
            }
        }
        records.push(written);
    }
    let mut differing = children.iter().filter(|(child, _)| {
        records
            .windows(2)
            .any(|pair| pair[0].get(child) != pair[1].get(child))
    });
    let (child, leaf) = differing.next()?;
    (differing.next().is_none() && *leaf).then_some(*child)
}

/// `term` as JSON with every provenance key removed.
fn without_keys(term: &DescriptorTerm) -> Option<serde_json::Value> {
    fn strip(value: &mut serde_json::Value) {
        match value {
            serde_json::Value::Object(object) => {
                object.retain(|_, field| !is_provenance_key(field));
                object.values_mut().for_each(strip);
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(strip),
            _ => {}
        }
    }
    let mut value = serde_json::to_value(term).ok()?;
    strip(&mut value);
    Some(value)
}

/// Whether `value` is a serialized [`ProvenanceKey`]: a role and an ordinal.
fn is_provenance_key(value: &serde_json::Value) -> bool {
    value.as_object().is_some_and(|object| {
        object.len() == 2
            && object.get("role").is_some_and(serde_json::Value::is_string)
            && object.get("ordinal").is_some_and(serde_json::Value::is_u64)
    })
}

#[cfg(test)]
mod tests {
    use krs_ir::{
        AtLeastTwo, CellTermField, DescriptorLiteral, DescriptorTerm, ItemKind, PackageId,
        ProductionFieldId, ProvenanceKey, StableItemId,
    };
    use krs_syntax::ProvenanceRole;

    use super::cell_alternatives;

    const CHILDREN: &[(&str, bool)] = &[("frame", false), ("flag", true), ("mode", true)];

    fn key(ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::RuleLeftLiteral, ordinal)
    }

    fn group() -> StableItemId {
        StableItemId::new(
            PackageId::new("CELL-ALTERNATIVES", "cell-alternatives", "0.1.0", "test").unwrap(),
            ["fixture"],
            "Outer",
            ItemKind::Cell,
            "",
        )
        .unwrap()
    }

    fn int(value: &str, ordinal: u32) -> DescriptorTerm {
        DescriptorTerm::Literal {
            key: key(ordinal),
            literal: DescriptorLiteral::Int(value.to_owned()),
        }
    }

    /// `Outer { child: value, .., }` with fresh keys from `ordinal`.
    fn record(children: &[(&str, DescriptorTerm)], ordinal: u32) -> DescriptorTerm {
        DescriptorTerm::Cell {
            key: key(ordinal),
            declaration: group(),
            fields: children
                .iter()
                .map(|(child, value)| CellTermField {
                    key: key(ordinal + 1),
                    field: ProductionFieldId::new(*child).unwrap(),
                    value: Box::new(value.clone()),
                })
                .collect(),
            open: true,
            update: None,
        }
    }

    fn or(alternatives: Vec<DescriptorTerm>) -> DescriptorTerm {
        DescriptorTerm::Or {
            key: key(99),
            alternatives: AtLeastTwo::try_from(alternatives).unwrap(),
        }
    }

    fn reason(term: &DescriptorTerm) -> Option<String> {
        cell_alternatives(term, "outer", &group(), CHILDREN).map(|(key, reason)| {
            assert_eq!(key, &self::key(99), "the error stands at the `|`");
            reason
        })
    }

    #[test]
    fn alternatives_of_a_whole_group_cell_are_refused_below_aliases() {
        let alternatives = or(vec![
            record(&[("flag", int("0", 1))], 10),
            record(&[("mode", int("1", 2))], 20),
        ]);
        let refused = reason(&alternatives).unwrap();
        assert!(
            refused.starts_with("`|` cannot join alternatives of the whole `outer` cell")
                && refused.contains("`Outer { child: A | B, .. }`"),
            "{refused}"
        );
        let aliased = DescriptorTerm::As {
            key: key(3),
            binding_key: key(4),
            name: "o".to_owned(),
            pattern: Box::new(alternatives),
        };
        assert_eq!(reason(&aliased), Some(refused));
        assert_eq!(reason(&record(&[("flag", int("0", 1))], 10)), None);
    }

    #[test]
    fn alternatives_differing_in_one_leaf_child_name_it() {
        let one = or(vec![
            record(&[("flag", int("0", 1)), ("mode", int("5", 2))], 10),
            record(&[("mode", int("5", 3)), ("flag", int("1", 4))], 20),
        ]);
        assert!(
            reason(&one).unwrap().contains(
                "; the alternatives differ only in `flag`: write `Outer { flag: A | B, .. }`"
            ),
            "{one:?}"
        );
        // `_` and an omitted child both match anything.
        let wildcard = or(vec![
            record(
                &[
                    ("flag", int("0", 1)),
                    ("mode", DescriptorTerm::Wildcard { key: key(5) }),
                ],
                10,
            ),
            record(&[("flag", int("1", 4))], 20),
        ]);
        assert!(reason(&wildcard).unwrap().contains("only in `flag`"));
        let two = or(vec![
            record(&[("flag", int("0", 1)), ("mode", int("5", 2))], 10),
            record(&[("flag", int("1", 3)), ("mode", int("6", 4))], 20),
        ]);
        assert!(!reason(&two).unwrap().contains("differ only"));
        // A group child is not a term position, so it gets no hint.
        let group_child = or(vec![
            record(&[("frame", int("0", 1))], 10),
            record(&[("frame", int("1", 2))], 20),
        ]);
        assert!(!reason(&group_child).unwrap().contains("differ only"));
    }
}
