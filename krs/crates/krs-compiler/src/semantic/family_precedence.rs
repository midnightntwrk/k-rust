//! Whole-theory check that a constructor family without a precedence chain
//! needs none (`krs::analysis::missing-precedence-chain`).
//!
//! A family's `#[k::precedence]` chain relates only the family's own
//! variants, and its priority and associativity relations restrict only a
//! direct child at the first or last item of its parent (C7). So a chain can
//! change how a family parses exactly when one of its variants can sit
//! directly at the edge of another: when some variant's template begins or
//! ends with a field whose sort admits the family's sort. Whether a sort
//! admits another is a fact of the assembled definition, whose subsorts any
//! package can extend, so this check runs here and not when the macro
//! expands. A family that needs no chain may omit it; one that needs it must
//! rank every variant, which the macro checks once the chain is present.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use krs_ir::{BuiltinSort, GrammarProductionItemKind, ProductionAttribute, StableItemId};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticProductionAttribute, SemanticSortRef,
};

use super::error::DescriptorLoweringError;
use super::overload::sort_name;

/// Rejects every family that has no production group (no chain) while one
/// of its variants can sit at the edge of another.
pub(super) fn check_chainless_families(
    modules: &[SemanticModule],
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    let mut families = BTreeMap::<FamilyKey<'_>, Vec<&SemanticProduction>>::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        if let Some(key) = family_key(production.id())
            && !is_list_production(production)
        {
            families.entry(key).or_default().push(production);
        }
    }
    for (key, productions) in &families {
        if productions
            .iter()
            .any(|production| has(production, is_group))
        {
            continue;
        }
        let edges = productions
            .iter()
            .filter(|production| has(production, is_format))
            .filter_map(|production| {
                let reasons = edge_reasons(production, parents);
                (!reasons.is_empty()).then_some((*production, reasons))
            })
            .collect::<Vec<_>>();
        let Some((first, _)) = edges.first() else {
            continue;
        };
        let variants = edges
            .iter()
            .map(|(production, reasons)| {
                format!(
                    "`{}` {}",
                    production.id().item_name(),
                    reasons.join(" and ")
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        let family = key.enum_name;
        return Err(DescriptorLoweringError::MissingPrecedenceChain {
            reason: format!(
                "`{family}` needs a `#[k::precedence(..)]` chain: {variants}, so one `{family}` production can sit directly at the edge of another, where a chain decides how they parse; rank every variant, for example `#[k::precedence((A) > left (B, C))]`, or list them all in one bare tier to accept every nesting"
            ),
            range: first.origin().origin().exact_authored_range().map(Box::new),
        });
    }
    Ok(())
}

/// One enum family: its variants share the package, module, and enum.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FamilyKey<'a> {
    package: &'a krs_ir::PackageId,
    module_path: &'a [String],
    enum_name: &'a str,
}

fn family_key(id: &StableItemId) -> Option<FamilyKey<'_>> {
    let enum_name = id
        .disambiguator()
        .strip_prefix(krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX)?;
    Some(FamilyKey {
        package: id.package(),
        module_path: id.module_path(),
        enum_name,
    })
}

fn has(
    production: &SemanticProduction,
    predicate: fn(&SemanticProductionAttribute) -> bool,
) -> bool {
    production.attributes().iter().any(predicate)
}

const fn is_group(attribute: &SemanticProductionAttribute) -> bool {
    matches!(attribute, ProductionAttribute::Group { .. })
}

/// A variant with a `#[k::syntax]` template always carries its format; one
/// without a template gets no group even from a chain, so it is outside what
/// a chain governs.
const fn is_format(attribute: &SemanticProductionAttribute) -> bool {
    matches!(attribute, ProductionAttribute::Format { .. })
}

fn is_list_production(production: &SemanticProduction) -> bool {
    has(production, |attribute| {
        matches!(
            attribute,
            ProductionAttribute::ListCons { .. } | ProductionAttribute::ListTerminator { .. }
        )
    })
}

/// Why the production's first or last item admits its own result sort, one
/// reason per edge.
fn edge_reasons(
    production: &SemanticProduction,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Vec<String> {
    let items = production.items();
    let family_sort = production.result_sort();
    let mut edges = Vec::new();
    if let Some(first) = items.first() {
        edges.push(("begins", first));
    }
    if items.len() > 1
        && let Some(last) = items.last()
    {
        edges.push(("ends", last));
    }
    edges
        .into_iter()
        .filter_map(|(side, item)| {
            let GrammarProductionItemKind::NonTerminal { field, sort } = item.kind() else {
                return None;
            };
            let why = admits(sort, family_sort, parents)?;
            Some(format!(
                "{side} with `{}: {}` ({why})",
                field.as_str(),
                sort_name(sort)
            ))
        })
        .collect()
}

/// Whether a field of sort `field` admits a term of sort `family`, and why.
/// Every user sort is a `KItem` in the emitted K, whether or not KRS
/// declares that parent, so `KItem` and `K` admit every sort.
fn admits(
    field: &SemanticSortRef,
    family: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Option<String> {
    if field == family {
        return Some("the family's own sort".to_owned());
    }
    if is_top_sort(field) {
        return Some(format!("`{}` admits every sort", sort_name(field)));
    }
    subsort_path(family, field, parents).map(|path| {
        format!(
            "through the subsorts {}",
            path.iter()
                .map(|sort| format!("`{}`", sort_name(sort)))
                .collect::<Vec<_>>()
                .join(" < ")
        )
    })
}

fn is_top_sort(sort: &SemanticSortRef) -> bool {
    match sort {
        SemanticSortRef::Builtin(BuiltinSort::KSequence) => true,
        SemanticSortRef::Declared(id) => {
            id.item_kind() == krs_ir::ItemKind::Sort
                && id.item_name() == "KItem"
                && id.package().k_namespace() == "KRS-FRAMEWORK"
                && id.package().cargo_name() == "krs"
                && id.package().cargo_source() == "framework"
        }
        _ => false,
    }
}

/// The shortest declared subsort chain from `from` up to `to`, both included.
fn subsort_path(
    from: &SemanticSortRef,
    to: &SemanticSortRef,
    parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Option<Vec<SemanticSortRef>> {
    let mut previous = BTreeMap::<&SemanticSortRef, &SemanticSortRef>::new();
    let mut pending = VecDeque::from([from]);
    while let Some(sort) = pending.pop_front() {
        for parent in parents.get(sort).into_iter().flatten() {
            if parent == from || previous.contains_key(parent) {
                continue;
            }
            previous.insert(parent, sort);
            if parent == to {
                let mut path = vec![to.clone()];
                let mut current = to;
                while let Some(&below) = previous.get(current) {
                    path.push(below.clone());
                    current = below;
                }
                path.reverse();
                return Some(path);
            }
            pending.push_back(parent);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{
        BuiltinSort, ItemKind, ModuleId, NodeOrigin, PackageId, ProductionAttribute,
        ProductionFieldId, ProductionGroupId, StableItemId, testing,
    };
    use krs_ir_levels::{
        SemanticModule, SemanticProduction, SemanticProductionItem, SemanticSort, SemanticSortRef,
    };

    use super::check_chainless_families;

    fn package() -> PackageId {
        testing::package("KRS-FAMILY", "family")
    }

    fn sort(name: &str) -> SemanticSortRef {
        SemanticSortRef::Declared(testing::item_in(package(), "family", name, ItemKind::Sort))
    }

    fn framework_k_item() -> SemanticSortRef {
        let framework = testing::package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework");
        SemanticSortRef::Declared(testing::item_in(framework, "krs", "KItem", ItemKind::Sort))
    }

    fn origin(key: &str) -> NodeOrigin {
        testing::origin_in(
            key,
            package(),
            "src/lib.rs",
            testing::digest_with("5".repeat(64)),
            0,
            1,
        )
    }

    /// One template item: `"text"` is a terminal, `name: Sort` a field.
    enum Item<'a> {
        T(&'a str),
        F(&'a str, SemanticSortRef),
    }

    /// Variant `name` of enum `family`, constructing `result`, with the given
    /// template; `group` names its chain tier, and `template` false gives the
    /// shape of a variant without `#[k::syntax]` (no format).
    fn variant(
        family: &str,
        name: &str,
        result: &SemanticSortRef,
        items: Vec<Item<'_>>,
        group: Option<&str>,
        template: bool,
    ) -> SemanticProduction {
        let id = StableItemId::new(
            package(),
            ["family"],
            name,
            ItemKind::Constructor,
            format!("{}{family}", krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX),
        )
        .unwrap();
        let items = items
            .into_iter()
            .enumerate()
            .map(|(index, item)| match item {
                Item::T(text) => {
                    SemanticProductionItem::terminal(origin(&format!("{name}.{index}")), text)
                        .unwrap()
                }
                Item::F(field, sort) => SemanticProductionItem::non_terminal(
                    origin(&format!("{name}.{index}")),
                    ProductionFieldId::new(field).unwrap(),
                    sort,
                ),
            })
            .collect();
        let mut attributes = Vec::new();
        if template {
            attributes.push(ProductionAttribute::Format {
                origin: origin(&format!("{name}.format")),
                fragments: vec![krs_ir::FormatFragment::Item(1)],
            });
        }
        if let Some(group) = group {
            attributes.push(ProductionAttribute::Group {
                origin: origin(&format!("{name}.group")),
                group: ProductionGroupId::new(group).unwrap(),
            });
        }
        SemanticProduction::new(origin(name), id, result.clone(), items, attributes).unwrap()
    }

    fn check(
        productions: Vec<SemanticProduction>,
        subsorts: &[(&str, &str)],
    ) -> Result<(), String> {
        let module = SemanticModule::new(
            origin("module"),
            ModuleId::new("KRS-FAMILY").unwrap(),
            vec![],
            ["Exp", "Atom", "Instr", "Operand", "AluOp"]
                .into_iter()
                .map(|name| {
                    SemanticSort::new(
                        origin(name),
                        testing::item_in(package(), "family", name, ItemKind::Sort),
                    )
                })
                .collect(),
            vec![],
            productions,
            vec![],
            vec![],
            None,
            vec![],
        );
        let mut parents = BTreeMap::<_, BTreeSet<_>>::new();
        for (sub, sup) in subsorts {
            parents.entry(sort(sub)).or_default().insert(sort(sup));
        }
        check_chainless_families(&[module], &parents).map_err(|error| error.to_string())
    }

    fn add(group: Option<&str>) -> SemanticProduction {
        variant(
            "Op",
            "Add",
            &sort("Exp"),
            vec![
                Item::F("lhs", sort("Exp")),
                Item::T("+"),
                Item::F("rhs", sort("Exp")),
            ],
            group,
            true,
        )
    }

    fn literal() -> SemanticProduction {
        variant(
            "Op",
            "Lit",
            &sort("Exp"),
            vec![
                Item::T("lit"),
                Item::T("("),
                Item::F("value", sort("Exp")),
                Item::T(")"),
            ],
            None,
            true,
        )
    }

    #[test]
    fn an_infix_variant_over_the_family_sort_needs_a_chain() {
        let error = check(vec![literal(), add(None)], &[]).unwrap_err();
        assert_eq!(
            error,
            "`Op` needs a `#[k::precedence(..)]` chain: `Add` begins with `lhs: Exp` (the family's own sort) and ends with `rhs: Exp` (the family's own sort), so one `Op` production can sit directly at the edge of another, where a chain decides how they parse; rank every variant, for example `#[k::precedence((A) > left (B, C))]`, or list them all in one bare tier to accept every nesting"
        );
    }

    #[test]
    fn a_chain_satisfies_the_check_even_with_one_bare_tier() {
        let mut literal = literal();
        literal = SemanticProduction::new(
            literal.origin().clone(),
            literal.id().clone(),
            literal.result_sort().clone(),
            literal.items().to_vec(),
            vec![ProductionAttribute::Group {
                origin: origin("Lit.group"),
                group: ProductionGroupId::new("op_tier0").unwrap(),
            }],
        )
        .unwrap();
        assert_eq!(check(vec![literal, add(Some("op_tier0"))], &[]), Ok(()));
    }

    #[test]
    fn a_prefix_only_variant_needs_a_chain() {
        let negate = variant(
            "Op",
            "Neg",
            &sort("Exp"),
            vec![Item::T("-"), Item::F("value", sort("Exp"))],
            None,
            true,
        );
        let error = check(vec![negate], &[]).unwrap_err();
        assert!(
            error.contains("`Neg` ends with `value: Exp` (the family's own sort)"),
            "{error}"
        );
    }

    #[test]
    fn an_edge_reached_through_a_subsort_names_the_subsort_chain() {
        let wrap = variant(
            "Atoms",
            "Wrap",
            &sort("Atom"),
            vec![Item::T("wrap"), Item::F("inner", sort("Exp"))],
            None,
            true,
        );
        let error = check(
            vec![wrap.clone()],
            &[("Atom", "Operand"), ("Operand", "Exp")],
        )
        .unwrap_err();
        assert!(
            error.contains(
                "`Wrap` ends with `inner: Exp` (through the subsorts `Atom` < `Operand` < `Exp`)"
            ),
            "{error}"
        );
        assert_eq!(check(vec![wrap], &[]), Ok(()));
    }

    #[test]
    fn k_item_and_k_fields_admit_every_sort() {
        let then = variant(
            "Steps",
            "Then",
            &sort("Instr"),
            vec![
                Item::F("first", sort("Operand")),
                Item::T(";"),
                Item::F("rest", framework_k_item()),
            ],
            None,
            true,
        );
        let error = check(vec![then], &[]).unwrap_err();
        assert!(
            error.contains("`Then` ends with `rest: KItem` (`KItem` admits every sort)"),
            "{error}"
        );
        let sequence = variant(
            "Steps",
            "Seq",
            &sort("Instr"),
            vec![
                Item::F("first", SemanticSortRef::Builtin(BuiltinSort::KSequence)),
                Item::T("then"),
            ],
            None,
            true,
        );
        let error = check(vec![sequence], &[]).unwrap_err();
        assert!(
            error.contains("`Seq` begins with `first: K` (`K` admits every sort)"),
            "{error}"
        );
    }

    #[test]
    fn edges_of_unrelated_sorts_and_inner_fields_need_no_chain() {
        let alu = variant(
            "Instruction",
            "Alu8",
            &sort("Instr"),
            vec![
                Item::F("op", sort("AluOp")),
                Item::T("a"),
                Item::T(","),
                Item::F("src", sort("Operand")),
            ],
            None,
            true,
        );
        let unimplemented = variant(
            "Instruction",
            "Unimplemented",
            &sort("Instr"),
            vec![
                Item::T("#unimplemented"),
                Item::T("("),
                Item::F("op", sort("Instr")),
                Item::T(")"),
            ],
            None,
            true,
        );
        let nop = variant(
            "Instruction",
            "Nop",
            &sort("Instr"),
            vec![Item::T("nop")],
            None,
            true,
        );
        assert_eq!(check(vec![alu, unimplemented, nop], &[]), Ok(()));
    }

    #[test]
    fn a_variant_without_a_template_is_outside_what_a_chain_governs() {
        let raw = variant(
            "Op",
            "Raw",
            &sort("Exp"),
            vec![Item::T("Raw"), Item::F("value", sort("Exp"))],
            None,
            false,
        );
        assert_eq!(check(vec![raw], &[]), Ok(()));
    }

    #[test]
    fn syntax_list_productions_are_not_checked() {
        let cons = StableItemId::new(
            package(),
            ["family"],
            "ExpsCons",
            ItemKind::Constructor,
            format!("{}Exps", krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX),
        )
        .unwrap();
        let nil = testing::item_in(package(), "family", "ExpsNil", ItemKind::Constructor);
        let cons = SemanticProduction::new(
            origin("cons"),
            cons,
            sort("Exp"),
            vec![
                SemanticProductionItem::non_terminal(
                    origin("head"),
                    ProductionFieldId::new("head").unwrap(),
                    sort("Exp"),
                ),
                SemanticProductionItem::terminal(origin("separator"), ",").unwrap(),
                SemanticProductionItem::non_terminal(
                    origin("tail"),
                    ProductionFieldId::new("tail").unwrap(),
                    sort("Exp"),
                ),
            ],
            vec![
                ProductionAttribute::Format {
                    origin: origin("cons.format"),
                    fragments: vec![krs_ir::FormatFragment::Item(1)],
                },
                ProductionAttribute::ListCons {
                    origin: origin("list"),
                    separator: ",".to_owned(),
                    non_empty: false,
                    terminator: nil,
                },
            ],
        )
        .unwrap();
        assert_eq!(check(vec![cons], &[]), Ok(()));
    }
}
