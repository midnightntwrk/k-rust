//! C node construction from the shared semantic outer-placement plans.

use std::collections::BTreeSet;
use std::fmt::Write;

use crate::definition::PartialOrder;
use crate::kast::Sort;
use crate::kompile::{Injectable, Placement, PlacementKind, encode_kore_sort};
use crate::names::BuiltinSort;

use super::quote_c_string;

pub(super) struct CPlacement<'a> {
    pub(super) location: &'a str,
    pub(super) has_location: &'a str,
    pub(super) prefix: &'a str,
    pub(super) subsorts: &'a PartialOrder<Sort>,
    pub(super) sorts: &'a BTreeSet<Sort>,
}

impl CPlacement<'_> {
    /// Emit only the outer transport of `child`; its constructor and chosen sort instances
    /// are already fixed by the grammar action that produced it.
    pub(super) fn write(&self, output: &mut String, plan: &Placement, child: &str) -> String {
        match plan.kind() {
            PlacementKind::Identity => child.into(),
            PlacementKind::Injection(witness) => {
                self.write_injection(output, witness, child, "injection")
            }
            PlacementKind::SingletonK { item } => {
                self.write_singleton(output, item.as_ref(), child)
            }
            PlacementKind::SingletonKInjection { item, sequence } => {
                let singleton = self.write_singleton(output, item.as_ref(), child);
                self.write_injection(output, sequence, &singleton, "sequence")
            }
        }
    }

    fn write_singleton(
        &self,
        output: &mut String,
        item: Option<&Injectable>,
        child: &str,
    ) -> String {
        let item = match item {
            None => child.into(),
            Some(witness) => self.write_injection(output, witness, child, "item"),
        };
        let k = Sort::builtin(BuiltinSort::K);
        let dotk = format!("{}_dotk", self.prefix);
        self.write_node(output, &dotk, "dotk{}", &k, &[]);
        let sequence = format!("{}_kseq", self.prefix);
        self.write_node(output, &sequence, "kseq{}", &k, &[&item, &dotk]);
        sequence
    }

    fn write_injection(
        &self,
        output: &mut String,
        witness: &Injectable,
        child: &str,
        suffix: &str,
    ) -> String {
        let name = format!("{}_{suffix}", self.prefix);
        self.write_node(
            output,
            &name,
            &injection_symbol(witness),
            witness.target(),
            &[child],
        );

        // The exact inner symbol proves both of its endpoints. Collapsing its payload
        // needs a separate witness for the composed pair; a kseq never matches it.
        for source in self.sorts {
            let Some(inner) = Injectable::between(source, witness.source(), self.subsorts) else {
                continue;
            };
            let Some(composed) = Injectable::between(source, witness.target(), self.subsorts)
            else {
                continue;
            };
            writeln!(
                output,
                "  if (!({child})->str && ({child})->nchildren == 1 && strcmp(({child})->symbol, {}) == 0 && strcmp(({child})->sort, {}) == 0 && strcmp(({child})->children[0]->sort, {}) == 0) {{\n    {name}->symbol = {};\n    {name}->children[0] = ({child})->children[0];\n  }}",
                quote_c_string(&injection_symbol(&inner)),
                quote_c_string(&encode_kore_sort(witness.source()).to_string()),
                quote_c_string(&encode_kore_sort(source).to_string()),
                quote_c_string(&injection_symbol(&composed)),
            )
            .expect("writing to a string cannot fail");
        }
        name
    }

    fn write_node(
        &self,
        output: &mut String,
        name: &str,
        symbol: &str,
        sort: &Sort,
        children: &[&str],
    ) {
        writeln!(
            output,
            "  node *{name} = malloc(sizeof(node) + {} * sizeof(node *));\n  {name}->symbol = {};\n  {name}->sort = {};\n  {name}->str = false;\n  {name}->location = {};\n  {name}->hasLocation = {};\n  {name}->nchildren = {};",
            children.len(),
            quote_c_string(symbol),
            quote_c_string(&encode_kore_sort(sort).to_string()),
            self.location,
            self.has_location,
            children.len(),
        )
        .expect("writing to a string cannot fail");
        for (index, child) in children.iter().enumerate() {
            writeln!(output, "  {name}->children[{index}] = {child};")
                .expect("writing to a string cannot fail");
        }
    }
}

pub(super) fn injection_symbol(witness: &Injectable) -> String {
    format!(
        "inj{{{}, {}}}",
        encode_kore_sort(witness.source()),
        encode_kore_sort(witness.target())
    )
}

#[cfg(test)]
mod tests {
    use super::CPlacement;
    use crate::definition::PartialOrder;
    use crate::kast::{Label, Sort, Term};
    use crate::kompile::{Placement, PlacementKind};
    use crate::names::BuiltinSort;
    use std::collections::BTreeSet;

    fn context<'a>(order: &'a PartialOrder<Sort>, sorts: &'a BTreeSet<Sort>) -> CPlacement<'a> {
        CPlacement {
            location: "@$",
            has_location: "1",
            prefix: "placed",
            subsorts: order,
            sorts,
        }
    }

    fn application() -> Term {
        Term::Apply {
            label: Label::new("a"),
            arguments: Vec::new(),
        }
    }

    #[test]
    fn identity_preserves_the_application_without_allocating_a_node() {
        let order = PartialOrder::new(Vec::<(Sort, Sort)>::new()).unwrap();
        let sorts = BTreeSet::from([Sort::new("A")]);
        let plan = Placement::between(&Sort::new("A"), &Sort::new("A"), &order).unwrap();
        assert!(matches!(plan.kind(), PlacementKind::Identity));
        assert_eq!(plan.clone().apply(application()), application());
        let mut output = String::new();
        assert_eq!(
            context(&order, &sorts).write(&mut output, &plan, "child"),
            "child"
        );
        assert!(output.is_empty());
    }

    #[test]
    fn singleton_has_a_kitem_head_and_k_sorted_sequence_nodes() {
        let item = Sort::builtin(BuiltinSort::KItem);
        let k = Sort::builtin(BuiltinSort::K);
        let order = PartialOrder::new([(item.clone(), k.clone())]).unwrap();
        let sorts = BTreeSet::from([item.clone(), k.clone()]);
        let plan = Placement::between(&item, &k, &order).unwrap();
        assert!(matches!(
            plan.kind(),
            PlacementKind::SingletonK { item: None }
        ));
        assert_eq!(
            plan.clone().apply(application()),
            Term::Sequence(vec![application()])
        );
        let mut output = String::new();
        let result = context(&order, &sorts).write(&mut output, &plan, "child");
        assert_eq!(result, "placed_kseq");
        assert!(output.contains("placed_kseq->symbol = \"kseq{}\""));
        assert!(output.contains("placed_dotk->symbol = \"dotk{}\""));
        for node in ["placed_dotk", "placed_kseq"] {
            assert!(output.contains(&format!("{node}->sort = \"SortK{{}}\"")));
            assert!(output.contains(&format!("{node}->str = false")));
            assert!(output.contains(&format!("{node}->location = @$")));
            assert!(output.contains(&format!("{node}->hasLocation = 1")));
        }
        assert!(output.contains("placed_dotk->nchildren = 0"));
        assert!(output.contains("placed_kseq->nchildren = 2"));
        assert!(output.contains("placed_kseq->children[0] = child"));
        assert!(output.contains("placed_kseq->children[1] = placed_dotk"));
        assert!(!output.contains("inj{"));
    }

    #[test]
    fn singleton_injection_embeds_the_item_and_then_the_whole_sequence() {
        let a = Sort::new("A");
        let item = Sort::builtin(BuiltinSort::KItem);
        let k = Sort::builtin(BuiltinSort::K);
        let list = Sort::new("KList");
        let order = PartialOrder::new([
            (a.clone(), item.clone()),
            (item.clone(), k.clone()),
            (k.clone(), list.clone()),
        ])
        .unwrap();
        let sorts = BTreeSet::from([a.clone(), item, k, list.clone()]);
        let plan = Placement::between(&a, &list, &order).unwrap();
        assert!(matches!(
            plan.kind(),
            PlacementKind::SingletonKInjection { item: Some(_), .. }
        ));
        let Term::Apply { label, arguments } = plan.clone().apply(application()) else {
            panic!("the sequence is embedded into KList");
        };
        assert_eq!(label.parameters, [Sort::builtin(BuiltinSort::K), list]);
        let [Term::Sequence(items)] = arguments.as_slice() else {
            panic!("the outer injection contains the whole singleton");
        };
        let [Term::Apply { label, arguments }] = items.as_slice() else {
            panic!("the singleton head is the embedded item");
        };
        assert_eq!(label.parameters, [a, Sort::builtin(BuiltinSort::KItem)]);
        assert_eq!(arguments, &[application()]);
        let mut output = String::new();
        assert_eq!(
            context(&order, &sorts).write(&mut output, &plan, "child"),
            "placed_sequence"
        );
        assert!(output.contains("placed_item->symbol = \"inj{SortA{}, SortKItem{}}\""));
        assert!(output.contains("placed_item->sort = \"SortKItem{}\""));
        assert!(output.contains("placed_kseq->children[0] = placed_item"));
        assert!(output.contains("placed_sequence->symbol = \"inj{SortK{}, SortKList{}}\""));
        assert!(output.contains("placed_sequence->children[0] = placed_kseq"));
        assert!(!output.contains("inj{SortA{}, SortKList{}}"));
        assert!(!output.contains("injSymbol"));
    }

    #[test]
    fn flattening_dispatch_requires_inner_and_composed_witnesses() {
        let a = Sort::new("A");
        let b = Sort::new("B");
        let c = Sort::new("C");
        let k = Sort::builtin(BuiltinSort::K);
        let item = Sort::builtin(BuiltinSort::KItem);
        let order = PartialOrder::new([
            (a.clone(), b.clone()),
            (b.clone(), c.clone()),
            (item.clone(), k.clone()),
            (k.clone(), c.clone()),
        ])
        .unwrap();
        let sorts = BTreeSet::from([a, b.clone(), c.clone(), item, k.clone()]);
        let plan = Placement::between(&b, &c, &order).unwrap();
        assert!(matches!(plan.kind(), PlacementKind::Injection(_)));
        let mut output = String::new();
        assert_eq!(
            context(&order, &sorts).write(&mut output, &plan, "child"),
            "placed_injection"
        );
        assert!(output.contains("strcmp((child)->symbol, \"inj{SortA{}, SortB{}}\") == 0"));
        assert!(output.contains("placed_injection->symbol = \"inj{SortA{}, SortC{}}\""));
        assert!(output.contains("placed_injection->children[0] = (child)->children[0]"));
        assert!(!output.contains("injSymbol"));

        let plan = Placement::between(&k, &c, &order).unwrap();
        assert!(matches!(plan.kind(), PlacementKind::Injection(_)));
        output.clear();
        context(&order, &sorts).write(&mut output, &plan, "child");
        assert!(output.contains("placed_injection->children[0] = child"));
        assert!(!output.contains("if ("));
        assert!(!output.contains("kseq{}"));
        assert!(!output.contains("inj{SortKItem{}, SortK{}}"));
    }
}
