//! The check, in builds with debug assertions, that the productions an inner grammar generated
//! respect the roles of their sorts.
//!
//! A rule or configuration grammar adds productions of its own next to the visible ones: per-sort
//! subsorts, casts and brackets, cell productions, the rule scaffolding and the kernel syntax.
//! Their sorts are chosen by code, not declared by the definition, so a generator that picks a
//! sort of the wrong role (a production's formal parameter, a placeholder spelled by hand, a
//! scaffolding sort as a declared operand) builds a grammar that still parses but gives inference
//! a position whose sort means something else. The check reads the finished grammar and panics on
//! such a production; it changes neither the grammar nor a result, and it does not exist in a
//! build without debug assertions.
//!
//! The check reads the grammar's semantic subsort relation, in which scaffolding sorts do stand:
//! `KBott ::= #KVariable` makes a variable a bottom term, and `#Rule<S> ::= S` makes every `S` a
//! rule pattern of sort `S`. Those pairs are exactly what G2 and G3 read, through the order of the
//! relation; G0 asserts first that the relation is acyclic, so that order always exists.

use std::iter;

use k_rust_kore::measure;

use crate::definition::production_kind::mentions_parameter;
use crate::definition::{PartialOrder, ProductionItem};
use crate::inner::sort_universe::SortUniverse;
use crate::kast::sort_role::KernelSort;
use crate::kast::{Sort, SortRole};

use super::grammar::render_parsing_production;
use super::parametric::substitute_sort;
use super::scanner::Item;
use super::{Grammar, Production};

impl Grammar {
    /// Panic, naming the rule, the production and the sort, when a production this grammar
    /// generated (one without a source production), or a parametric instance's substitution,
    /// violates the sort-role invariant, or when the grammar's semantic subsort relation is cyclic:
    ///
    /// - G0 acyclic: the semantic subsort relation has no cycle. The panic names each step of the
    ///   cycle, marked `(generated)` when a generated unlabeled unary production states it and
    ///   `(declared)` otherwise (a pair a generated production also states is marked generated).
    /// - G1 classified: every sort of its result and of its nonterminal items, declared or
    ///   recognized, is a member or synonym alias of `universe`, a kernel sort, a scaffolding
    ///   sort, or a registered placeholder. Every parametric instance binds exactly its formal
    ///   parameters and writes the substituted sort at each parameter-dependent result or item;
    ///   every such written sort is classified too.
    /// - G2 no bottom operand: a labeled production declares no nonterminal item at a sort at or
    ///   below `KBott`. No term sort is below a bottom sort, so a term standing there, a variable
    ///   above all, has no sort.
    /// - G3 no wrapper operand: a labeled production whose result is a defined sort declares no
    ///   nonterminal item at a wrapper, a scaffolding or non-term kernel sort with a term sort
    ///   strictly below it. The declared sort of an item is the sort inference assigns to the
    ///   term there, and an anonymous variable takes it exactly, so an item declared at a wrapper
    ///   types its term by a sort that denotes no set of terms; the wrapper may only be the sort
    ///   the position is recognized at.
    ///
    /// A definition's own productions are judged by the definition checks. The sorts that a
    /// concretized instance's substitution writes are chosen by the parametric plan, so G1 checks
    /// those sorts on every instance. Every other sort of an instance is the definition's.
    /// The operand sorts that generated productions copy from the definition (a cell body, the
    /// injected `<generatedCounter>` cell) are universe members because every unbound operand
    /// sort of a visible production is one.
    ///
    /// G2 and G3 read the order of the semantic subsort relation, which G0 guarantees. Every
    /// cycle a definition can cause is ruled out before this point, on every path that builds a
    /// rule or configuration grammar: the builder first rejects the definition sentences it is
    /// built from when their declared subsorts contradict the positions K fixes for its kernel
    /// sorts (`config::reject_kernel_position_contradiction`, the contradiction the load also
    /// reports as a diagnostic), the grammar constructor rejects a cycle among the definition's own
    /// productions, and the per-member generators state only the kernel positions a sort's role
    /// grants, by const assertion. A cycle here therefore needs a generated pair outside those
    /// rules, which is a compiler defect, so every labeled generated production is checked against
    /// G2 and G3.
    pub(in crate::inner) fn assert_generated_sort_roles(&self, universe: &SortUniverse) {
        // The check's own order, built outside the grammar's cache and uncounted: the check is
        // not work of the grammar, so it neither changes the work counters nor builds the order
        // inference would otherwise build (and count) on its first parse.
        let order = match measure::without_counting(|| {
            PartialOrder::new(self.subsort_relations.iter().cloned())
        }) {
            Ok(order) => order,
            Err(cycle) => panic!(
                "G0: the semantic subsort relation is cyclic: {}",
                self.render_cycle_steps(&cycle.path),
            ),
        };
        for production in &self.productions {
            let Some(origin) = &production.parametric_origin else {
                continue;
            };
            assert!(
                origin
                    .substitution
                    .keys()
                    .all(|parameter| origin.parameters.contains(parameter))
                    && origin
                        .parameters
                        .iter()
                        .all(|parameter| origin.substitution.contains_key(parameter)),
                "G1: the parametric instance `{}` has substitution {:?}, which does not bind \
                 exactly its parameters {:?}",
                render_parsing_production(production),
                origin.substitution,
                origin.parameters,
            );
            let formal_operands = origin.items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            });
            debug_assert_eq!(
                formal_operands.clone().count(),
                declared_operands(production).count()
            );
            for (formal, sort) in iter::once((&origin.result, &production.result))
                .chain(formal_operands.zip(declared_operands(production)))
            {
                if mentions_parameter(formal, &origin.parameters) {
                    assert_eq!(
                        *sort,
                        substitute_sort(formal, &origin.substitution),
                        "G1: the parametric instance `{}` writes `{sort}` for `{formal}`, which \
                         differs from its substitution {:?}",
                        render_parsing_production(production),
                        origin.substitution,
                    );
                    assert!(
                        self.is_classified(sort, universe),
                        "G1: the parametric instance `{}` writes `{sort}` for `{formal}`, which \
                         is neither a sort of the grammar's universe nor a kernel, scaffolding \
                         or registered placeholder sort (substitution {:?})",
                        render_parsing_production(production),
                        origin.substitution,
                    );
                }
            }
        }
        let bottom = KernelSort::KBott.sort();
        for production in self
            .productions
            .iter()
            .filter(|production| production.source_production.is_none())
        {
            let recognized = production
                .item_sort_ids
                .iter()
                .flatten()
                .map(|sort_id| &self.sorts[*sort_id]);
            for sort in iter::once(&production.result)
                .chain(declared_operands(production))
                .chain(recognized)
            {
                assert!(
                    self.is_classified(sort, universe),
                    "G1: the generated production `{}` mentions `{sort}`, which is neither a sort \
                     of the grammar's universe nor a kernel, scaffolding or registered placeholder \
                     sort",
                    render_parsing_production(production),
                );
            }
            if production.label.is_none() {
                continue;
            }
            for operand in declared_operands(production) {
                assert!(
                    !order.less_than_eq(operand, &bottom),
                    "G2: the generated labeled production `{}` declares an operand at `{operand}`, \
                     which is at or below `KBott`, so a term there has no sort",
                    render_parsing_production(production),
                );
                if production.result.role() == SortRole::Defined
                    && let Some(term_sort) = term_sort_below_wrapper(&order, operand)
                {
                    panic!(
                        "G3: the generated labeled production `{}` of the defined sort `{}` \
                         declares an operand at the wrapper `{operand}`, which derives the term \
                         sort `{term_sort}` but denotes no set of terms",
                        render_parsing_production(production),
                        production.result,
                    );
                }
            }
        }
    }

    /// G0: the steps `A < B` of `path`, a cycle whose last sort is its first, each marked
    /// `(generated)` when a generated unlabeled production `B ::= A` states it and `(declared)`
    /// otherwise. `(declared)` means only that no generated unlabeled unary production states the
    /// pair: a pair a generator inserts into the relation without a production (a user list's
    /// element below its non-empty list) is marked declared.
    fn render_cycle_steps(&self, path: &[Sort]) -> String {
        path.iter()
            .zip(path.iter().skip(1))
            .map(|(lesser, greater)| {
                let provenance = if self.generates_subsort(lesser, greater) {
                    "generated"
                } else {
                    "declared"
                };
                format!("{lesser} < {greater} ({provenance})")
            })
            .collect::<Vec<_>>()
            .join("; ")
    }

    /// G0: whether a generated unlabeled production `greater ::= lesser` states the pair.
    fn generates_subsort(&self, lesser: &Sort, greater: &Sort) -> bool {
        self.productions.iter().any(|production| {
            production.source_production.is_none()
                && production.label.is_none()
                && production.result == *greater
                && matches!(
                    production.items.as_slice(),
                    [Item::NonTerminal(child)] if child == lesser
                )
        })
    }

    /// G1: whether `sort` has a role a generated production may give it.
    fn is_classified(&self, sort: &Sort, universe: &SortUniverse) -> bool {
        universe.admits(sort)
            || self.placeholders.contains_key(sort)
            || match sort.role() {
                SortRole::Kernel(_) => sort.parameters.is_empty(),
                SortRole::Scaffolding => true,
                SortRole::RigidVariable | SortRole::Nat | SortRole::Defined => false,
            }
    }
}

/// The declared sorts of the nonterminal items of `production`.
fn declared_operands(production: &Production) -> impl Iterator<Item = &Sort> {
    production.items.iter().filter_map(|item| match item {
        Item::NonTerminal(sort) => Some(sort),
        Item::Terminal(_) | Item::Regex { .. } => None,
    })
}

/// G3: a term sort strictly below `sort` when `sort` is a wrapper, a scaffolding sort or a kernel
/// sort that is not a sort of `K` terms.
fn term_sort_below_wrapper<'o>(order: &'o PartialOrder<Sort>, sort: &Sort) -> Option<&'o Sort> {
    let wrapper = match sort.role() {
        SortRole::Scaffolding => true,
        role @ SortRole::Kernel(_) => !role.is_k_term_sort(),
        SortRole::RigidVariable | SortRole::Nat | SortRole::Defined => false,
    };
    if !wrapper {
        return None;
    }
    order
        .elements()
        .find(|lesser| order.less_than(lesser, sort) && lesser.role().is_k_term_sort())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::definition::{Attributes, ProductionItem, Sentence};
    use crate::inner::sort_universe::SortUniverse;
    use crate::kast::{Label, Sort};

    use super::super::scanner::Item;
    use super::super::{Grammar, ParametricOrigin};

    fn nonterminal(sort: Sort) -> ProductionItem {
        ProductionItem::NonTerminal { sort, name: None }
    }

    fn terminal(text: &str) -> ProductionItem {
        ProductionItem::Terminal(text.into())
    }

    fn production(parameters: Vec<Sort>, sort: Sort, items: Vec<ProductionItem>) -> Sentence {
        Sentence::Production {
            label: None,
            parameters,
            sort,
            items,
            attributes: Attributes::default(),
        }
    }

    fn syntax_sort(parameters: Vec<Sort>, sort: Sort) -> Sentence {
        Sentence::SyntaxSort {
            parameters,
            sort,
            attributes: Attributes::default(),
        }
    }

    fn mint(parameter: &str) -> Sort {
        Sort::with_parameters("MInt", vec![Sort::new(parameter)])
    }

    /// A prelude-free module: `Exp`, a cell sort `KCell`, the parametric `MInt{W}` with its
    /// instance `MInt{64}`, and an ML-style production whose result is its own formal parameter
    /// `Sort`.
    fn module() -> Vec<Sentence> {
        let binder = Sort::new("Sort");
        vec![
            production(Vec::new(), Sort::new("Exp"), vec![terminal("e")]),
            syntax_sort(Vec::new(), Sort::new("KCell")),
            syntax_sort(vec![Sort::new("W")], mint("W")),
            syntax_sort(Vec::new(), mint("64")),
            production(vec![binder.clone()], binder, vec![terminal("#Top")]),
        ]
    }

    /// The module's grammar and universe, before any generated production is added.
    fn grammar_and_universe() -> (Grammar, SortUniverse) {
        let sentences = module();
        let visible = sentences.iter().collect::<Vec<_>>();
        let grammar = Grammar::from_configuration_sentences(visible.iter().copied())
            .expect("the module's grammar builds");
        (grammar, SortUniverse::new(&visible))
    }

    /// Add the generated unary production `result ::= child`.
    fn add_subsort(grammar: &mut Grammar, result: Sort, child: Sort) {
        grammar
            .add(result, vec![nonterminal(child)], None, false, true)
            .expect("the subsort is added");
    }

    fn add_instance(grammar: &mut Grammar, slot: Sort, origin: ParametricOrigin) {
        let source = grammar
            .productions
            .iter()
            .find_map(|production| production.source_production)
            .expect("the module has a source production");
        grammar
            .add(
                Sort::new("Int"),
                vec![
                    terminal("inner"),
                    terminal("("),
                    nonterminal(slot),
                    terminal(")"),
                ],
                None,
                false,
                false,
            )
            .expect("the instance is added");
        let instance = grammar.productions.last_mut().unwrap();
        instance.parametric_origin = Some(origin);
        instance.source_production = Some(source);
    }

    fn instance_origin(parameters: Vec<Sort>, result: Sort, slot: Sort) -> ParametricOrigin {
        ParametricOrigin {
            label: None,
            parameters,
            result,
            items: vec![
                terminal("inner"),
                terminal("("),
                nonterminal(slot),
                terminal(")"),
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::new(),
        }
    }

    fn instance_grammar_and_universe() -> (Grammar, SortUniverse) {
        let mut sentences = module();
        sentences.push(syntax_sort(Vec::new(), Sort::new("Int")));
        let visible = sentences.iter().collect::<Vec<_>>();
        let grammar = Grammar::from_configuration_sentences(visible.iter().copied())
            .expect("the module's grammar builds");
        (grammar, SortUniverse::new(&visible))
    }

    #[test]
    #[should_panic(expected = "writes `MInt{Int}` for `MInt{T}`")]
    fn an_instance_that_writes_an_undeclared_instance_fails_g1() {
        let (mut grammar, universe) = instance_grammar_and_universe();
        let parameter = Sort::new("T");
        let mut origin = instance_origin(vec![parameter.clone()], parameter.clone(), mint("T"));
        origin.substitution.insert(parameter, Sort::new("Int"));
        assert!(!universe.admits(&mint("Int")));
        add_instance(&mut grammar, mint("Int"), origin);

        grammar.assert_generated_sort_roles(&universe);
    }

    #[test]
    #[should_panic(expected = "which does not bind exactly its parameters")]
    fn an_instance_with_a_partial_substitution_fails_g1() {
        let (mut grammar, universe) = instance_grammar_and_universe();
        let parameter = Sort::new("S");
        let mut origin = instance_origin(
            vec![parameter.clone(), Sort::new("W")],
            parameter.clone(),
            mint("W"),
        );
        origin.substitution.insert(parameter, Sort::new("Int"));
        add_instance(&mut grammar, mint("W"), origin);

        grammar.assert_generated_sort_roles(&universe);
    }

    #[test]
    #[should_panic(expected = "which differs from its substitution")]
    fn an_instance_that_disagrees_with_its_substitution_fails_g1() {
        let (mut grammar, universe) = instance_grammar_and_universe();
        let parameter = Sort::new("T");
        let mut origin = instance_origin(vec![parameter.clone()], parameter.clone(), mint("T"));
        origin.substitution.insert(parameter, Sort::new("Int"));
        assert!(universe.admits(&mint("64")));
        add_instance(&mut grammar, mint("64"), origin);

        grammar.assert_generated_sort_roles(&universe);
    }

    #[test]
    fn an_instance_at_sorts_of_the_grammar_passes_the_check() {
        let (mut grammar, universe) = instance_grammar_and_universe();
        assert!(universe.admits(&Sort::new("Int")));
        let parameter = Sort::new("T");
        let mut origin = instance_origin(
            vec![parameter.clone()],
            parameter.clone(),
            parameter.clone(),
        );
        origin.substitution.insert(parameter, Sort::new("Int"));
        add_instance(&mut grammar, Sort::new("Int"), origin);

        grammar.assert_generated_sort_roles(&universe);
    }

    /// The control: the productions of the four demonstrations with each sort at its role are
    /// silent, and so is the recognition bridge `MInt{K} ::= MInt{64}` that the parametric plan
    /// generates into its registered placeholder.
    #[test]
    fn generated_productions_at_their_roles_pass_the_check() {
        let (mut grammar, universe) = grammar_and_universe();
        assert!(grammar.placeholders.contains_key(&mint("K")));
        assert!(grammar.productions.iter().any(|production| {
            production.source_production.is_none()
                && production.result == mint("K")
                && matches!(production.items.as_slice(), [Item::NonTerminal(child)] if *child == mint("64"))
        }));
        add_subsort(&mut grammar, Sort::new("KItem"), Sort::new("Exp"));
        add_subsort(&mut grammar, Sort::new("KItem"), mint("64"));
        add_subsort(&mut grammar, Sort::new("KBott"), Sort::new("#KVariable"));
        add_subsort(&mut grammar, Sort::new("#RuleExp"), Sort::new("Exp"));
        grammar
            .add(
                Sort::new("#RuleExp"),
                vec![
                    nonterminal(Sort::new("Exp")),
                    terminal("#as"),
                    nonterminal(Sort::new("Exp")),
                ],
                Some(Label::new("#KAs")),
                false,
                false,
            )
            .expect("the alias is added");
        add_subsort(&mut grammar, Sort::new("#RuleK"), Sort::new("K"));
        grammar
            .add(
                Sort::new("KCell"),
                vec![
                    terminal("<k>"),
                    nonterminal(Sort::new("K")),
                    terminal("</k>"),
                ],
                Some(Label::new("<k>")),
                false,
                false,
            )
            .expect("the cell is added");

        grammar.assert_generated_sort_roles(&universe);
    }

    /// 86a21b90: the per-sort generators ranged over a collection that kept the formal parameter
    /// `Sort` of an ML-style production, and so added `KItem ::= Sort`.
    #[test]
    #[should_panic(
        expected = "G1: the generated production `syntax KItem ::= Sort` mentions `Sort`"
    )]
    fn a_kitem_subsort_of_a_binder_fails_g1() {
        let (mut grammar, universe) = grammar_and_universe();

        add_subsort(&mut grammar, Sort::new("KItem"), Sort::new("Sort"));

        grammar.assert_generated_sort_roles(&universe);
    }

    /// dfaad153: the parametric bridge into the placeholder `MInt{K}` was added through a sort
    /// spelled by hand, which the grammar never registered and no sentence declares. The grammar
    /// is built without the instance declaration, so its parametric plan registers no placeholder
    /// and adds no bridge of its own, as in a grammar built before placeholders were registered;
    /// `MInt{64}` stays a member of the module's universe, so the placeholder is the only sort
    /// out of role.
    #[test]
    #[should_panic(
        expected = "G1: the generated production `syntax MInt{K} ::= MInt{64}` mentions `MInt{K}`"
    )]
    fn an_unregistered_placeholder_bridge_fails_g1() {
        let sentences = module();
        let visible = sentences.iter().collect::<Vec<_>>();
        let universe = SortUniverse::new(&visible);
        let mut grammar = Grammar::from_configuration_sentences(
            visible
                .iter()
                .copied()
                .filter(|sentence| !matches!(sentence, Sentence::SyntaxSort { sort, .. } if *sort == mint("64"))),
        )
        .expect("the module's grammar builds");
        assert!(grammar.placeholders.is_empty());

        add_subsort(&mut grammar, mint("K"), mint("64"));

        grammar.assert_generated_sort_roles(&universe);
    }

    /// 16a7bce0: the portable rule scaffolding declared the alias of `P #as V` at `#KVariable`,
    /// which `KBott ::= #KVariable` puts below `KBott`, so the alias variable had no sort.
    #[test]
    #[should_panic(
        expected = "G2: the generated labeled production `syntax #RuleExp ::= Exp \"#as\" #KVariable` \
                    declares an operand at `#KVariable`"
    )]
    fn an_alias_declared_at_kvariable_fails_g2() {
        let (mut grammar, universe) = grammar_and_universe();
        add_subsort(&mut grammar, Sort::new("KBott"), Sort::new("#KVariable"));
        add_subsort(&mut grammar, Sort::new("#RuleExp"), Sort::new("Exp"));

        grammar
            .add(
                Sort::new("#RuleExp"),
                vec![
                    nonterminal(Sort::new("Exp")),
                    terminal("#as"),
                    nonterminal(Sort::new("#KVariable")),
                ],
                Some(Label::new("#KAs")),
                false,
                false,
            )
            .expect("the alias is added");

        grammar.assert_generated_sort_roles(&universe);
    }

    /// 45126388: the portable rule grammar declared a cell's body at the scaffolding sort
    /// `#RuleK`, so a whole-body variable was typed `#RuleK` instead of `K`.
    #[test]
    #[should_panic(
        expected = "G3: the generated labeled production `syntax KCell ::= \"<k>\" #RuleK \"</k>\"` \
                    of the defined sort `KCell` declares an operand at the wrapper `#RuleK`"
    )]
    fn a_cell_body_declared_at_its_rule_scaffold_fails_g3() {
        let (mut grammar, universe) = grammar_and_universe();
        add_subsort(&mut grammar, Sort::new("#RuleK"), Sort::new("K"));

        grammar
            .add(
                Sort::new("KCell"),
                vec![
                    terminal("<k>"),
                    nonterminal(Sort::new("#RuleK")),
                    terminal("</k>"),
                ],
                Some(Label::new("<k>")),
                false,
                false,
            )
            .expect("the cell is added");

        grammar.assert_generated_sort_roles(&universe);
    }

    /// G0: two generated pairs that close a cycle are a compiler defect, reported with each step
    /// of the cycle marked as generated.
    #[test]
    #[should_panic(
        expected = "G0: the semantic subsort relation is cyclic: Exp < KItem (generated); \
                    KItem < Exp (generated)"
    )]
    fn a_generated_pair_that_closes_a_cycle_fails_g0() {
        let (mut grammar, universe) = grammar_and_universe();
        add_subsort(&mut grammar, Sort::new("KItem"), Sort::new("Exp"));
        add_subsort(&mut grammar, Sort::new("Exp"), Sort::new("KItem"));

        grammar.assert_generated_sort_roles(&universe);
    }

    /// G0 names a step that a definition production states as declared, so a cycle through one
    /// generated and one declared pair shows which side is which.
    #[test]
    #[should_panic(
        expected = "G0: the semantic subsort relation is cyclic: Exp < KItem (generated); \
                    KItem < Exp (declared)"
    )]
    fn a_cycle_through_a_declared_pair_marks_it_declared() {
        let mut sentences = module();
        sentences.push(production(
            Vec::new(),
            Sort::new("Exp"),
            vec![nonterminal(Sort::new("KItem"))],
        ));
        let visible = sentences.iter().collect::<Vec<_>>();
        let universe = SortUniverse::new(&visible);
        let mut grammar = Grammar::from_configuration_sentences(visible.iter().copied())
            .expect("the module's grammar builds");
        add_subsort(&mut grammar, Sort::new("KItem"), Sort::new("Exp"));

        grammar.assert_generated_sort_roles(&universe);
    }

    /// The G2 violation of `an_alias_declared_at_kvariable_fails_g2`, in a grammar whose
    /// generated pairs also close a cycle: the check reports the cycle instead of passing the
    /// violation silently.
    #[test]
    #[should_panic(expected = "G0")]
    fn a_cycle_does_not_hide_a_g2_violation() {
        let (mut grammar, universe) = grammar_and_universe();
        add_subsort(&mut grammar, Sort::new("KBott"), Sort::new("#KVariable"));
        add_subsort(&mut grammar, Sort::new("#RuleExp"), Sort::new("Exp"));
        grammar
            .add(
                Sort::new("#RuleExp"),
                vec![
                    nonterminal(Sort::new("Exp")),
                    terminal("#as"),
                    nonterminal(Sort::new("#KVariable")),
                ],
                Some(Label::new("#KAs")),
                false,
                false,
            )
            .expect("the alias is added");
        add_subsort(&mut grammar, Sort::new("KItem"), Sort::new("Exp"));
        add_subsort(&mut grammar, Sort::new("Exp"), Sort::new("KItem"));

        grammar.assert_generated_sort_roles(&universe);
    }
}
