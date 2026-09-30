//! The sorts an inner grammar generates per-sort productions for, and the tables that state which
//! productions each sort role receives.
//!
//! A grammar's per-sort productions (brackets, subsorts into `KItem` and from the bottom sorts,
//! casts, sort predicates and projections, the portable build's rule scaffolding) range over one
//! set, [`SortUniverse`], computed once from the grammar's visible sentences. Which of them a sort
//! receives is a fact about its [`SortRole`], stated once per grammar in an exhaustive table:
//! every table is a `const fn` with one `match` naming every role or kernel sort, and every row
//! is a complete struct literal, so a new role forces a row and a new column forces every row.
//! The generators take [`GrammarSort`] and [`CastTarget`], whose fields are private, so a
//! production's formal parameter or an ad hoc spelling cannot reach them.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};

use crate::definition::{ProductionItem, Sentence, SortCatalog};
use crate::kast::sort_role::KernelSort;
use crate::kast::{Sort, SortRole};

/// The sorts of one grammar that per-sort generators range over (invariant I1).
///
/// The members are the sorts the visible sentences declare ([`SortCatalog::all_sorts`]: declared
/// nullary sorts, declared instances of parametric sorts and their numeral arguments) and, for
/// every visible production, its result and nonterminal item sorts that are not among that
/// production's `parameters` and are nullary or a declared instance.
///
/// The second part is required because a visible production is part of the grammar whether or
/// not the sentence declaring one of its sorts is visible: a production imported through a module
/// that imports the declaring module privately, or a cell production injected into every rule
/// grammar, still declares positions of its operand sorts, and each position needs the per-sort
/// productions of its sort (a variable, a cast, a bracket). Whether such a sort is declared
/// anywhere is the sort check's judgement, not the grammar's.
///
/// A production's `parameters` are sort variables bound by that production alone
/// (`syntax {Sort} Sort ::= "#Top"`), so a result or item sort naming one of them is not a sort of
/// the module and is never a member; a declared sort that happens to share a parameter's spelling
/// stays a member. A parametric sort with a free parameter (`MInt{Width}`) is a shape, not a
/// sort, and is never a member.
///
/// Membership is independent of the role: kernel, scaffolding and numeral sorts are members when
/// the sentences mention them, and the plan tables decide what each role receives.
pub(in crate::inner) struct SortUniverse {
    members: BTreeMap<Sort, SortRole>,
    /// `(alias, target)` of every visible sort synonym, in visible order. A synonym is another
    /// spelling of its target, not a sort of its own, so it is not a member; its casts are
    /// generated from here.
    synonyms: Vec<(Sort, Sort)>,
}

impl SortUniverse {
    pub(in crate::inner) fn new(visible: &[&Sentence]) -> Self {
        let catalog = SortCatalog::from_visible(visible.iter().copied());
        let instances = catalog
            .instantiations()
            .values()
            .flatten()
            .collect::<BTreeSet<_>>();
        let members = catalog
            .all_sorts()
            .iter()
            .chain(
                visible
                    .iter()
                    .flat_map(|sentence| unbound_production_sorts(sentence))
                    .filter(|sort| sort.parameters.is_empty() || instances.contains(sort)),
            )
            .map(|sort| (sort.clone(), sort.role()))
            .collect();
        let synonyms = visible
            .iter()
            .filter_map(|sentence| synonym(sentence))
            .collect();
        Self { members, synonyms }
    }

    /// Every member, in `Sort` order.
    pub(in crate::inner) fn members(&self) -> impl Iterator<Item = GrammarSort> + '_ {
        self.members.iter().map(|(sort, role)| GrammarSort {
            sort: sort.clone(),
            role: *role,
        })
    }

    /// The member `sort`, for a generator that starts from a sentence's operand.
    pub(in crate::inner) fn member(&self, sort: &Sort) -> Option<GrammarSort> {
        self.members
            .get_key_value(sort)
            .map(|(sort, role)| GrammarSort {
                sort: sort.clone(),
                role: *role,
            })
    }

    /// The casts of every visible synonym, in visible order: written with the alias, typed by
    /// the target.
    pub(in crate::inner) fn synonym_casts(&self) -> impl Iterator<Item = CastTarget> + '_ {
        self.synonyms.iter().map(|(alias, target)| CastTarget {
            cast: alias.clone(),
            label: target.clone(),
            outer_inner: KernelSort::K.sort(),
        })
    }

    /// Whether `sort` is a member or a synonym alias: a sort a generated production may mention.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "read by the grammar sort-role checker (CBC-05-T7)"
        )
    )]
    pub(in crate::inner) fn admits(&self, sort: &Sort) -> bool {
        self.members.contains_key(sort) || self.synonyms.iter().any(|(alias, _)| alias == sort)
    }
}

/// The result and nonterminal item sorts of a production that its own `parameters` do not bind.
/// No other sentence declares a position of a sort; the catalog reads the sort declarations.
fn unbound_production_sorts(sentence: &Sentence) -> Vec<&Sort> {
    match sentence {
        Sentence::Production {
            parameters,
            sort,
            items,
            ..
        } => std::iter::once(sort)
            .chain(items.iter().filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            }))
            .filter(|sort| !parameters.contains(sort))
            .collect(),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => Vec::new(),
    }
}

/// `(alias, target)` of a sort synonym.
fn synonym(sentence: &Sentence) -> Option<(Sort, Sort)> {
    match sentence {
        Sentence::SortSynonym {
            new_sort, old_sort, ..
        } => Some((new_sort.clone(), old_sort.clone())),
        Sentence::SyntaxSort { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
}

/// The argument of a per-sort generator: a universe member or a kernel sort, with its role.
///
/// The fields are private, and the only constructors are [`SortUniverse::members`],
/// [`SortUniverse::member`] and [`GrammarSort::kernel`].
#[derive(Clone, Debug)]
pub(in crate::inner) struct GrammarSort {
    sort: Sort,
    role: SortRole,
}

impl GrammarSort {
    /// A kernel sort, which every grammar has whether or not the module declares it.
    pub(in crate::inner) fn kernel(kernel: KernelSort) -> Self {
        Self {
            sort: kernel.sort(),
            role: SortRole::Kernel(kernel),
        }
    }

    pub(in crate::inner) fn sort(&self) -> &Sort {
        &self.sort
    }

    pub(in crate::inner) fn role(&self) -> SortRole {
        self.role
    }
}

/// The sorts of one family of cast productions.
///
/// `cast` is the sort written after `::`, `:` and `:>`, and the result of the syntactic casts
/// `::`; `label` is the operand sort of `::` and `:`, the result of `:` and `:>`, and names the
/// semantic cast; `outer_inner` is the operand sort of `:>`. A synonym's casts are written with
/// the alias and typed by the target, because the alias is a spelling of the target.
pub(in crate::inner) struct CastTarget {
    cast: Sort,
    label: Sort,
    outer_inner: Sort,
}

impl CastTarget {
    /// The casts of a grammar sort: written with and typed by the sort, and `{K}:>S` projects any
    /// `K` term to it.
    pub(in crate::inner) fn member(sort: &GrammarSort) -> Self {
        Self {
            cast: sort.sort.clone(),
            label: sort.sort.clone(),
            outer_inner: KernelSort::K.sort(),
        }
    }

    /// The casts of a kernel sort in the fixed kernel syntax. `KLabel` and `KList` are not sorts
    /// of `K` terms, so `:>` into them starts from a term of the same sort; every other kernel
    /// sort is projected from `K`.
    pub(in crate::inner) fn kernel(kernel: KernelSort) -> Self {
        let outer_inner = match kernel {
            KernelSort::KLabel => KernelSort::KLabel,
            KernelSort::KList => KernelSort::KList,
            KernelSort::K
            | KernelSort::KItem
            | KernelSort::KConfigVar
            | KernelSort::KBott
            | KernelSort::KString
            | KernelSort::Bag
            | KernelSort::Cell
            | KernelSort::Bool => KernelSort::K,
        };
        Self {
            cast: kernel.sort(),
            label: kernel.sort(),
            outer_inner: outer_inner.sort(),
        }
    }

    pub(in crate::inner) fn cast(&self) -> &Sort {
        &self.cast
    }

    pub(in crate::inner) fn label(&self) -> &Sort {
        &self.label
    }

    pub(in crate::inner) fn outer_inner(&self) -> &Sort {
        &self.outer_inner
    }
}

/// The rule grammar's per-sort productions for one universe member, by role.
///
/// The conditions that are facts about the grammar rather than the sort stay at the call site:
/// the predicate and projection only without a visible production of the same label, the `KItem`
/// subsort only without a generated or explicit top sort, the bottom subsort only without a
/// generated bottom sort, the bracket only without a visible bracket production of the sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::inner) struct RuleMemberProductions {
    /// `isS(_)`.
    pub(in crate::inner) predicate: bool,
    /// `project:S(_)`.
    pub(in crate::inner) projection: bool,
    /// The `#Rule` and `#RewriteSide` scaffolding sorts of the portable build, through which a
    /// position of the sort also admits a rewrite or an `#as` pattern of it.
    #[cfg(not(feature = "z3-inference"))]
    pub(in crate::inner) rule_scaffold: bool,
    /// `KItem ::= S`.
    pub(in crate::inner) kitem_subsort: bool,
    /// `S ::= KBott`, through which a variable stands at the sort.
    pub(in crate::inner) bottom_subsort: bool,
    /// The four cast productions of [`CastTarget::member`].
    pub(in crate::inner) casts: bool,
    /// `S ::= "(" S ")"`.
    pub(in crate::inner) bracket: bool,
}

/// The rule grammar's per-member table.
///
/// A defined sort receives every production. `Bool` is a sort of `K` terms, but its `KItem`
/// subsort, its variable subsorts and its casts belong to the fixed kernel syntax both grammars
/// share, so the member loop adds only its predicate, projection, scaffolding and bracket.
/// `KLabel`, `KList` and `KString` receive every production when the module declares them (their
/// predicate and projection are revisited by CBC-05-T10). `K`, `KItem`, `Bag`, `Cell`, `KBott` and
/// `KConfigVar` receive their productions from the kernel syntax and the kernel seeds, not from
/// the member loop. A rigid variable, a scaffolding sort and a numeral denote no set of terms a
/// rule could mention, so they receive nothing.
pub(in crate::inner) const fn rule_member_productions(role: SortRole) -> RuleMemberProductions {
    use KernelSort as S;
    match role {
        SortRole::Defined | SortRole::Kernel(S::KLabel | S::KList | S::KString) => {
            RuleMemberProductions {
                predicate: true,
                projection: true,
                #[cfg(not(feature = "z3-inference"))]
                rule_scaffold: true,
                kitem_subsort: true,
                bottom_subsort: true,
                casts: true,
                bracket: true,
            }
        }
        SortRole::Kernel(S::Bool) => RuleMemberProductions {
            predicate: true,
            projection: true,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: true,
            kitem_subsort: false,
            bottom_subsort: false,
            casts: false,
            bracket: true,
        },
        SortRole::Kernel(S::K | S::KItem | S::KConfigVar | S::KBott | S::Bag | S::Cell)
        | SortRole::RigidVariable
        | SortRole::Scaffolding
        | SortRole::Nat => RuleMemberProductions {
            predicate: false,
            projection: false,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: false,
            kitem_subsort: false,
            bottom_subsort: false,
            casts: false,
            bracket: false,
        },
    }
}

/// Where the rule grammar adds a kernel sort's scaffolding (portable build).
#[cfg(not(feature = "z3-inference"))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::inner) enum ScaffoldPosition {
    /// Inside the rule kernel syntax, before `#RuleBody ::= #Rule<K>`, which derives through it.
    BeforeRuleBody,
    /// After the rule cells.
    AfterRuleCells,
}

/// The rule grammar's productions for one kernel sort, whether or not the module declares it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::inner) struct RuleKernelSeeds {
    /// `S ::= "(" S ")"`.
    pub(in crate::inner) bracket: bool,
    /// The four cast productions of [`CastTarget::kernel`].
    pub(in crate::inner) casts: bool,
    /// The `#Rule` scaffolding of the portable build, and where it is added.
    #[cfg(not(feature = "z3-inference"))]
    pub(in crate::inner) rule_scaffold: Option<ScaffoldPosition>,
}

/// The rule grammar's kernel seed table.
///
/// A rule body is a `K` pattern, and cell contents, collection cells and the common argument
/// positions declared `KItem` (`ListItem`, `SetItem`) are `Bag` and `KItem` patterns, so these
/// three receive a bracket and scaffolding in every rule grammar; a parenthesized `Bag => Bag`
/// rewrite before a collection cell's trailing dots needs the `Bag` bracket. `Bag` and `Cell` are
/// the structural sorts of a rule's cells and receive casts. `K`, `KItem`, `KLabel`, `KList` and
/// `Bool` receive their casts in the fixed kernel syntax.
pub(in crate::inner) const fn rule_kernel_seeds(kernel: KernelSort) -> RuleKernelSeeds {
    match kernel {
        KernelSort::K => RuleKernelSeeds {
            bracket: true,
            casts: false,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: Some(ScaffoldPosition::BeforeRuleBody),
        },
        KernelSort::KItem => RuleKernelSeeds {
            bracket: true,
            casts: false,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: Some(ScaffoldPosition::AfterRuleCells),
        },
        KernelSort::Bag => RuleKernelSeeds {
            bracket: true,
            casts: true,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: Some(ScaffoldPosition::AfterRuleCells),
        },
        KernelSort::Cell => RuleKernelSeeds {
            bracket: false,
            casts: true,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: None,
        },
        KernelSort::KConfigVar
        | KernelSort::KBott
        | KernelSort::KLabel
        | KernelSort::KList
        | KernelSort::KString
        | KernelSort::Bool => RuleKernelSeeds {
            bracket: false,
            casts: false,
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: None,
        },
    }
}

/// The decisions of one grammar that are not per sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::inner) struct GrammarPlan {
    /// The casts of every visible synonym ([`SortUniverse::synonym_casts`]).
    pub(in crate::inner) synonym_casts: bool,
}

/// A rule may cast a term to a visible synonym, which is a spelling of its target.
pub(in crate::inner) const RULE_GRAMMAR: GrammarPlan = GrammarPlan {
    synonym_casts: true,
};

use KernelSort::{Bag, Bool, Cell, K, KBott, KConfigVar, KItem, KLabel, KList, KString};

/// The order in which the rule grammar adds its kernel bracket seeds.
pub(in crate::inner) const RULE_BRACKET_SEED_ORDER: [KernelSort; 10] = checked_order([
    K, KItem, Bag, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
]);

/// The order in which the rule grammar adds its kernel cast seeds.
pub(in crate::inner) const RULE_CAST_SEED_ORDER: [KernelSort; 10] = checked_order([
    Bag, Cell, K, KItem, KConfigVar, KBott, KLabel, KList, KString, Bool,
]);

/// The order in which the rule grammar adds the kernel scaffolding seeds at each
/// [`ScaffoldPosition`].
#[cfg(not(feature = "z3-inference"))]
pub(in crate::inner) const RULE_SCAFFOLD_SEED_ORDER: [KernelSort; 10] = checked_order([
    K, Bag, KItem, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
]);

/// Whether `order` names every kernel sort exactly once, so an ordering array filtered by a seed
/// table cannot drop a kernel sort.
const fn is_permutation_of_all(order: &[KernelSort; 10]) -> bool {
    let mut seen = [false; KernelSort::ALL.len()];
    let mut index = 0;
    while index < order.len() {
        let slot = order[index] as usize;
        if seen[slot] {
            return false;
        }
        seen[slot] = true;
        index += 1;
    }
    true
}

/// `order`, checked while the constant it initializes is evaluated: an ordering array that does
/// not name every kernel sort exactly once does not compile.
const fn checked_order(order: [KernelSort; 10]) -> [KernelSort; 10] {
    assert!(
        is_permutation_of_all(&order),
        "an ordering array names every kernel sort exactly once"
    );
    order
}

/// The configuration grammar's tables.
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "read by the configuration grammar (CBC-05-T4)")
)]
pub(in crate::inner) mod configuration {
    use super::{GrammarPlan, KernelSort, SortRole, checked_order};
    use KernelSort::{Bag, Bool, Cell, K, KBott, KConfigVar, KItem, KLabel, KList, KString};

    /// The configuration grammar's per-sort productions for one universe member, by role.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(in crate::inner) struct ConfigurationMemberProductions {
        /// `S ::= "(" S ")"`.
        pub(in crate::inner) bracket: bool,
        /// `KItem ::= S`.
        pub(in crate::inner) kitem_subsort: bool,
        /// `S ::= KConfigVar` and `S ::= #KVariable`: a configuration variable and a variable
        /// stand at the sort.
        pub(in crate::inner) variable_subsorts: bool,
        /// The four cast productions of [`CastTarget::member`](super::CastTarget::member).
        pub(in crate::inner) casts: bool,
    }

    /// The configuration grammar's per-member table: a defined sort and every kernel sort
    /// receive a bracket; a defined sort, `KLabel`, `KList` and `KString` receive their subsorts
    /// and casts here, the other kernel sorts from the fixed kernel syntax; a rigid variable, a
    /// scaffolding sort and a numeral denote no set of terms a configuration could mention and
    /// receive nothing.
    pub(in crate::inner) const fn configuration_member_productions(
        role: SortRole,
    ) -> ConfigurationMemberProductions {
        use KernelSort as S;
        match role {
            SortRole::Defined | SortRole::Kernel(S::KLabel | S::KList | S::KString) => {
                ConfigurationMemberProductions {
                    bracket: true,
                    kitem_subsort: true,
                    variable_subsorts: true,
                    casts: true,
                }
            }
            SortRole::Kernel(
                S::Bool | S::K | S::KItem | S::Bag | S::Cell | S::KBott | S::KConfigVar,
            ) => ConfigurationMemberProductions {
                bracket: true,
                kitem_subsort: false,
                variable_subsorts: false,
                casts: false,
            },
            SortRole::RigidVariable | SortRole::Scaffolding | SortRole::Nat => {
                ConfigurationMemberProductions {
                    bracket: false,
                    kitem_subsort: false,
                    variable_subsorts: false,
                    casts: false,
                }
            }
        }
    }

    /// The configuration grammar's productions for one kernel sort, whether or not the module
    /// declares it.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(in crate::inner) struct ConfigurationKernelSeeds {
        /// `S ::= "(" S ")"`.
        pub(in crate::inner) bracket: bool,
    }

    /// The configuration grammar's kernel seed table: a configuration body is a `K` term whose
    /// cells hold `KItem` and `Bag` terms, and each of the three can be parenthesized.
    pub(in crate::inner) const fn configuration_kernel_seeds(
        kernel: KernelSort,
    ) -> ConfigurationKernelSeeds {
        match kernel {
            KernelSort::K | KernelSort::KItem | KernelSort::Bag => {
                ConfigurationKernelSeeds { bracket: true }
            }
            KernelSort::KConfigVar
            | KernelSort::KBott
            | KernelSort::KLabel
            | KernelSort::KList
            | KernelSort::KString
            | KernelSort::Cell
            | KernelSort::Bool => ConfigurationKernelSeeds { bracket: false },
        }
    }

    /// A configuration may cast a term to a visible synonym, as a rule may.
    pub(in crate::inner) const CONFIGURATION_GRAMMAR: GrammarPlan = GrammarPlan {
        synonym_casts: true,
    };

    /// The order in which the configuration grammar adds its kernel bracket seeds.
    pub(in crate::inner) const CONFIGURATION_BRACKET_SEED_ORDER: [KernelSort; 10] =
        checked_order([
            K, KItem, Bag, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
        ]);
}

#[cfg(test)]
mod tests {
    use super::configuration::*;
    use super::*;
    use crate::definition::Attributes;

    fn syntax_sort(sort: Sort) -> Sentence {
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort,
            attributes: Attributes::default(),
        }
    }

    fn mint(width: &str) -> Sort {
        Sort::with_parameters("MInt", vec![Sort::new(width)])
    }

    /// 032a375b: a declared instance of a parametric sort is a sort of the grammar and receives
    /// the per-sort productions of a defined sort; the parametric shape it instantiates does not.
    #[test]
    fn a_declared_instance_is_a_member_and_its_shape_is_not() {
        let width = Sort::new("Width");
        let sentences = [
            syntax_sort(mint("8")),
            Sentence::Production {
                label: None,
                parameters: vec![width.clone()],
                sort: Sort::with_parameters("MInt", vec![width]),
                items: vec![ProductionItem::Terminal("mint".into())],
                attributes: Attributes::default(),
            },
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        let member = universe
            .member(&mint("8"))
            .expect("MInt{8} is a member of the universe of `syntax MInt{8}`");
        assert_eq!(member.role(), SortRole::Defined);
        let productions = rule_member_productions(member.role());
        assert!(productions.kitem_subsort && productions.casts && productions.bracket);
        assert!(universe.member(&mint("Width")).is_none());
        assert!(universe.member(&Sort::new("Width")).is_none());
        // The numeral argument is a member, and its role gives it no production.
        assert_eq!(
            universe.member(&Sort::new("8")).map(|member| member.role()),
            Some(SortRole::Nat)
        );
        assert_eq!(
            rule_member_productions(SortRole::Nat),
            rule_member_productions(SortRole::Scaffolding)
        );
    }

    /// 7a20220d: a visible synonym yields the casts of its alias, typed by its target, and is not
    /// a member of its own.
    #[test]
    fn a_synonym_yields_one_cast_target_written_with_the_alias_and_typed_by_the_target() {
        let sentences = [
            syntax_sort(Sort::new("Rat")),
            Sentence::SortSynonym {
                new_sort: Sort::new("Wad"),
                old_sort: Sort::new("Rat"),
                attributes: Attributes::default(),
            },
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        let casts = universe.synonym_casts().collect::<Vec<_>>();
        assert_eq!(casts.len(), 1);
        assert_eq!(casts[0].cast(), &Sort::new("Wad"));
        assert_eq!(casts[0].label(), &Sort::new("Rat"));
        assert_eq!(casts[0].outer_inner(), &Sort::new("K"));
        assert!(universe.member(&Sort::new("Wad")).is_none());
        assert!(universe.admits(&Sort::new("Wad")));
        assert!(universe.admits(&Sort::new("Rat")));
        assert!(!universe.admits(&Sort::new("Int")));
    }

    #[test]
    fn kernel_casts_project_from_k_except_into_klabel_and_klist() {
        for kernel in KernelSort::ALL {
            let target = CastTarget::kernel(kernel);
            assert_eq!(target.cast(), &kernel.sort());
            assert_eq!(target.label(), &kernel.sort());
            let expected = match kernel {
                KernelSort::KLabel | KernelSort::KList => kernel.sort(),
                KernelSort::K
                | KernelSort::KItem
                | KernelSort::KConfigVar
                | KernelSort::KBott
                | KernelSort::KString
                | KernelSort::Bag
                | KernelSort::Cell
                | KernelSort::Bool => Sort::new("K"),
            };
            assert_eq!(target.outer_inner(), &expected, "{}", kernel.name());
        }
    }

    fn every_role() -> Vec<SortRole> {
        KernelSort::ALL
            .into_iter()
            .map(SortRole::Kernel)
            .chain([
                SortRole::RigidVariable,
                SortRole::Scaffolding,
                SortRole::Nat,
                SortRole::Defined,
            ])
            .collect()
    }

    /// The tables as the design states them (CBC-05 section 2.3). The columns are those of the
    /// struct, in field order.
    #[test]
    fn plan_tables_are_pinned() {
        use KernelSort as S;
        let rule_member = |role: SortRole| {
            let row = rule_member_productions(role);
            [
                row.predicate,
                row.projection,
                #[cfg(not(feature = "z3-inference"))]
                row.rule_scaffold,
                row.kitem_subsort,
                row.bottom_subsort,
                row.casts,
                row.bracket,
            ]
        };
        let configuration_member = |role: SortRole| {
            let row = configuration_member_productions(role);
            [
                row.bracket,
                row.kitem_subsort,
                row.variable_subsorts,
                row.casts,
            ]
        };
        for role in every_role() {
            let every_rule_production = match role {
                SortRole::Defined | SortRole::Kernel(S::KLabel | S::KList | S::KString) => true,
                SortRole::Kernel(
                    S::Bool | S::K | S::KItem | S::KConfigVar | S::KBott | S::Bag | S::Cell,
                )
                | SortRole::RigidVariable
                | SortRole::Scaffolding
                | SortRole::Nat => false,
            };
            let expected_rule = if role == SortRole::Kernel(S::Bool) {
                vec![
                    true,
                    true,
                    #[cfg(not(feature = "z3-inference"))]
                    true,
                    false,
                    false,
                    false,
                    true,
                ]
            } else {
                vec![every_rule_production; rule_member(role).len()]
            };
            assert_eq!(rule_member(role).to_vec(), expected_rule, "{role:?}");
            let expected_configuration = match role {
                SortRole::Defined | SortRole::Kernel(S::KLabel | S::KList | S::KString) => {
                    [true, true, true, true]
                }
                SortRole::Kernel(
                    S::Bool | S::K | S::KItem | S::Bag | S::Cell | S::KBott | S::KConfigVar,
                ) => [true, false, false, false],
                SortRole::RigidVariable | SortRole::Scaffolding | SortRole::Nat => {
                    [false, false, false, false]
                }
            };
            assert_eq!(
                configuration_member(role),
                expected_configuration,
                "{role:?}"
            );
        }

        let rule_seeds = |order: &[KernelSort; 10], column: fn(RuleKernelSeeds) -> bool| {
            order
                .iter()
                .copied()
                .filter(|kernel| column(rule_kernel_seeds(*kernel)))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            rule_seeds(&RULE_BRACKET_SEED_ORDER, |seeds| seeds.bracket),
            [S::K, S::KItem, S::Bag]
        );
        assert_eq!(
            rule_seeds(&RULE_CAST_SEED_ORDER, |seeds| seeds.casts),
            [S::Bag, S::Cell]
        );
        #[cfg(not(feature = "z3-inference"))]
        {
            let at = |position| {
                RULE_SCAFFOLD_SEED_ORDER
                    .iter()
                    .copied()
                    .filter(|kernel| rule_kernel_seeds(*kernel).rule_scaffold == Some(position))
                    .collect::<Vec<_>>()
            };
            assert_eq!(at(ScaffoldPosition::BeforeRuleBody), [S::K]);
            assert_eq!(at(ScaffoldPosition::AfterRuleCells), [S::Bag, S::KItem]);
        }
        assert_eq!(
            CONFIGURATION_BRACKET_SEED_ORDER
                .iter()
                .copied()
                .filter(|kernel| configuration_kernel_seeds(*kernel).bracket)
                .collect::<Vec<_>>(),
            [S::K, S::KItem, S::Bag]
        );
        assert_eq!(
            [RULE_GRAMMAR, CONFIGURATION_GRAMMAR],
            [GrammarPlan {
                synonym_casts: true
            }; 2]
        );
    }

    #[test]
    fn an_ordering_array_with_a_repeated_kernel_sort_is_rejected() {
        let mut order = KernelSort::ALL;
        assert!(is_permutation_of_all(&order));
        order[9] = KernelSort::K;
        assert!(!is_permutation_of_all(&order));
    }
}
