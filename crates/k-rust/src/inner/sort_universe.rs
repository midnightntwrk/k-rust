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
/// The members are the sorts that a visible sentence declares or gives a position: the sort of
/// every `syntax S` declaration, and the result and nonterminal item sorts of every production,
/// each unless the sentence's own `parameters` bind it, and each only when it is nullary or a
/// declared instance of a parametric sort ([`SortCatalog::instantiations`]).
///
/// The positions count whether or not the sentence declaring their sort is visible: a production
/// imported through a module that imports the declaring module privately, or a cell production
/// injected into every rule grammar, still declares positions of its operand sorts, and each
/// position needs the per-sort productions of its sort (a variable, a cast, a bracket). Whether
/// such a sort is declared anywhere is the sort check's judgement, not the grammar's.
///
/// A sentence's `parameters` are sort variables bound by that sentence alone
/// (`syntax {Sort} Sort ::= "#Top"`), so a sort naming one of them is not a sort of the module and
/// is never a member; a declared sort that happens to share a parameter's spelling stays a member.
/// A parametric sort with a free parameter (`MInt{Width}`) is a shape, not a sort, and is never a
/// member. The arguments of a declared instance (the `8` of `MInt{8}`) are not positions of the
/// grammar, so a numeral is a member only when a sentence declares it or gives a production a
/// position of it (`syntax 8 ::= "eight"`); it is then a sort of terms like any declared sort.
///
/// Membership is independent of the role: kernel, scaffolding and numeral sorts are members when
/// the sentences declare or position them, and the plan tables decide what each role receives.
pub(in crate::inner) struct SortUniverse {
    members: BTreeMap<Sort, SortRole>,
    /// `(alias, target)` of every visible sort synonym whose target is a sort of the grammar (a
    /// member or a nullary kernel sort), in visible order. A synonym is another spelling of its
    /// target, not a sort of its own, so it is not a member; its casts are generated from here.
    /// A synonym whose target is not a sort of the grammar (declared nowhere visible and given no
    /// position, or a shape with a free parameter) names no sort of it and is left out.
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
        let members: BTreeMap<Sort, SortRole> = visible
            .iter()
            .flat_map(|sentence| unbound_sorts(sentence))
            .filter(|sort| sort.parameters.is_empty() || instances.contains(sort))
            .map(|sort| (sort.clone(), sort.role()))
            .collect();
        let synonyms = visible
            .iter()
            .filter_map(|sentence| synonym(sentence))
            .filter(|(_, target)| is_grammar_sort(&members, target))
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

    /// The casts of every visible synonym whose target is a sort of the grammar, in visible order:
    /// written with the alias, typed by the target. A synonym whose target is not a sort of the
    /// grammar has no casts: they would be typed by a sort no production derives or accepts.
    pub(in crate::inner) fn synonym_casts(&self) -> impl Iterator<Item = CastTarget> + '_ {
        self.synonyms
            .iter()
            .map(|(alias, target)| CastTarget::new(alias.clone(), target.clone()))
    }

    /// Whether `sort` is a member or the alias of a synonym whose target is a sort of the grammar:
    /// a sort a generated production may mention. Read by the grammar sort-role check, which
    /// exists in builds with debug assertions.
    #[cfg(debug_assertions)]
    pub(in crate::inner) fn admits(&self, sort: &Sort) -> bool {
        self.members.contains_key(sort) || self.synonyms.iter().any(|(alias, _)| alias == sort)
    }
}

/// The sorts a sentence declares or gives a position that its own `parameters` do not bind: the
/// sort of a `syntax S` declaration, the result and nonterminal item sorts of a production. No
/// other sentence declares a sort or a position of one; a synonym is a spelling of its target.
fn unbound_sorts(sentence: &Sentence) -> Vec<&Sort> {
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
        Sentence::SyntaxSort {
            parameters, sort, ..
        } => std::iter::once(sort)
            .filter(|sort| !parameters.contains(sort))
            .collect(),
        Sentence::SortSynonym { .. }
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

/// Whether `sort` is a sort of the grammar whose universe has `members`: a member, or a nullary
/// kernel sort, which every grammar has. A synonym whose target is neither spells no sort of the
/// grammar.
fn is_grammar_sort(members: &BTreeMap<Sort, SortRole>, sort: &Sort) -> bool {
    if members.contains_key(sort) {
        return true;
    }
    match sort.role() {
        SortRole::Kernel(_) => sort.parameters.is_empty(),
        SortRole::RigidVariable | SortRole::Scaffolding | SortRole::Nat | SortRole::Defined => {
            false
        }
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
/// semantic cast. A synonym's casts are written with the alias and typed by the target, because
/// the alias is a spelling of the target.
///
/// The projection cast `{K}:>cast` lowers to `project:label` applied to its `K` operand.
/// Compilation declares `project:label` exactly when the role of `label` has a sort projection
/// ([`SortRole::has_sort_projection`]), so the family has the projection cast exactly then:
/// `projects` is decided once, in [`CastTarget::new`], from that predicate.
pub(in crate::inner) struct CastTarget {
    cast: Sort,
    label: Sort,
    projects: bool,
}

impl CastTarget {
    /// The casts written with `cast` and typed by `label`. The projection cast is among them
    /// exactly when `label`'s role has a sort projection, the condition under which compilation
    /// declares the `project:label` it lowers to.
    fn new(cast: Sort, label: Sort) -> Self {
        let projects = label.role().has_sort_projection();
        Self {
            cast,
            label,
            projects,
        }
    }

    /// The casts of a grammar sort: written with and typed by the sort.
    pub(in crate::inner) fn member(sort: &GrammarSort) -> Self {
        Self::new(sort.sort.clone(), sort.sort.clone())
    }

    /// The casts of a kernel sort in the fixed kernel syntax: written with and typed by the sort.
    pub(in crate::inner) fn kernel(kernel: KernelSort) -> Self {
        Self::new(kernel.sort(), kernel.sort())
    }

    pub(in crate::inner) fn cast(&self) -> &Sort {
        &self.cast
    }

    pub(in crate::inner) fn label(&self) -> &Sort {
        &self.label
    }

    /// The operand sort of the projection cast `{K}:>cast`, which is `K`, or `None` when the
    /// family has no projection cast because compilation declares no `project:label`.
    pub(in crate::inner) fn projection_operand(&self) -> Option<Sort> {
        self.projects.then(|| KernelSort::K.sort())
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
    /// The cast productions of [`CastTarget::member`].
    pub(in crate::inner) casts: bool,
    /// `S ::= "(" S ")"`.
    pub(in crate::inner) bracket: bool,
}

/// The rule grammar's per-member table.
///
/// The sort predicate and the sort projection of every row are [`SortRole::has_sort_predicate`]
/// and [`SortRole::has_sort_projection`], the predicates compilation generates the same helpers
/// from (`kompile::passes::generate_sort_helpers`): a rule can mention `isS(_)` or
/// `project:S(_)` exactly when the compiled definition declares it.
///
/// For the other columns: a defined sort receives every production. A numeral member is a sort
/// that a sentence declares or gives a production a position of ([`SortUniverse`]), so it
/// receives what a defined sort receives. `Bool` is a sort of `K` terms, but its `KItem` subsort,
/// its variable subsorts and its casts belong to the fixed kernel syntax both grammars share, so
/// the member loop adds only its scaffolding and bracket. `KLabel`, `KList` and `KString` receive
/// every production except `KItem ::= S` when the module declares them: a variable, a cast or a
/// bracket may stand at a label, an argument sequence or a token spelling, but none of the three
/// is a sort of K items ([`SortRole::lies_below_kitem`]), and with the declared `KList ::= K` and
/// `K ::= KItem`, `KItem ::= KList` would close the cycle `KItem < K < KList < KItem`, under which
/// no term can be given a sort. `K`, `KItem`, `Bag`, `Cell`, `KBott` and `KConfigVar` receive
/// their other productions from the kernel syntax and the kernel seeds, not from the member loop.
/// A rigid variable and a scaffolding sort denote no set of terms a rule could mention, so they
/// receive nothing.
pub(in crate::inner) const fn rule_member_productions(role: SortRole) -> RuleMemberProductions {
    use KernelSort as S;
    match role {
        SortRole::Defined | SortRole::Nat => RuleMemberProductions {
            predicate: role.has_sort_predicate(),
            projection: role.has_sort_projection(),
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: true,
            kitem_subsort: true,
            bottom_subsort: true,
            casts: true,
            bracket: true,
        },
        SortRole::Kernel(S::KLabel | S::KList | S::KString) => RuleMemberProductions {
            predicate: role.has_sort_predicate(),
            projection: role.has_sort_projection(),
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: true,
            kitem_subsort: false,
            bottom_subsort: true,
            casts: true,
            bracket: true,
        },
        SortRole::Kernel(S::Bool) => RuleMemberProductions {
            predicate: role.has_sort_predicate(),
            projection: role.has_sort_projection(),
            #[cfg(not(feature = "z3-inference"))]
            rule_scaffold: true,
            kitem_subsort: false,
            bottom_subsort: false,
            casts: false,
            bracket: true,
        },
        SortRole::Kernel(S::K | S::KItem | S::KConfigVar | S::KBott | S::Bag | S::Cell)
        | SortRole::RigidVariable
        | SortRole::Scaffolding => RuleMemberProductions {
            predicate: role.has_sort_predicate(),
            projection: role.has_sort_projection(),
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
    /// The cast productions of [`CastTarget::kernel`].
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

/// Every kernel sort, in the order in which a grammar adds one family of kernel seeds; the seed
/// table then decides which of them receive the family.
///
/// The length is that of [`KernelSort::ALL`], so a kernel sort added to `ALL` makes every ordering
/// array fail to compile until it is placed in it, and [`checked_order`] rejects a repeated one.
pub(in crate::inner) type SeedOrder = [KernelSort; KernelSort::ALL.len()];

/// The order in which the rule grammar adds its kernel bracket seeds.
pub(in crate::inner) const RULE_BRACKET_SEED_ORDER: SeedOrder = checked_order([
    K, KItem, Bag, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
]);

/// The order in which the rule grammar adds its kernel cast seeds.
pub(in crate::inner) const RULE_CAST_SEED_ORDER: SeedOrder = checked_order([
    Bag, Cell, K, KItem, KConfigVar, KBott, KLabel, KList, KString, Bool,
]);

/// The order in which the rule grammar adds the kernel scaffolding seeds at each
/// [`ScaffoldPosition`].
#[cfg(not(feature = "z3-inference"))]
pub(in crate::inner) const RULE_SCAFFOLD_SEED_ORDER: SeedOrder = checked_order([
    K, Bag, KItem, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
]);

/// Whether `order` names every kernel sort exactly once: as many entries as [`KernelSort::ALL`],
/// no two equal. An ordering array filtered by a seed table then cannot drop a kernel sort.
const fn is_permutation_of_all(order: &[KernelSort]) -> bool {
    if order.len() != KernelSort::ALL.len() {
        return false;
    }
    let mut seen = [false; KernelSort::ALL.len()];
    let mut index = 0;
    while index < order.len() {
        let slot = order[index] as usize;
        if slot >= seen.len() || seen[slot] {
            return false;
        }
        seen[slot] = true;
        index += 1;
    }
    true
}

/// `order`, checked while the constant it initializes is evaluated: an ordering array that does
/// not name every kernel sort exactly once does not compile.
const fn checked_order(order: SeedOrder) -> SeedOrder {
    assert!(
        is_permutation_of_all(&order),
        "an ordering array names every kernel sort exactly once"
    );
    order
}

/// The configuration grammar's tables.
pub(in crate::inner) mod configuration {
    use super::{GrammarPlan, KernelSort, SeedOrder, SortRole, checked_order};
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
        /// The cast productions of [`CastTarget::member`](super::CastTarget::member).
        pub(in crate::inner) casts: bool,
    }

    /// The configuration grammar's per-member table: a defined sort, a numeral member (a sort a
    /// sentence declares or positions, as in the rule grammar) and every kernel sort receive a
    /// bracket; a defined sort and a numeral member receive their subsorts and casts here;
    /// `KLabel`, `KList` and `KString` receive every production except `KItem ::= S`, because a
    /// label, an argument sequence and a token spelling are not K items
    /// ([`SortRole::lies_below_kitem`]) and `KItem ::= KList` would close the cycle
    /// `KItem < K < KList < KItem` with the declared `KList ::= K` and `K ::= KItem`; the other
    /// kernel sorts receive their subsorts and casts from the fixed kernel syntax; a rigid variable
    /// and a scaffolding sort denote no set of terms a configuration could mention and receive
    /// nothing.
    pub(in crate::inner) const fn configuration_member_productions(
        role: SortRole,
    ) -> ConfigurationMemberProductions {
        use KernelSort as S;
        match role {
            SortRole::Defined | SortRole::Nat => ConfigurationMemberProductions {
                bracket: true,
                kitem_subsort: true,
                variable_subsorts: true,
                casts: true,
            },
            SortRole::Kernel(S::KLabel | S::KList | S::KString) => ConfigurationMemberProductions {
                bracket: true,
                kitem_subsort: false,
                variable_subsorts: true,
                casts: true,
            },
            SortRole::Kernel(
                S::Bool | S::K | S::KItem | S::Bag | S::Cell | S::KBott | S::KConfigVar,
            ) => ConfigurationMemberProductions {
                bracket: true,
                kitem_subsort: false,
                variable_subsorts: false,
                casts: false,
            },
            SortRole::RigidVariable | SortRole::Scaffolding => ConfigurationMemberProductions {
                bracket: false,
                kitem_subsort: false,
                variable_subsorts: false,
                casts: false,
            },
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
    pub(in crate::inner) const CONFIGURATION_BRACKET_SEED_ORDER: SeedOrder = checked_order([
        K, KItem, Bag, KConfigVar, KBott, KLabel, KList, KString, Cell, Bool,
    ]);
}

/// Whether the per-member subsort columns of both member tables state, for `role`, only kernel
/// positions the role grants: `KItem ::= S` only for a sort strictly below `KItem`
/// ([`SortRole::lies_below_kitem`]), and `S ::= KBott`, `S ::= KConfigVar` and `S ::= #KVariable`
/// only for a sort a variable stands at ([`SortRole::admits_variables`]).
///
/// A generated subsort is an inclusion the grammar's sort order relies on. One that the role
/// denies places a sort where it cannot lie, and together with the definition's own subsorts it
/// can close a cycle, in which no term can be given a sort.
const fn member_subsorts_are_granted(role: SortRole) -> bool {
    let rule = rule_member_productions(role);
    let configuration = configuration::configuration_member_productions(role);
    (!rule.kitem_subsort || role.lies_below_kitem())
        && (!configuration.kitem_subsort || role.lies_below_kitem())
        && (!rule.bottom_subsort || role.admits_variables())
        && (!configuration.variable_subsorts || role.admits_variables())
}

/// Every role's rows of both member tables state only granted kernel positions: a row that states
/// another does not compile.
const _: () = {
    let mut index = 0;
    while index < KernelSort::ALL.len() {
        assert!(
            member_subsorts_are_granted(SortRole::Kernel(KernelSort::ALL[index])),
            "a member table states a kernel position that a kernel sort's role denies"
        );
        index += 1;
    }
    let others = [
        SortRole::Defined,
        SortRole::Nat,
        SortRole::RigidVariable,
        SortRole::Scaffolding,
    ];
    let mut index = 0;
    while index < others.len() {
        assert!(
            member_subsorts_are_granted(others[index]),
            "a member table states a kernel position that a non-kernel role denies"
        );
        index += 1;
    }
};

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
        // The numeral argument instantiates the shape; no sentence gives it a position.
        assert!(universe.member(&Sort::new("8")).is_none());
    }

    /// A numeral that a sentence declares (`syntax 16`) or gives a production a position of
    /// (`syntax 8 ::= "eight"`, the operand of `bar(8)`) is a sort of terms, and receives what a
    /// defined sort receives in both grammars except the sort predicate and projection, which
    /// compilation declares for no numeral; a numeral that only instantiates a parametric sort is
    /// not a member.
    #[test]
    fn a_numeral_declared_or_positioned_by_a_sentence_is_a_member_with_the_rows_of_a_defined_sort()
    {
        let sentences = [
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("8"),
                items: vec![ProductionItem::Terminal("eight".into())],
                attributes: Attributes::default(),
            },
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("Foo"),
                items: vec![
                    ProductionItem::Terminal("bar".into()),
                    ProductionItem::Terminal("(".into()),
                    ProductionItem::NonTerminal {
                        sort: Sort::new("8"),
                        name: None,
                    },
                    ProductionItem::Terminal(")".into()),
                ],
                attributes: Attributes::default(),
            },
            syntax_sort(Sort::new("16")),
            syntax_sort(mint("32")),
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        for numeral in ["8", "16"] {
            let member = universe
                .member(&Sort::new(numeral))
                .unwrap_or_else(|| panic!("{numeral} is a member"));
            assert_eq!(member.role(), SortRole::Nat, "{numeral}");
            assert_eq!(
                RuleMemberProductions {
                    predicate: false,
                    projection: false,
                    ..rule_member_productions(SortRole::Defined)
                },
                rule_member_productions(member.role()),
                "{numeral}"
            );
            assert_eq!(
                configuration_member_productions(member.role()),
                configuration_member_productions(SortRole::Defined),
                "{numeral}"
            );
        }
        assert!(universe.member(&mint("32")).is_some());
        assert!(universe.member(&Sort::new("32")).is_none());
    }

    /// A declaration's own parameters bind its sort as a production's bind its positions:
    /// `syntax {X} X` declares no sort, while `syntax {X} Foo` declares `Foo`, which the binder
    /// does not mention.
    #[test]
    fn a_sort_declaration_binds_its_own_parameters() {
        let x = Sort::new("X");
        let sentences = [
            Sentence::SyntaxSort {
                parameters: vec![x.clone()],
                sort: x.clone(),
                attributes: Attributes::default(),
            },
            Sentence::SyntaxSort {
                parameters: vec![x.clone()],
                sort: Sort::new("Foo"),
                attributes: Attributes::default(),
            },
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        assert!(universe.member(&x).is_none());
        assert!(universe.member(&Sort::new("Foo")).is_some());
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
        assert_eq!(casts[0].projection_operand(), Some(Sort::new("K")));
        assert!(universe.member(&Sort::new("Wad")).is_none());
        #[cfg(debug_assertions)]
        {
            assert!(universe.admits(&Sort::new("Wad")));
            assert!(universe.admits(&Sort::new("Rat")));
            assert!(!universe.admits(&Sort::new("Int")));
        }
    }

    /// A synonym whose target the view neither declares nor positions names no sort of the
    /// grammar: it has no casts, and its alias is not a sort a generated production may mention.
    /// Nor does a synonym of a shape with a free parameter (`syntax {W} Word = MInt{W}`), which
    /// is never a member.
    #[test]
    fn a_synonym_of_no_sort_of_the_grammar_has_no_casts() {
        let synonym = |alias: &str, target: Sort| Sentence::SortSynonym {
            new_sort: Sort::new(alias),
            old_sort: target,
            attributes: Attributes::default(),
        };
        let sentences = [
            synonym("New", Sort::new("Old")),
            syntax_sort(mint("8")),
            synonym("Word", mint("W")),
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        assert_eq!(universe.synonym_casts().count(), 0);
        #[cfg(debug_assertions)]
        for alias in ["New", "Word", "Old"] {
            assert!(!universe.admits(&Sort::new(alias)), "{alias}");
        }
    }

    /// Control: a synonym of a nullary kernel sort, which every grammar has, keeps its casts.
    #[test]
    fn a_synonym_of_a_kernel_sort_has_casts() {
        let sentences = [Sentence::SortSynonym {
            new_sort: Sort::new("Item"),
            old_sort: KernelSort::KItem.sort(),
            attributes: Attributes::default(),
        }];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        let casts = universe.synonym_casts().collect::<Vec<_>>();
        assert_eq!(casts.len(), 1);
        assert_eq!(casts[0].cast(), &Sort::new("Item"));
        assert_eq!(casts[0].label(), &KernelSort::KItem.sort());
        #[cfg(debug_assertions)]
        assert!(universe.admits(&Sort::new("Item")));
    }

    /// The projection cast `{K}:>S` lowers to `project:S`, which compilation declares for `K`,
    /// `KItem` and `Bool` and for no other kernel sort, so only their kernel casts have it.
    #[test]
    fn kernel_casts_have_the_projection_cast_exactly_for_k_kitem_and_bool() {
        for kernel in KernelSort::ALL {
            let target = CastTarget::kernel(kernel);
            assert_eq!(target.cast(), &kernel.sort());
            assert_eq!(target.label(), &kernel.sort());
            let expected = match kernel {
                KernelSort::K | KernelSort::KItem | KernelSort::Bool => Some(Sort::new("K")),
                KernelSort::KConfigVar
                | KernelSort::KBott
                | KernelSort::KLabel
                | KernelSort::KList
                | KernelSort::KString
                | KernelSort::Bag
                | KernelSort::Cell => None,
            };
            assert_eq!(target.projection_operand(), expected, "{}", kernel.name());
        }
    }

    /// A defined member and a declared instance have a sort projection, so their casts include
    /// `{K}:>S`; a numeral member has none, so its casts do not.
    #[test]
    fn member_casts_have_the_projection_cast_exactly_for_a_sort_with_a_projection() {
        let sentences = [
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("8"),
                items: vec![ProductionItem::Terminal("eight".into())],
                attributes: Attributes::default(),
            },
            syntax_sort(Sort::new("Foo")),
            syntax_sort(mint("8")),
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        let projection_operand = |sort: &Sort| {
            let member = universe
                .member(sort)
                .unwrap_or_else(|| panic!("{sort} is a member"));
            CastTarget::member(&member).projection_operand()
        };
        assert_eq!(projection_operand(&Sort::new("8")), None);
        assert_eq!(projection_operand(&Sort::new("Foo")), Some(Sort::new("K")));
        assert_eq!(projection_operand(&mint("8")), Some(Sort::new("K")));
    }

    /// A synonym's projection cast lowers to the projection of its target, so a synonym of a
    /// sort without a projection (`Bag`, a numeral member) has no projection cast; its other
    /// casts remain.
    #[test]
    fn a_synonym_of_a_sort_without_a_projection_has_no_projection_cast() {
        let synonym = |alias: &str, target: Sort| Sentence::SortSynonym {
            new_sort: Sort::new(alias),
            old_sort: target,
            attributes: Attributes::default(),
        };
        let sentences = [
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("8"),
                items: vec![ProductionItem::Terminal("eight".into())],
                attributes: Attributes::default(),
            },
            synonym("Bg", KernelSort::Bag.sort()),
            synonym("W", Sort::new("8")),
        ];
        let visible = sentences.iter().collect::<Vec<_>>();

        let universe = SortUniverse::new(&visible);

        let casts = universe.synonym_casts().collect::<Vec<_>>();
        assert_eq!(casts.len(), 2);
        assert_eq!(casts[0].cast(), &Sort::new("Bg"));
        assert_eq!(casts[0].label(), &KernelSort::Bag.sort());
        assert_eq!(casts[0].projection_operand(), None);
        assert_eq!(casts[1].cast(), &Sort::new("W"));
        assert_eq!(casts[1].label(), &Sort::new("8"));
        assert_eq!(casts[1].projection_operand(), None);
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

    /// The tables of CBC-05 section 2.3, except the `Nat` rows, which equal the `Defined` rows (a
    /// numeral member is a sort a sentence declares or positions), and the rule grammar's sort
    /// predicate and projection columns, which are the role predicates compilation generates the
    /// same helpers from. The other columns are those of the struct, in field order.
    #[test]
    fn plan_tables_are_pinned() {
        use KernelSort as S;
        let rule_member = |role: SortRole| {
            let row = rule_member_productions(role);
            [
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
            let row = rule_member_productions(role);
            assert_eq!(
                [row.predicate, row.projection],
                [role.has_sort_predicate(), role.has_sort_projection()],
                "{role:?}"
            );
            let expected_helpers = match role {
                SortRole::Defined | SortRole::Kernel(S::K | S::KItem | S::Bool) => [true, true],
                SortRole::Kernel(S::KConfigVar) => [true, false],
                SortRole::Nat
                | SortRole::Kernel(
                    S::KLabel | S::KList | S::KString | S::KBott | S::Bag | S::Cell,
                )
                | SortRole::RigidVariable
                | SortRole::Scaffolding => [false, false],
            };
            assert_eq!(
                [row.predicate, row.projection],
                expected_helpers,
                "{role:?}"
            );
            let every_rule_production = vec![true; rule_member(role).len()];
            let no_rule_production = vec![false; rule_member(role).len()];
            let expected_rule = match role {
                SortRole::Defined | SortRole::Nat => every_rule_production,
                SortRole::Kernel(S::Bool) => vec![
                    #[cfg(not(feature = "z3-inference"))]
                    true,
                    false,
                    false,
                    false,
                    true,
                ],
                // Every production except `KItem ::= S`.
                SortRole::Kernel(S::KLabel | S::KList | S::KString) => vec![
                    #[cfg(not(feature = "z3-inference"))]
                    true,
                    false,
                    true,
                    true,
                    true,
                ],
                SortRole::Kernel(S::K | S::KItem | S::KConfigVar | S::KBott | S::Bag | S::Cell)
                | SortRole::RigidVariable
                | SortRole::Scaffolding => no_rule_production,
            };
            assert_eq!(rule_member(role).to_vec(), expected_rule, "{role:?}");
            let expected_configuration = match role {
                SortRole::Defined | SortRole::Nat => [true, true, true, true],
                SortRole::Kernel(S::KLabel | S::KList | S::KString) => [true, false, true, true],
                SortRole::Kernel(
                    S::Bool | S::K | S::KItem | S::Bag | S::Cell | S::KBott | S::KConfigVar,
                ) => [true, false, false, false],
                SortRole::RigidVariable | SortRole::Scaffolding => [false, false, false, false],
            };
            assert_eq!(
                configuration_member(role),
                expected_configuration,
                "{role:?}"
            );
        }

        let rule_seeds = |order: &SeedOrder, column: fn(RuleKernelSeeds) -> bool| {
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

    /// The runtime twin of the `const` assertion over [`member_subsorts_are_granted`]: no row of
    /// either member table states a kernel position the sort's role denies. A label, an argument
    /// sequence and a token spelling are not K items, so `KLabel`, `KList` and `KString` receive
    /// no `KItem ::= S`.
    #[test]
    fn member_subsort_columns_state_only_granted_kernel_positions() {
        let mut denied = Vec::new();
        for role in every_role() {
            let rule = rule_member_productions(role);
            let configuration = configuration_member_productions(role);
            if rule.kitem_subsort && !role.lies_below_kitem() {
                denied.push(format!("rule KItem ::= {role:?}"));
            }
            if configuration.kitem_subsort && !role.lies_below_kitem() {
                denied.push(format!("configuration KItem ::= {role:?}"));
            }
            if rule.bottom_subsort && !role.admits_variables() {
                denied.push(format!("rule {role:?} ::= KBott"));
            }
            if configuration.variable_subsorts && !role.admits_variables() {
                denied.push(format!(
                    "configuration {role:?} ::= KConfigVar | #KVariable"
                ));
            }
        }
        assert!(
            denied.is_empty(),
            "member tables state kernel positions the roles deny: {denied:#?}"
        );
    }

    /// The control of [`checked_order`]: an ordering that repeats, omits or adds a kernel sort is
    /// not a permutation of [`KernelSort::ALL`].
    #[test]
    fn an_ordering_that_repeats_omits_or_adds_a_kernel_sort_is_rejected() {
        let all = KernelSort::ALL;
        assert!(is_permutation_of_all(&all));
        let mut reversed = all;
        reversed.reverse();
        assert!(is_permutation_of_all(&reversed));

        let mut repeated = all;
        repeated[all.len() - 1] = KernelSort::K;
        assert!(!is_permutation_of_all(&repeated));
        // One kernel sort short: the length an ordering array written before a kernel sort was
        // added to `ALL` has.
        assert!(!is_permutation_of_all(&all[..all.len() - 1]));
        let mut longer = all.to_vec();
        longer.push(KernelSort::K);
        assert!(!is_permutation_of_all(&longer));
    }
}
