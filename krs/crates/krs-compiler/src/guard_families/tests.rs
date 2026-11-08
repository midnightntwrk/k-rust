//! Unit tests of the guard families: families, atoms, the components a
//! flip may take, bit flips of `k::bits!` tables, and what is not generated.

use std::cell::Cell;
use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ConfigurationRoot, FixedCell,
    FixedConfiguration, FixedInitializerCell, GrammarProductionItem, InsertedNode, ItemKind,
    ModuleId, NodeOrigin, OriginFrame, PackageId, ProductionAttribute, ProductionFieldId,
    SemanticId, SentenceKind, SourceMapKey, StableItemId,
};
use krs_ir_levels::{
    IrCondition, SemanticLevel, SemanticModule, SemanticNondetGroup, SemanticProduction,
    SemanticRule, SemanticRuleCondition, SemanticSortRef as Sort, SemanticTerm,
};

use super::{
    AtomKind, FamilyKind, FlipOperator, GuardFamily, NotGeneratedReason,
    equation_pairs_outside_unifications,
};

/// The guard families of `modules`, once every pair of equations the
/// equation check finds may both apply is checked to be among their
/// unifications.
fn guard_families(modules: &[SemanticModule]) -> Vec<GuardFamily> {
    let (_, missing) = equation_pairs_outside_unifications(modules);
    assert!(missing.is_empty(), "{missing:#?}");
    super::guard_families(modules)
}

use BuiltinOperation::{
    BoolAnd, BoolNot, IntBitRange, IntEqual, IntGreaterEqual, IntLess, IntNotEqual,
};

/// A fixed run of a template: offset, length, value.
type Run = (u32, u32, i128);

const INT: Sort = Sort::Builtin(BuiltinSort::Int);
const BOOL: Sort = Sort::Builtin(BuiltinSort::Bool);
const K: Sort = Sort::Builtin(BuiltinSort::KSequence);

fn package() -> PackageId {
    PackageId::new("FLIPS", "flips", "0.1.0", "test").unwrap()
}

fn item(name: &str, kind: ItemKind) -> StableItemId {
    StableItemId::new(package(), ["fixture"], name, kind, "").unwrap()
}

fn sid(name: &str) -> SemanticId {
    SemanticId::new(name.to_owned()).unwrap()
}

/// Builds terms whose nodes each get a fresh source-map key and, unless a
/// construct is named, a fresh authored range.
#[derive(Default)]
struct Terms {
    next: Cell<u32>,
}

impl Terms {
    fn key(&self) -> SourceMapKey {
        let next = self.next.get() + 1;
        self.next.set(next);
        SourceMapKey::new(format!("sem.flips.{next}")).unwrap()
    }

    /// A node of its own construct.
    fn fresh(&self) -> NodeOrigin {
        let key = self.key();
        let start = 10_000 + 10 * self.next.get();
        NodeOrigin::new(key, krs_ir::testing::authored(start, start + 5))
    }

    /// A node rendering the construct at `start`.
    fn at(&self, start: u32) -> NodeOrigin {
        NodeOrigin::new(self.key(), krs_ir::testing::authored(start, start + 1))
    }

    /// A node KRS inserted.
    fn inserted(&self, kind: InsertedNode) -> NodeOrigin {
        let mut stack = krs_ir::testing::authored(1, 2);
        stack.push(OriginFrame::inserted(kind, None));
        NodeOrigin::new(self.key(), stack)
    }

    fn var(&self, name: &str, sort: Sort) -> SemanticTerm {
        SemanticTerm::variable(self.fresh(), sort, sid(name))
    }

    fn int(&self, value: i128) -> SemanticTerm {
        SemanticTerm::token(self.fresh(), INT, value.to_string()).unwrap()
    }

    fn builtin_at(
        origin: NodeOrigin,
        operation: BuiltinOperation,
        arguments: Vec<SemanticTerm>,
    ) -> SemanticTerm {
        let sort = Sort::Builtin(operation.result_sort().builtin().unwrap());
        SemanticTerm::application(origin, sort, ApplicationRef::Builtin(operation), arguments)
    }

    fn builtin(&self, operation: BuiltinOperation, arguments: Vec<SemanticTerm>) -> SemanticTerm {
        Self::builtin_at(self.fresh(), operation, arguments)
    }

    /// `name(arguments)`, a declared application of sort `sort`.
    fn apply_at(
        origin: NodeOrigin,
        name: &str,
        sort: Sort,
        arguments: Vec<SemanticTerm>,
    ) -> SemanticTerm {
        SemanticTerm::application(
            origin,
            sort,
            ApplicationRef::Declared(item(name, ItemKind::Constructor)),
            arguments,
        )
    }

    fn apply(&self, name: &str, sort: Sort, arguments: Vec<SemanticTerm>) -> SemanticTerm {
        Self::apply_at(self.fresh(), name, sort, arguments)
    }

    fn not(&self, term: SemanticTerm) -> SemanticTerm {
        self.builtin(BoolNot, vec![term])
    }

    fn all(&self, conjuncts: Vec<SemanticTerm>) -> SemanticTerm {
        conjuncts
            .into_iter()
            .reduce(|left, right| self.builtin(BoolAnd, vec![left, right]))
            .unwrap()
    }

    /// The conjuncts `k::bits!` adds to a guard on binder `name`, every node
    /// rendering the template's range at `start`, as the desugaring spans
    /// every token of the guard: `x >= 0`, `x < 2^w`, and one equality per
    /// fixed run (offset, length, value).
    fn template(&self, start: u32, name: &str, width: u32, runs: &[Run]) -> Vec<SemanticTerm> {
        let var = || SemanticTerm::variable(self.at(start), INT, sid(name));
        let int =
            |value: i128| SemanticTerm::token(self.at(start), INT, value.to_string()).unwrap();
        let mut conjuncts = vec![
            Self::builtin_at(self.at(start), IntGreaterEqual, vec![var(), int(0)]),
            Self::builtin_at(self.at(start), IntLess, vec![var(), int(1 << width)]),
        ];
        for (offset, length, value) in runs {
            let range = Self::builtin_at(
                self.at(start),
                IntBitRange,
                vec![var(), int(i128::from(*offset)), int(i128::from(*length))],
            );
            conjuncts.push(Self::builtin_at(
                self.at(start),
                IntEqual,
                vec![range, int(*value)],
            ));
        }
        conjuncts
    }
}

fn condition(terms: &Terms, guard: SemanticTerm) -> IrCondition<SemanticLevel> {
    IrCondition::Bool(SemanticRuleCondition::new(terms.fresh(), guard))
}

/// An equation `function(arguments) => 0 requires guard`.
fn equation(
    terms: &Terms,
    name: &str,
    function: &str,
    arguments: Vec<SemanticTerm>,
    guard: Option<SemanticTerm>,
) -> SemanticRule {
    let head = terms.apply(function, INT, arguments);
    let body = SemanticTerm::rewrite(terms.fresh(), INT, head, terms.int(0)).unwrap();
    SemanticRule::new(
        terms.fresh(),
        item(name, ItemKind::Equation),
        SentenceKind::Equation,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_requires(guard.map(|guard| condition(terms, guard)))
    .unwrap()
}

/// A transition `Boundary(binders) => .K requires guard` at the head of the
/// computation cell.
fn transition(
    terms: &Terms,
    name: &str,
    binders: &[&str],
    guard: Option<SemanticTerm>,
) -> SemanticRule {
    let arguments = binders
        .iter()
        .map(|binder| terms.var(binder, BOOL))
        .collect();
    let head = terms.apply("Boundary", K, arguments);
    let empty = SemanticTerm::k_sequence(terms.fresh(), K, Vec::new());
    let body = SemanticTerm::rewrite(terms.fresh(), K, head, empty).unwrap();
    SemanticRule::new(
        terms.fresh(),
        item(name, ItemKind::Rule),
        SentenceKind::Transition,
        Vec::new(),
        body,
    )
    .unwrap()
    .with_requires(guard.map(|guard| condition(terms, guard)))
    .unwrap()
}

/// A function `name(x: Int) -> Int`.
fn function(terms: &Terms, name: &str) -> SemanticProduction {
    function_of(terms, name, &[INT])
}

/// A function `name(x0: sorts[0], ..) -> Int`.
fn function_of(terms: &Terms, name: &str, sorts: &[Sort]) -> SemanticProduction {
    let mut items = vec![
        GrammarProductionItem::terminal(terms.fresh(), name).unwrap(),
        GrammarProductionItem::terminal(terms.fresh(), "(").unwrap(),
    ];
    for (index, sort) in sorts.iter().enumerate() {
        if index > 0 {
            items.push(GrammarProductionItem::terminal(terms.fresh(), ",").unwrap());
        }
        items.push(GrammarProductionItem::non_terminal(
            terms.fresh(),
            ProductionFieldId::new(format!("x{index}")).unwrap(),
            sort.clone(),
        ));
    }
    items.push(GrammarProductionItem::terminal(terms.fresh(), ")").unwrap());
    SemanticProduction::new(
        terms.fresh(),
        item(name, ItemKind::Constructor),
        INT,
        items,
        vec![ProductionAttribute::Function {
            origin: terms.fresh(),
        }],
    )
    .unwrap()
}

/// The fixed configuration of one computation cell `k`.
fn configuration(terms: &Terms) -> krs_ir_levels::SemanticConfiguration {
    FixedConfiguration::new(
        terms.fresh(),
        sid("configuration.flips"),
        ConfigurationRoot::GeneratedTop,
        vec![FixedCell::leaf(terms.fresh(), sid("cell.k"), "k", Vec::new(), K).unwrap()],
        terms.fresh(),
        sid("initializer.flips"),
        Vec::new(),
        vec![FixedInitializerCell::term(
            terms.fresh(),
            sid("cell.k"),
            SemanticTerm::k_sequence(terms.fresh(), K, Vec::new()),
        )],
    )
    .unwrap()
}

fn module(terms: &Terms, functions: &[&str], rules: Vec<SemanticRule>) -> SemanticModule {
    let functions = functions.iter().map(|name| function(terms, name)).collect();
    module_of(terms, functions, rules)
}

fn module_of(
    terms: &Terms,
    functions: Vec<SemanticProduction>,
    rules: Vec<SemanticRule>,
) -> SemanticModule {
    let configuration = rules
        .iter()
        .any(|rule| rule.kind() == SentenceKind::Transition)
        .then(|| configuration(terms));
    SemanticModule::new(
        terms.fresh(),
        ModuleId::new("FLIPS").unwrap(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        functions,
        Vec::new(),
        Vec::new(),
        configuration,
        rules,
    )
}

/// The one family of `families`.
fn only(families: &[GuardFamily]) -> &GuardFamily {
    assert_eq!(families.len(), 1, "{families:#?}");
    &families[0]
}

/// The head an atom's flips are named by.
fn head(family: &GuardFamily, atom: usize) -> String {
    match &family.atoms[atom].kind {
        AtomKind::Boolean { head } => head.clone(),
        AtomKind::Bit { bit, .. } => format!("bit{bit}"),
    }
}

/// Each obligation as (operator, atom head, flipped sentence names).
fn obligations(family: &GuardFamily) -> Vec<(FlipOperator, String, Vec<String>)> {
    family
        .obligations
        .iter()
        .map(|flip| {
            let names = flip
                .sentences
                .iter()
                .map(|sentence| family.sentences[*sentence].rule.item_name().to_owned())
                .collect();
            (flip.operator, head(family, flip.atom), names)
        })
        .collect()
}

/// The obligations of the atom named `name`.
fn obligations_of(family: &GuardFamily, name: &str) -> Vec<(FlipOperator, String, Vec<String>)> {
    obligations(family)
        .into_iter()
        .filter(|(_, head, _)| head == name)
        .collect()
}

fn names(list: &[&str]) -> Vec<String> {
    list.iter().map(|name| (*name).to_owned()).collect()
}

fn flip(head: &str, sentences: &[&str]) -> (FlipOperator, String, Vec<String>) {
    (FlipOperator::Flip, head.to_owned(), names(sentences))
}

fn bit_flip(bit: u32, sentences: &[&str]) -> (FlipOperator, String, Vec<String>) {
    (FlipOperator::BitFlip, format!("bit{bit}"), names(sentences))
}

/// The four boundary transitions on `Boundary(H, I, P)`: dispatch and step
/// split `!H` by `Dispatches(I, P)`, wake and halted split `H` by
/// `Requested(P)`. Each rule's tests are its own authored constructs.
fn boundary(terms: &Terms) -> Vec<SemanticRule> {
    let halted = || terms.var("H", BOOL);
    let dispatches = || {
        terms.apply(
            "Dispatches",
            BOOL,
            vec![terms.var("I", BOOL), terms.var("P", BOOL)],
        )
    };
    let requested = || terms.apply("Requested", BOOL, vec![terms.var("P", BOOL)]);
    let binders = ["H", "I", "P"];
    vec![
        transition(
            terms,
            "boundary_dispatch",
            &binders,
            Some(terms.all(vec![terms.not(halted()), dispatches()])),
        ),
        transition(
            terms,
            "boundary_step",
            &binders,
            Some(terms.all(vec![terms.not(halted()), terms.not(dispatches())])),
        ),
        transition(
            terms,
            "boundary_wake",
            &binders,
            Some(terms.all(vec![halted(), requested()])),
        ),
        transition(
            terms,
            "boundary_halted",
            &binders,
            Some(terms.all(vec![halted(), terms.not(requested())])),
        ),
    ]
}

#[test]
fn complementary_boundary_rules_form_one_family_with_three_atoms() {
    let terms = Terms::default();
    let modules = [module(&terms, &[], boundary(&terms))];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(family.kind, FamilyKind::Rules { priority: 50 });
    assert_eq!(family.sentences.len(), 4);
    let heads = (0..family.atoms.len())
        .map(|atom| head(family, atom))
        .collect::<Vec<_>>();
    assert_eq!(heads, names(&["H", "Dispatches", "Requested"]));
    assert_eq!(
        obligations(family),
        vec![
            flip(
                "H",
                &[
                    "boundary_dispatch",
                    "boundary_halted",
                    "boundary_step",
                    "boundary_wake"
                ]
            ),
            flip("Dispatches", &["boundary_dispatch", "boundary_step"]),
            flip("Requested", &["boundary_halted", "boundary_wake"]),
        ]
    );
    assert!(family.obligations.iter().all(|flip| flip.whole));
    assert_eq!(family.obligations[0].id, "flip--boundary_dispatch+3--H");
    assert_eq!(
        family.obligations[2].id,
        "flip--boundary_halted+boundary_wake--Requested"
    );
    assert!(
        family.not_generated.is_empty(),
        "{:#?}",
        family.not_generated
    );
}

/// `Vector(R)` as an `if` chain of six branches over five conditions
/// `C1(R)`..`C5(R)`: branch `i` is guarded by the negations of the earlier
/// conditions (renderings of their constructs) and its own condition.
fn chain(terms: &Terms) -> Vec<SemanticRule> {
    let condition = |index: u32| {
        Terms::apply_at(
            terms.at(100 * index),
            &format!("C{index}"),
            BOOL,
            vec![terms.var("R", INT)],
        )
    };
    (1..=6)
        .map(|branch| {
            let mut conjuncts = (1..branch)
                .map(|earlier| terms.not(condition(earlier)))
                .collect::<Vec<_>>();
            if branch < 6 {
                conjuncts.push(condition(branch));
            }
            equation(
                terms,
                &format!("vector_{branch}"),
                "Vector",
                vec![terms.var("R", INT)],
                Some(terms.all(conjuncts)),
            )
        })
        .collect()
}

#[test]
fn an_if_else_chain_is_flattened_and_each_flip_touches_every_rendering() {
    let terms = Terms::default();
    let modules = [module(&terms, &["Vector"], chain(&terms))];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(family.atoms.len(), 5);
    for (index, atom) in family.atoms.iter().enumerate() {
        assert_eq!(
            atom.kind,
            AtomKind::Boolean {
                head: format!("C{}", index + 1)
            }
        );
        // Condition `i` is rendered in its own branch and every later one.
        assert_eq!(atom.occurrences.len(), 6 - index);
    }
    let flips = obligations(family);
    assert_eq!(flips.len(), 5);
    for (index, (operator, head, sentences)) in flips.iter().enumerate() {
        assert_eq!(*operator, FlipOperator::Flip);
        assert_eq!(*head, format!("C{}", index + 1));
        let expected = (index + 1..=6)
            .map(|branch| format!("vector_{branch}"))
            .collect::<Vec<_>>();
        assert_eq!(*sentences, expected);
    }
}

/// A deterministic pseudo-random sequence (a 64-bit LCG).
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from(self.0 >> 33).unwrap() % bound
    }
}

/// One leaf of a decision tree: its (atom, polarity) literals.
type Leaf = Vec<(u32, bool)>;

/// The leaves of a random decision tree over atoms `0..atoms`.
fn random_partition(random: &mut Lcg, atoms: u32, path: &mut Leaf, leaves: &mut Vec<Leaf>) {
    let free = (0..atoms)
        .filter(|atom| path.iter().all(|(used, _)| used != atom))
        .collect::<Vec<_>>();
    if free.is_empty() || (!path.is_empty() && random.below(4) == 0) {
        leaves.push(path.clone());
        return;
    }
    let atom = free[random.below(free.len())];
    for polarity in [true, false] {
        path.push((atom, polarity));
        random_partition(random, atoms, path, leaves);
        path.pop();
    }
}

#[test]
fn a_whole_flip_keeps_a_propositional_partition() {
    for seed in 0..40 {
        let mut random = Lcg(seed);
        let atoms = 2 + u32::try_from(random.below(3)).unwrap();
        let mut leaves = Vec::new();
        random_partition(&mut random, atoms, &mut Vec::new(), &mut leaves);
        let terms = Terms::default();
        let rules = leaves
            .iter()
            .enumerate()
            .map(|(index, leaf)| {
                let conjuncts = leaf
                    .iter()
                    .map(|(atom, polarity)| {
                        let test =
                            terms.apply(&format!("A{atom}"), BOOL, vec![terms.var("X", INT)]);
                        if *polarity { test } else { terms.not(test) }
                    })
                    .collect::<Vec<_>>();
                equation(
                    &terms,
                    &format!("leaf_{index:02}"),
                    "F",
                    vec![terms.var("X", INT)],
                    Some(terms.all(conjuncts)),
                )
            })
            .collect();
        let modules = [module(&terms, &["F"], rules)];
        let families = guard_families(&modules);
        let family = only(&families);
        assert!(
            family.not_generated.is_empty(),
            "seed {seed}: {:#?}",
            family.not_generated
        );
        // Each flipped family is still a partition of the valuations.
        for flip in &family.obligations {
            let atom = head(family, flip.atom)
                .trim_start_matches('A')
                .parse::<u32>()
                .unwrap();
            let flipped = flip
                .sentences
                .iter()
                .map(|sentence| {
                    let name = family.sentences[*sentence].rule.item_name();
                    name.trim_start_matches("leaf_").parse::<usize>().unwrap()
                })
                .collect::<BTreeSet<_>>();
            for valuation in 0_u32..1 << atoms {
                let holding = leaves
                    .iter()
                    .enumerate()
                    .filter(|(index, leaf)| {
                        leaf.iter().all(|(tested, polarity)| {
                            let value = (valuation >> tested) & 1 == 1;
                            let value = value ^ (*tested == atom && flipped.contains(index));
                            value == *polarity
                        })
                    })
                    .count();
                assert_eq!(
                    holding, 1,
                    "seed {seed}, {}, valuation {valuation:b}",
                    flip.id
                );
            }
        }
        // Every atom a leaf tests has obligations.
        let tested = leaves
            .iter()
            .flatten()
            .map(|(atom, _)| *atom)
            .collect::<BTreeSet<_>>();
        let flipped = family
            .obligations
            .iter()
            .map(|flip| flip.atom)
            .collect::<BTreeSet<_>>();
        assert_eq!(flipped.len(), tested.len(), "seed {seed}");
    }
}

/// The fetch rules' grid: `Bug` × `InRom`, one rule per combination.
fn grid(terms: &Terms) -> Vec<SemanticRule> {
    let bug = || terms.apply("Bug", BOOL, vec![terms.var("I", BOOL)]);
    let rom = || terms.apply("InRom", BOOL, vec![terms.var("P", BOOL)]);
    [
        ("fetch_bug_rom", true, true),
        ("fetch_bug_ram", true, false),
        ("fetch_rom", false, true),
        ("fetch_ram", false, false),
    ]
    .into_iter()
    .map(|(name, is_bug, in_rom)| {
        let bug = if is_bug { bug() } else { terms.not(bug()) };
        let rom = if in_rom { rom() } else { terms.not(rom()) };
        transition(
            terms,
            name,
            &["H", "I", "P"],
            Some(terms.all(vec![bug, rom])),
        )
    })
    .collect()
}

#[test]
fn components_of_a_grid_family() {
    let terms = Terms::default();
    let modules = [module(&terms, &[], grid(&terms))];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        obligations(family),
        vec![
            flip("Bug", &["fetch_bug_ram", "fetch_ram"]),
            flip("Bug", &["fetch_bug_rom", "fetch_rom"]),
            flip("InRom", &["fetch_bug_ram", "fetch_bug_rom"]),
            flip("InRom", &["fetch_ram", "fetch_rom"]),
        ]
    );
    assert!(family.obligations.iter().all(|flip| !flip.whole));
}

/// Two transitions on `Boundary(heads)` whose guards test `Less` of two
/// binders, the second one negated.
fn less_pair(terms: &Terms, left: [&str; 2], right: [&str; 2]) -> Vec<SemanticRule> {
    let less = |binders: [&str; 2]| {
        let arguments = binders
            .iter()
            .map(|binder| terms.var(binder, BOOL))
            .collect();
        terms.apply("Less", BOOL, arguments)
    };
    vec![
        transition(terms, "less", &left, Some(less(["X", "Y"]))),
        transition(terms, "not_less", &right, Some(terms.not(less(["X", "Y"])))),
    ]
}

#[test]
fn atoms_are_identified_under_the_head_unifier_not_by_name() {
    // Other names at the same positions: `Less(X, Y)` and `Less(X, Y)` of
    // heads `Boundary(X, Y)` and `Boundary(X, Y)` are one atom; so would be
    // any renaming.
    let terms = Terms::default();
    let modules = [module(
        &terms,
        &[],
        less_pair(&terms, ["X", "Y"], ["X", "Y"]),
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(family.atoms.len(), 1);
    assert_eq!(
        obligations(family),
        vec![flip("Less", &["less", "not_less"])]
    );
    // The same names at swapped positions: under the unifier of
    // `Boundary(X, Y)` and `Boundary(Y, X)`, `Less(X, Y)` meets
    // `Less(Y, X)`: two atoms, and nothing complementary keeps the pair
    // apart.
    let terms = Terms::default();
    let modules = [module(
        &terms,
        &[],
        less_pair(&terms, ["X", "Y"], ["Y", "X"]),
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(family.atoms.len(), 2);
    assert!(family.obligations.is_empty());
    assert!(!family.not_generated.is_empty());
    assert!(family.not_generated.iter().all(|refused| {
        refused.reason == NotGeneratedReason::TheorySeparated && refused.pair == Some([0, 1])
    }));
}

#[test]
fn guard_meaning_complements_are_one_atom() {
    let terms = Terms::default();
    let below = terms.builtin(IntLess, vec![terms.var("V", INT), terms.int(128)]);
    let above = terms.builtin(IntGreaterEqual, vec![terms.var("V", INT), terms.int(128)]);
    let modules = [module(
        &terms,
        &["Signed"],
        vec![
            equation(
                &terms,
                "signed_positive",
                "Signed",
                vec![terms.var("V", INT)],
                Some(below),
            ),
            equation(
                &terms,
                "signed_negative",
                "Signed",
                vec![terms.var("V", INT)],
                Some(above),
            ),
        ],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(family.atoms.len(), 1);
    // Sentences in identity order: negative (`>=`) first.
    let polarities = family.atoms[0]
        .occurrences
        .iter()
        .map(|occurrence| occurrence.positive)
        .collect::<Vec<_>>();
    assert_eq!(polarities, [true, false]);
    assert_eq!(
        obligations(family),
        vec![flip(
            "IntGreaterEqual",
            &["signed_negative", "signed_positive"]
        )]
    );
}

#[test]
fn a_literal_separated_pair_is_not_generated() {
    let terms = Terms::default();
    let other = terms.builtin(IntNotEqual, vec![terms.var("X", INT), terms.int(0)]);
    let modules = [module(
        &terms,
        &["F"],
        vec![
            equation(&terms, "f_zero", "F", vec![terms.int(0)], None),
            equation(
                &terms,
                "f_other",
                "F",
                vec![terms.var("X", INT)],
                Some(other),
            ),
        ],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(family.obligations.is_empty());
    assert_eq!(family.not_generated.len(), 1);
    let refused = &family.not_generated[0];
    assert_eq!(refused.reason, NotGeneratedReason::TheorySeparated);
    assert_eq!(refused.reason.as_str(), "theory-separated");
    // Sentences in identity order: `f_other`, `f_zero`.
    assert_eq!(refused.pair, Some([0, 1]));
}

/// An 8-bit decode table: inc and dec differ in bit 0, halt is the literal
/// `0x76`, ld's template `01 yyy zzz` has the hole `op != 0x76`, and nop and
/// `ld_bc` are the literals `0x00` and `0x01`, which differ in bit 0.
fn decode(terms: &Terms) -> Vec<SemanticRule> {
    let templated = |name: &str, start: u32, runs: &[Run], extra: Vec<SemanticTerm>| {
        let mut conjuncts = terms.template(start, "Op", 8, runs);
        conjuncts.extend(extra);
        let guard = Some(terms.all(conjuncts));
        equation(terms, name, "Decode", vec![terms.var("Op", INT)], guard)
    };
    let hole = terms.builtin(IntNotEqual, vec![terms.var("Op", INT), terms.int(0x76)]);
    vec![
        templated("decode_inc_r", 100, &[(6, 2, 0), (0, 3, 4)], Vec::new()),
        templated("decode_dec_r", 200, &[(6, 2, 0), (0, 3, 5)], Vec::new()),
        equation(terms, "decode_halt", "Decode", vec![terms.int(0x76)], None),
        equation(terms, "decode_nop", "Decode", vec![terms.int(0x00)], None),
        equation(terms, "decode_ld_bc", "Decode", vec![terms.int(0x01)], None),
        templated("decode_ld_r_r", 300, &[(6, 2, 1)], vec![hole]),
    ]
}

#[test]
fn bit_components_of_a_template_table() {
    let terms = Terms::default();
    let modules = [module(&terms, &["Decode"], decode(&terms))];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(
        family.not_generated.is_empty(),
        "{:#?}",
        family.not_generated
    );
    // The template conjuncts and the hole are no Boolean atoms.
    assert!(
        family
            .atoms
            .iter()
            .all(|atom| matches!(atom.kind, AtomKind::Bit { column: 0, .. }))
    );
    assert_eq!(
        obligations_of(family, "bit0"),
        vec![
            bit_flip(0, &["decode_dec_r", "decode_inc_r"]),
            bit_flip(0, &["decode_halt", "decode_ld_r_r"]),
            // Two literals whose patterns do not unify still collide once
            // one is flipped alone.
            bit_flip(0, &["decode_ld_bc", "decode_nop"]),
        ]
    );
    let ids = family
        .obligations
        .iter()
        .map(|flip| flip.id.as_str())
        .collect::<Vec<_>>();
    assert!(
        ids.contains(&"bitflip--decode_dec_r+decode_inc_r--bit0"),
        "{ids:?}"
    );
    // The hole moves with halt's literal: both are occurrences of bit 0.
    let atom = family
        .atoms
        .iter()
        .find(|atom| atom.kind == AtomKind::Bit { column: 0, bit: 0 })
        .unwrap();
    let position = |name: &str| {
        family
            .sentences
            .iter()
            .position(|sentence| sentence.rule.item_name() == name)
            .unwrap()
    };
    let (ld, halt) = (position("decode_ld_r_r"), position("decode_halt"));
    assert!(
        atom.occurrences
            .iter()
            .any(|occurrence| occurrence.sentence == ld)
    );
    assert!(
        atom.occurrences
            .iter()
            .any(|occurrence| occurrence.sentence == halt && !occurrence.positive)
    );
    // Bit 3 is a free bit of inc and dec, which do not mention it; nop and
    // ld_bc flipped there land on no other equation, so each is a component
    // of its own.
    assert_eq!(
        obligations_of(family, "bit3"),
        vec![
            bit_flip(3, &["decode_halt", "decode_ld_r_r"]),
            bit_flip(3, &["decode_ld_bc"]),
            bit_flip(3, &["decode_nop"]),
        ]
    );
}

#[test]
fn a_literal_only_table_has_no_bit_atoms() {
    let terms = Terms::default();
    let rules = (0..8)
        .map(|value| {
            equation(
                &terms,
                &format!("r8_{value}"),
                "R8",
                vec![terms.int(value)],
                None,
            )
        })
        .collect();
    let modules = [module(&terms, &["R8"], rules)];
    let families = guard_families(&modules);
    assert!(families.is_empty(), "{families:#?}");
}

#[test]
fn inserted_nodes_are_never_atoms() {
    let terms = Terms::default();
    let lookup = Terms::apply_at(
        terms.inserted(InsertedNode::LookupGuard),
        "InKeys",
        BOOL,
        vec![terms.var("P", BOOL)],
    );
    let defined = Terms::apply_at(
        terms.inserted(InsertedNode::DefinednessTest),
        "Defined",
        BOOL,
        vec![terms.var("I", BOOL)],
    );
    let inserted_keys = [
        lookup.origin().key().clone(),
        defined.origin().key().clone(),
    ];
    let ready = || terms.apply("Ready", BOOL, vec![terms.var("H", BOOL)]);
    let binders = ["H", "I", "P"];
    let template = terms.template(900, "Op", 4, &[(0, 2, 1)]);
    let template_keys = template
        .iter()
        .map(|conjunct| conjunct.origin().key().clone())
        .collect::<Vec<_>>();
    let mut conjuncts = template;
    conjuncts.push(terms.apply("Even", BOOL, vec![terms.var("Op", INT)]));
    let rules = vec![
        transition(
            &terms,
            "ready",
            &binders,
            Some(terms.all(vec![lookup, defined, ready()])),
        ),
        transition(&terms, "waiting", &binders, Some(terms.not(ready()))),
        equation(
            &terms,
            "pick_one",
            "Pick",
            vec![terms.var("Op", INT)],
            Some(terms.all(conjuncts)),
        ),
    ];
    let modules = [module(&terms, &["Pick"], rules)];
    let families = guard_families(&modules);
    let boolean = families
        .iter()
        .flat_map(|family| &family.atoms)
        .filter(|atom| matches!(atom.kind, AtomKind::Boolean { .. }))
        .collect::<Vec<_>>();
    let heads = boolean
        .iter()
        .map(|atom| match &atom.kind {
            AtomKind::Boolean { head } => head.as_str(),
            AtomKind::Bit { .. } => unreachable!(),
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(heads, BTreeSet::from(["Even", "Ready"]));
    let keys = boolean
        .iter()
        .flat_map(|atom| &atom.occurrences)
        .map(|occurrence| occurrence.key.clone())
        .collect::<BTreeSet<_>>();
    assert!(inserted_keys.iter().all(|key| !keys.contains(key)));
    assert!(template_keys.iter().all(|key| !keys.contains(key)));
    // The transition pair still flips its authored atom.
    let rules = families
        .iter()
        .find(|family| matches!(family.kind, FamilyKind::Rules { .. }))
        .unwrap();
    assert_eq!(
        obligations(rules),
        vec![flip("Ready", &["ready", "waiting"])]
    );
}

#[test]
fn nondet_and_spec_module_families_are_not_generated() {
    let terms = Terms::default();
    let raced = |name: &str| {
        transition(&terms, name, &["H", "I", "P"], Some(terms.var("H", BOOL)))
            .with_nondet_group(Some(SemanticNondetGroup::new(terms.fresh(), "race")))
    };
    let modules = [module(
        &terms,
        &[],
        vec![raced("race_left"), raced("race_right")],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(family.obligations.is_empty());
    assert!(
        family
            .not_generated
            .iter()
            .any(|refused| refused.atom.is_none() && refused.sentences == [0, 1])
    );
    assert!(
        family
            .not_generated
            .iter()
            .all(|refused| refused.reason == NotGeneratedReason::NondetGroup)
    );

    let terms = Terms::default();
    let low = terms.builtin(IntLess, vec![terms.var("X", INT), terms.int(4)]);
    let high = terms.builtin(IntGreaterEqual, vec![terms.var("X", INT), terms.int(4)]);
    let helper = module(
        &terms,
        &["Helper"],
        vec![
            equation(
                &terms,
                "helper_low",
                "Helper",
                vec![terms.var("X", INT)],
                Some(low),
            ),
            equation(
                &terms,
                "helper_high",
                "Helper",
                vec![terms.var("X", INT)],
                Some(high),
            ),
        ],
    )
    .into_spec();
    let families = guard_families(&[helper]);
    let family = only(&families);
    assert!(family.obligations.is_empty());
    assert_eq!(family.not_generated.len(), 1);
    assert_eq!(
        family.not_generated[0].reason,
        NotGeneratedReason::SpecModule
    );
}

#[test]
fn generation_is_deterministic() {
    let build = || {
        let terms = Terms::default();
        let mut rules = boundary(&terms);
        rules.extend(chain(&terms));
        rules.extend(decode(&terms));
        [module(&terms, &["Vector", "Decode"], rules)]
    };
    let first = guard_families(&build());
    assert_eq!(first, guard_families(&build()));
    assert_eq!(first.len(), 3);
    let ids = first
        .iter()
        .flat_map(|family| &family.obligations)
        .map(|flip| flip.id.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        ids.iter().collect::<BTreeSet<_>>().len(),
        ids.len(),
        "{ids:?}"
    );
}

#[test]
fn components_of_any_size_are_obligations() {
    // A 3-bit table: 000, 001 and 01x in the lower half, 100, 101 and 11x
    // in the upper. Flipping bit 1 links each half's three equations: two
    // components of three, both obligations, neither the whole flip.
    let terms = Terms::default();
    let table: [(&str, u32, &[Run]); 6] = [
        ("low_a", 100, &[(0, 3, 0)]),
        ("low_b", 200, &[(0, 3, 1)]),
        ("low_c", 300, &[(1, 2, 1)]),
        ("high_a", 400, &[(0, 3, 4)]),
        ("high_b", 500, &[(0, 3, 5)]),
        ("high_c", 600, &[(1, 2, 3)]),
    ];
    let rules = table
        .iter()
        .map(|(name, start, runs)| {
            let guard = Some(terms.all(terms.template(*start, "Op", 3, runs)));
            equation(&terms, name, "Table", vec![terms.var("Op", INT)], guard)
        })
        .collect();
    let modules = [module(&terms, &["Table"], rules)];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        obligations_of(family, "bit1"),
        vec![
            bit_flip(1, &["high_a", "high_b", "high_c"]),
            bit_flip(1, &["low_a", "low_b", "low_c"]),
        ]
    );
    assert!(
        family
            .obligations
            .iter()
            .filter(|flip| family.atoms[flip.atom].kind == AtomKind::Bit { column: 0, bit: 1 })
            .all(|flip| !flip.whole)
    );
}

/// The atoms of `kind` with their flipped sentence names, for each
/// obligation.
fn obligations_on(family: &GuardFamily, kind: &AtomKind) -> Vec<Vec<String>> {
    family
        .obligations
        .iter()
        .filter(|flip| family.atoms[flip.atom].kind == *kind)
        .map(|flip| {
            flip.sentences
                .iter()
                .map(|sentence| family.sentences[*sentence].rule.item_name().to_owned())
                .collect()
        })
        .collect()
}

#[test]
fn templates_sharing_the_condition_span_are_each_a_bit_argument() {
    // The desugaring gives every token of a sentence's template guards the
    // span of the authored condition's first token: both templates of
    // `two_a` and `two_b` render one range, and in `two_c` the authored
    // `F` that leads the condition renders it too.
    let terms = Terms::default();
    let shared = 700;
    let both = |name: &str, low: i128, high: i128| {
        let mut conjuncts = terms.template(shared, "A", 4, &[(3, 1, low)]);
        conjuncts.extend(terms.template(shared, "B", 4, &[(3, 1, high)]));
        equation(
            &terms,
            name,
            "Two",
            vec![
                terms.var("A", INT),
                terms.var("B", INT),
                terms.var("F", BOOL),
            ],
            Some(terms.all(conjuncts)),
        )
    };
    let flagged = |name: &str, flag: SemanticTerm| {
        let mut conjuncts = terms.template(shared, "A", 4, &[(3, 1, 1)]);
        conjuncts.push(flag);
        equation(
            &terms,
            name,
            "Two",
            vec![
                terms.var("A", INT),
                terms.var("B", INT),
                terms.var("F", BOOL),
            ],
            Some(terms.all(conjuncts)),
        )
    };
    let leading = SemanticTerm::variable(terms.at(shared), BOOL, sid("F"));
    let rules = vec![
        both("two_a", 0, 0),
        both("two_b", 0, 1),
        flagged("two_c", leading),
        flagged("two_d", terms.not(terms.var("F", BOOL))),
    ];
    let modules = [module_of(
        &terms,
        vec![function_of(&terms, "Two", &[INT, INT, BOOL])],
        rules,
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(
        family.not_generated.is_empty(),
        "{:#?}",
        family.not_generated
    );
    assert_eq!(
        obligations_on(family, &AtomKind::Bit { column: 0, bit: 3 }),
        vec![names(&["two_a", "two_b", "two_c", "two_d"])]
    );
    assert_eq!(
        obligations_on(family, &AtomKind::Bit { column: 1, bit: 3 }),
        vec![names(&["two_a", "two_b"])]
    );
    assert_eq!(
        obligations_of(family, "F"),
        vec![flip("F", &["two_c", "two_d"])]
    );
    // The two arguments' bit-3 flips get distinct identities.
    let ids = family
        .obligations
        .iter()
        .map(|flip| flip.id.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(ids.len(), family.obligations.len(), "{ids:?}");
}

#[test]
fn bounds_written_out_are_authored_atoms_not_a_template() {
    // `f_none` states `X >= 0 && X < 16` itself, the bounds of the 4-bit
    // templates of `f_hi` and `f_lo`: each comparison is authored (its range
    // strictly contains its operands'), so it is a Boolean atom whose flips
    // are obligations, not a template the bit abstraction absorbs.
    let terms = Terms::default();
    let arguments = || vec![terms.var("X", INT), terms.var("F", BOOL)];
    let templated = |name: &str, start: u32, high: i128| {
        let mut conjuncts = terms.template(start, "X", 4, &[(3, 1, high)]);
        conjuncts.push(terms.var("F", BOOL));
        equation(
            &terms,
            name,
            "Wide",
            arguments(),
            Some(terms.all(conjuncts)),
        )
    };
    let written = terms.all(vec![
        terms.builtin(IntGreaterEqual, vec![terms.var("X", INT), terms.int(0)]),
        terms.builtin(IntLess, vec![terms.var("X", INT), terms.int(16)]),
        terms.not(terms.var("F", BOOL)),
    ]);
    let rules = vec![
        templated("f_hi", 900, 1),
        templated("f_lo", 950, 0),
        equation(&terms, "f_none", "Wide", arguments(), Some(written)),
    ];
    let modules = [module_of(
        &terms,
        vec![function_of(&terms, "Wide", &[INT, BOOL])],
        rules,
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(
        family.not_generated.is_empty(),
        "{:#?}",
        family.not_generated
    );
    let bounds = family
        .atoms
        .iter()
        .enumerate()
        .filter(|(_, atom)| matches!(&atom.kind, AtomKind::Boolean { head } if head != "F"))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    assert_eq!(bounds.len(), 2, "{:#?}", family.atoms);
    for atom in bounds {
        assert_eq!(
            obligations_of(family, &head(family, atom)),
            vec![flip(&head(family, atom), &["f_none"])]
        );
    }
    assert_eq!(
        obligations_on(family, &AtomKind::Bit { column: 0, bit: 3 }),
        vec![names(&["f_hi", "f_lo"])]
    );
}

#[test]
fn the_pairs_the_equation_check_compares_are_unified() {
    // `Narrow` is ground: `n_eight`, `n_four` and `n_three` all apply at 3
    // (results agree, so the check admits them), and `n_ten` at 10 alone. `Pick` has a Bool argument, beyond the ground analysis,
    // so its pair is the coverage unifier's: `X` meets `true`.
    let terms = Terms::default();
    let below = |bound: i128| {
        Some(terms.all(vec![
            terms.builtin(IntGreaterEqual, vec![terms.var("X", INT), terms.int(0)]),
            terms.builtin(IntLess, vec![terms.var("X", INT), terms.int(bound)]),
        ]))
    };
    let true_ = SemanticTerm::token(terms.fresh(), BOOL, "true".to_owned()).unwrap();
    let rules = vec![
        equation(
            &terms,
            "n_eight",
            "Narrow",
            vec![terms.var("X", INT)],
            below(8),
        ),
        equation(
            &terms,
            "n_four",
            "Narrow",
            vec![terms.var("X", INT)],
            below(4),
        ),
        equation(&terms, "n_three", "Narrow", vec![terms.int(3)], None),
        equation(&terms, "n_ten", "Narrow", vec![terms.int(10)], None),
        equation(&terms, "p_any", "Pick", vec![terms.var("X", BOOL)], None),
        equation(&terms, "p_true", "Pick", vec![true_], None),
    ];
    let modules = [module_of(
        &terms,
        vec![
            function(&terms, "Narrow"),
            function_of(&terms, "Pick", &[BOOL]),
        ],
        rules,
    )];
    let (checked, missing) = equation_pairs_outside_unifications(&modules);
    assert!(missing.is_empty(), "{missing:#?}");
    assert_eq!(checked, 4);
}

#[test]
fn a_template_on_no_equation_argument_is_reported() {
    // Two transitions whose `Op` binders are cell content, not an argument
    // of an equation: the templates are no Boolean atoms and no bit atoms.
    let terms = Terms::default();
    let rule = |name: &str, value: i128| {
        let mut conjuncts = terms.template(800, "Op", 4, &[(3, 1, value)]);
        conjuncts.push(terms.apply("Ready", BOOL, vec![terms.var("H", BOOL)]));
        transition(&terms, name, &["H", "I", "P"], Some(terms.all(conjuncts)))
    };
    let modules = [module(&terms, &[], vec![rule("low", 0), rule("high", 1)])];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(
        family.atoms.iter().all(|atom| atom.kind
            == AtomKind::Boolean {
                head: "Ready".to_owned()
            }),
        "{:#?}",
        family.atoms
    );
    assert!(
        family
            .not_generated
            .iter()
            .any(|refused| refused.reason == NotGeneratedReason::BitDomain
                && refused.sentences == [0, 1]),
        "{:#?}",
        family.not_generated
    );
}

#[test]
fn bit_domain_and_evaluation_bound_are_their_own_reasons() {
    let terms = Terms::default();
    let wide = |name: &str, width: u32, value: i128| {
        let guard = Some(terms.all(terms.template(100, "Op", width, &[(0, 1, value)])));
        equation(&terms, name, "Wide", vec![terms.var("Op", INT)], guard)
    };
    let modules = [module(
        &terms,
        &["Wide"],
        vec![wide("wide_even", 17, 0), wide("wide_odd", 17, 1)],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(family.obligations.is_empty());
    assert_eq!(
        family
            .not_generated
            .iter()
            .map(|refused| refused.reason)
            .collect::<Vec<_>>(),
        [NotGeneratedReason::EvaluationBound]
    );

    let terms = Terms::default();
    let modules = [module(
        &terms,
        &["Mixed"],
        vec![
            {
                let guard = Some(terms.all(terms.template(100, "Op", 4, &[(0, 1, 0)])));
                equation(
                    &terms,
                    "mixed_4",
                    "Mixed",
                    vec![terms.var("Op", INT)],
                    guard,
                )
            },
            {
                let guard = Some(terms.all(terms.template(200, "Op", 8, &[(0, 1, 1)])));
                equation(
                    &terms,
                    "mixed_8",
                    "Mixed",
                    vec![terms.var("Op", INT)],
                    guard,
                )
            },
        ],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        family
            .not_generated
            .iter()
            .map(|refused| refused.reason)
            .collect::<Vec<_>>(),
        [NotGeneratedReason::BitDomain]
    );
}

#[test]
fn a_lone_guarded_sentence_flips_each_of_its_atoms() {
    // One guarded equation is a family of one: no pair to keep apart, so
    // each atom is one obligation on the sentence.
    let terms = Terms::default();
    let guard = terms.all(vec![
        terms.apply("Ready", BOOL, vec![terms.var("X", INT)]),
        terms.apply("Armed", BOOL, vec![terms.var("X", INT)]),
    ]);
    let modules = [module(
        &terms,
        &["Lone"],
        vec![equation(
            &terms,
            "lone",
            "Lone",
            vec![terms.var("X", INT)],
            Some(guard),
        )],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        obligations(family),
        vec![flip("Ready", &["lone"]), flip("Armed", &["lone"])]
    );
    assert!(family.obligations.iter().all(|flip| flip.whole));
}

#[test]
fn an_atom_an_inserted_node_also_states_is_reported() {
    // `InKeys(P)` is authored in `kept` and inserted in `looked_up`; under
    // the heads' unifier they are one atom, which no flip can edit whole.
    let terms = Terms::default();
    let binders = ["H", "I", "P"];
    let authored = terms.apply("InKeys", BOOL, vec![terms.var("P", BOOL)]);
    let inserted = Terms::apply_at(
        terms.inserted(InsertedNode::LookupGuard),
        "InKeys",
        BOOL,
        vec![terms.var("P", BOOL)],
    );
    let ready = || terms.apply("Ready", BOOL, vec![terms.var("H", BOOL)]);
    let rules = vec![
        transition(
            &terms,
            "kept",
            &binders,
            Some(terms.all(vec![authored, ready()])),
        ),
        transition(
            &terms,
            "looked_up",
            &binders,
            Some(terms.all(vec![inserted, terms.not(ready())])),
        ),
    ];
    let modules = [module(&terms, &[], rules)];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        obligations(family),
        vec![flip("Ready", &["kept", "looked_up"])]
    );
    assert_eq!(
        family
            .not_generated
            .iter()
            .map(|refused| (refused.reason, refused.sentences.clone()))
            .collect::<Vec<_>>(),
        [(NotGeneratedReason::Unflippable, vec![0, 1])]
    );
}

#[test]
fn an_atom_identity_conflict_keeps_the_bit_flips() {
    // `Q(X)` and `Q(Op)` render one construct but are different terms under
    // the heads' unifier: no Boolean flip, yet bit 3 still separates the
    // two equations and its flip is generated.
    let terms = Terms::default();
    let arm = |name: &str, start: u32, value: i128, subject: &str| {
        let mut conjuncts = terms.template(start, "Op", 4, &[(3, 1, value)]);
        conjuncts.push(Terms::apply_at(
            terms.at(900),
            "Q",
            BOOL,
            vec![terms.var(subject, INT)],
        ));
        let other = if value == 0 { "X" } else { "Y" };
        equation(
            &terms,
            name,
            "Pair",
            vec![terms.var("Op", INT), terms.var(other, INT)],
            Some(terms.all(conjuncts)),
        )
    };
    let modules = [module_of(
        &terms,
        vec![function_of(&terms, "Pair", &[INT, INT])],
        vec![arm("pair_low", 100, 0, "X"), arm("pair_high", 200, 1, "Op")],
    )];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(
        family
            .not_generated
            .iter()
            .any(|refused| refused.reason == NotGeneratedReason::AtomIdentity),
        "{:#?}",
        family.not_generated
    );
    assert_eq!(
        obligations(family),
        vec![bit_flip(3, &["pair_high", "pair_low"])]
    );
}

/// `k::matches!(N, Raise(binds..))` at the construct `start`, whose pattern
/// binds `binds`.
fn matches_raise(terms: &Terms, start: u32, binds: &[&str]) -> SemanticTerm {
    let arguments = binds.iter().map(|name| terms.var(name, BOOL)).collect();
    SemanticTerm::matches(
        terms.at(start),
        BOOL,
        terms.var("N", BOOL),
        terms.apply("Raise", BOOL, arguments),
        binds.iter().map(|name| sid(name)).collect(),
    )
}

#[test]
fn a_matches_test_that_binds_nothing_is_flipped() {
    // `k::matches!(n, Raise { .. })` and its negation keep the two rules
    // apart; its flip is a guard an author can write.
    let terms = Terms::default();
    let rules = vec![
        transition(
            &terms,
            "tag_raise",
            &["N"],
            Some(matches_raise(&terms, 700, &[])),
        ),
        transition(
            &terms,
            "tag_other",
            &["N"],
            Some(terms.not(matches_raise(&terms, 800, &[]))),
        ),
    ];
    let modules = [module(&terms, &[], rules)];
    let families = guard_families(&modules);
    let family = only(&families);
    assert_eq!(
        obligations(family),
        vec![flip("matches", &["tag_other", "tag_raise"])]
    );
    assert!(
        family.not_generated.is_empty(),
        "{:#?}",
        family.not_generated
    );
}

#[test]
fn a_matches_test_that_binds_a_local_is_reported() {
    // Negated, `k::matches!(n, Raise(y))` would leave `y` bound by nothing,
    // so the atom has no flip; the family still accounts for it.
    let terms = Terms::default();
    let rules = vec![
        transition(
            &terms,
            "tag_raise",
            &["N"],
            Some(matches_raise(&terms, 700, &["Y"])),
        ),
        transition(
            &terms,
            "tag_other",
            &["N"],
            Some(terms.not(matches_raise(&terms, 800, &["Y"]))),
        ),
    ];
    let modules = [module(&terms, &[], rules)];
    let families = guard_families(&modules);
    let family = only(&families);
    assert!(family.obligations.is_empty(), "{:#?}", family.obligations);
    assert_eq!(
        family
            .not_generated
            .iter()
            .map(|refused| (refused.reason, refused.sentences.clone()))
            .collect::<Vec<_>>(),
        [(NotGeneratedReason::Unflippable, vec![0, 1])]
    );
}
