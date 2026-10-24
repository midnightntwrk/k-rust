//! The collection memberships of the condition reader (`conditions.rs`, "collection
//! memberships"): unit tests of what a membership adds and of what stays unread, and a seeded
//! property test that compares `contradictory` with brute force over integer assignments, with
//! closed and open lists, sets, `MAP.values`, `MAP.keys` and `MAP.in_keys` of maps of 0 to 2
//! entries, and collections whose element sort differs from the item's (a map with `Int` values
//! listed in a `KItem` list, a list of `Int` read with a `KItem` item).

use std::sync::Arc;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{cases_contradictory, contradictory, contradictory_without_cases, memberships};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
    term::Term,
};

const DEFINITION: &str = r#"
[] module MAIN
    sort SortK{} []
    sort SortKItem{} []
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    sort SortTree{} []
    symbol dotTree{}() : SortTree{} [constructor{}(), functional{}(), injective{}()]
    symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
    symbol dotk{}() : SortK{} [constructor{}(), functional{}(), injective{}()]
    symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortInt{}, SortKItem{}}(F:SortInt{}))) [subsort{SortInt{}, SortKItem{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortBool{}, SortKItem{}}(F:SortBool{}))) [subsort{SortBool{}, SortKItem{}}()]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortTree{}, SortKItem{}}(F:SortTree{}))) [subsort{SortTree{}, SortKItem{}}()]
    hooked-symbol notBool{}(SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.not")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq")]
    hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ne")]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.tdiv")]
    hooked-symbol neK{}(SortK{}, SortK{}) : SortBool{} [function{}(), total{}(), hook{}("KEQUAL.ne")]
    hooked-sort SortList{} [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
    hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol listItem{}(SortKItem{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
    hooked-sort SortIntList{} [hook{}("LIST.List"), unit{}(intListUnit{}()), element{}(intListItem{}()), concat{}(intListConcat{}())]
    hooked-symbol intListUnit{}() : SortIntList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol intListItem{}(SortInt{}) : SortIntList{} [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol intListConcat{}(SortIntList{}, SortIntList{}) : SortIntList{} [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
    hooked-sort SortSet{} [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
    hooked-symbol setUnit{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
    hooked-symbol setItem{}(SortKItem{}) : SortSet{} [function{}(), total{}(), hook{}("SET.element")]
    hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{} [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
    hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-sort SortKMap{} [hook{}("MAP.Map"), unit{}(kmapUnit{}()), element{}(kmapItem{}()), concat{}(kmapConcat{}())]
    hooked-symbol kmapUnit{}() : SortKMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol kmapItem{}(SortKItem{}, SortKItem{}) : SortKMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol kmapConcat{}(SortKMap{}, SortKMap{}) : SortKMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol inList{}(SortKItem{}, SortList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
    hooked-symbol inListInt{}(SortInt{}, SortList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
    hooked-symbol inIntList{}(SortInt{}, SortIntList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
    hooked-symbol inIntListK{}(SortKItem{}, SortIntList{}) : SortBool{} [function{}(), total{}(), hook{}("LIST.in")]
    hooked-symbol inSet{}(SortKItem{}, SortSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
    hooked-symbol inSetInt{}(SortInt{}, SortSet{}) : SortBool{} [function{}(), total{}(), hook{}("SET.in")]
    hooked-symbol inKeys{}(SortInt{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
    hooked-symbol values{}(SortMap{}) : SortList{} [function{}(), hook{}("MAP.values")]
    hooked-symbol valuesInt{}(SortMap{}) : SortIntList{} [function{}(), hook{}("MAP.values")]
    hooked-symbol keys{}(SortMap{}) : SortSet{} [function{}(), total{}(), hook{}("MAP.keys")]
    hooked-symbol kvalues{}(SortKMap{}) : SortList{} [function{}(), hook{}("MAP.values")]
endmodule []
"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .unwrap_or_else(|error| panic!("{source} internalizes: {error:?}"))
}

/// `\equals(text, value)` for a Boolean `value`.
fn required(definition: &BackendDefinition, text: &str, value: bool) -> Predicate {
    Predicate::Equals(
        term(definition, text),
        term(definition, &format!(r#"\dv{{SortBool{{}}}}("{value}")"#)),
    )
}

fn not(predicate: Predicate) -> Predicate {
    Predicate::Not(Arc::new(predicate))
}

const TREE: &str = "inj{SortTree{}, SortKItem{}}(dotTree{}())";
const T: &str = "inj{SortTree{}, SortKItem{}}(T:SortTree{})";

/// `T =/=K .Tree`, KEVM serialization.md:591's condition, as the simplifier leaves it:
/// `\not(\equals(T, .Tree))`.
fn tree_is_not_empty(definition: &BackendDefinition) -> Predicate {
    not(Predicate::Equals(
        term(definition, "T:SortTree{}"),
        term(definition, "dotTree{}()"),
    ))
}

/// The conjuncts the simplifier leaves of the conjunction of `predicates`, as the check reads
/// them (`Context::conditions`).
fn simplified(definition: &BackendDefinition, predicates: Vec<Predicate>) -> Vec<Predicate> {
    let simplified = simplify_predicate_with_solver(
        definition,
        &Predicate::And(predicates.into()),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop")
    .expect("the conjunction simplifies");
    let mut conjuncts = std::collections::BTreeSet::new();
    crate::confluence::flatten(simplified, &mut conjuncts);
    conjuncts.into_iter().collect()
}

/// KEVM serialization.md:591/592: at `M = K |-> T`, `.MerkleTree in values(M)` lists the one
/// value `T`, so it states `T = .MerkleTree`, against 591's `T =/=K .MerkleTree`.
#[test]
fn membership_in_a_one_entry_values_list_is_an_equality() {
    let d = &definition();
    let member = required(
        d,
        &format!("inList{{}}({TREE}, kvalues{{}}(kmapItem{{}}(K:SortKItem{{}}, {T})))"),
        true,
    );
    // The two conditions as written, simplified as the check simplifies them.
    let written = required(
        d,
        &format!("neK{{}}(kseq{{}}({T}, dotk{{}}()), kseq{{}}({TREE}, dotk{{}}()))"),
        true,
    );
    let conjuncts = simplified(d, vec![member.clone(), written]);
    assert!(!conjuncts.contains(&Predicate::False), "{conjuncts:?}");
    assert!(contradictory(d, &conjuncts));
    assert!(contradictory(d, &[member.clone(), tree_is_not_empty(d)]));
    assert!(!contradictory(d, std::slice::from_ref(&member)));
    // `notBool` is read through, and the list may be written out.
    let negated = required(
        d,
        &format!("notBool{{}}(inList{{}}({TREE}, listItem{{}}({T})))"),
        false,
    );
    assert!(contradictory(d, &[negated, tree_is_not_empty(d)]));
    // Required false, the one member must differ: `T` beside `T = .Tree`.
    let absent = required(
        d,
        &format!("inList{{}}({TREE}, kvalues{{}}(kmapItem{{}}(K:SortKItem{{}}, {T})))"),
        false,
    );
    let same = Predicate::Equals(term(d, "T:SortTree{}"), term(d, "dotTree{}()"));
    assert!(contradictory(d, &[absent, same]));
}

/// A list with a middle, a map with a rest, and a `\not` of a membership are not read: the middle
/// or the rest may hold the item, and the `\not` also holds where the map is undefined.
#[test]
fn open_collections_and_negated_memberships_stay_unread() {
    let d = &definition();
    let open_list = required(
        d,
        &format!("inList{{}}({TREE}, listConcat{{}}(listItem{{}}({T}), M:SortList{{}}))"),
        true,
    );
    assert!(!contradictory(d, &[open_list, tree_is_not_empty(d)]));
    let map_with_rest = required(
        d,
        &format!(
            "inList{{}}({TREE}, kvalues{{}}(kmapConcat{{}}(kmapItem{{}}(K:SortKItem{{}}, {T}), R:SortKMap{{}})))"
        ),
        true,
    );
    assert!(!contradictory(d, &[map_with_rest, tree_is_not_empty(d)]));
    // Satisfiable where `K1 = K2`: the map is undefined, so the membership is not `true`.
    let negated = not(required(
        d,
        &format!(
            "inList{{}}({TREE}, kvalues{{}}(kmapConcat{{}}(kmapItem{{}}(K1:SortKItem{{}}, {T}), kmapItem{{}}(K2:SortKItem{{}}, {TREE}))))"
        ),
        true,
    ));
    assert!(!contradictory(d, std::slice::from_ref(&negated)));
}

/// Required true in a collection without members refutes; required false adds nothing.
#[test]
fn a_membership_in_no_members_is_refuted_only_when_required_true() {
    let d = &definition();
    assert!(contradictory(
        d,
        &[required(
            d,
            "inIntList{}(X:SortInt{}, intListUnit{}())",
            true
        )]
    ));
    assert!(!contradictory(
        d,
        &[required(
            d,
            "inIntList{}(X:SortInt{}, intListUnit{}())",
            false
        )]
    ));
    assert!(contradictory(
        d,
        &[required(d, "inKeys{}(X:SortInt{}, mapUnit{}())", true)]
    ));
}

/// Members are converted as `MAP.values` converts them (`Int` values listed in a `KItem` list),
/// and the item is read as `LIST.in` reads it (an `Int` item of a `KItem` list is its injection,
/// a `KItem` injection of an `Int` read in an `Int` list is its operand); an item of a wider sort
/// that is no injection of an element adds nothing.
#[test]
fn members_and_items_are_read_at_the_hooks_sorts() {
    let d = &definition();
    let apart = required(d, "neInt{}(X:SortInt{}, Y:SortInt{})", true);
    let converted = required(
        d,
        "inListInt{}(X:SortInt{}, values{}(mapItem{}(\\dv{SortInt{}}(\"1\"), Y:SortInt{})))",
        true,
    );
    assert!(contradictory(d, &[converted, apart.clone()]));
    let same_sort = required(
        d,
        "inIntList{}(X:SortInt{}, valuesInt{}(mapItem{}(\\dv{SortInt{}}(\"1\"), Y:SortInt{})))",
        true,
    );
    assert!(contradictory(d, &[same_sort, apart.clone()]));
    let wide_injection = required(
        d,
        "inIntListK{}(inj{SortInt{}, SortKItem{}}(X:SortInt{}), intListItem{}(Y:SortInt{}))",
        true,
    );
    assert!(contradictory(d, &[wide_injection, apart]));
    let wider = required(d, "inIntListK{}(I:SortKItem{}, intListUnit{}())", true);
    assert!(!contradictory(d, std::slice::from_ref(&wider)));
}

/// Sets, `MAP.keys` and `MAP.in_keys` of collections without rest, by the same rule.
#[test]
fn set_and_key_memberships_are_read_by_the_same_rule() {
    let d = &definition();
    let one = r#"\dv{SortInt{}}("1")"#;
    let two = r#"\dv{SortInt{}}("2")"#;
    let not_one = required(d, &format!("neInt{{}}(X:SortInt{{}}, {one})"), true);
    let not_two = required(d, &format!("neInt{{}}(X:SortInt{{}}, {two})"), true);
    let in_keys = required(
        d,
        &format!("inKeys{{}}(X:SortInt{{}}, mapItem{{}}({one}, Y:SortInt{{}}))"),
        true,
    );
    assert!(contradictory(d, &[in_keys, not_one.clone()]));
    let in_key_set = required(
        d,
        &format!(
            "inSetInt{{}}(X:SortInt{{}}, keys{{}}(mapConcat{{}}(mapItem{{}}({one}, Y:SortInt{{}}), mapItem{{}}({two}, Z:SortInt{{}}))))"
        ),
        true,
    );
    assert!(contradictory(
        d,
        &[in_key_set.clone(), not_one.clone(), not_two.clone()]
    ));
    assert!(!contradictory(d, &[in_key_set, not_one.clone()]));
    let in_set = required(
        d,
        &format!(
            "inSet{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(X:SortInt{{}}), setItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({one})))"
        ),
        true,
    );
    assert!(contradictory(d, &[in_set, not_one]));
}

/// Two binary disjunctions refuted by cases (4 cases) beside a membership of five members: the
/// expanded conjunction has 20 cases, past the budget of 16, so only the conjunction as it is
/// refutes, and it still does.
#[test]
fn a_membership_disjunction_keeps_a_refutation_by_cases() {
    let d = &definition();
    let int = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
    let is = |variable: &str, value: i64| {
        required(
            d,
            &format!("eqInt{{}}({variable}:SortInt{{}}, {})", int(value)),
            true,
        )
    };
    let isnt = |variable: &str, value: i64| {
        required(
            d,
            &format!("neInt{{}}({variable}:SortInt{{}}, {})", int(value)),
            true,
        )
    };
    let list = (1..=5).fold("intListUnit{}()".to_owned(), |list, value| {
        format!("intListConcat{{}}(intListItem{{}}({}), {list})", int(value))
    });
    let conjuncts = vec![
        Predicate::Or(vec![is("X", 0), is("X", 1)].into()),
        Predicate::Or(vec![is("Y", 0), is("Y", 1)].into()),
        isnt("X", 0),
        isnt("X", 1),
        required(d, &format!("inIntList{{}}(Z:SortInt{{}}, {list})"), true),
    ];
    assert!(contradictory(d, &conjuncts));
    let table = memberships(d);
    let super::Expansion::Added(expanded) = super::collection_memberships(d, &conjuncts) else {
        panic!("the membership adds a disjunction");
    };
    assert!(!contradictory_without_cases(d, &table, &expanded));
    assert!(!cases_contradictory(d, &table, &expanded));
}

// The property test.

const NAMES: [&str; 3] = ["X", "Y", "Z"];

/// An integer operand: a variable, a literal, or the partial quotient `X /Int Y`.
#[derive(Clone, Copy, Debug)]
enum Operand {
    Variable(usize),
    Literal(i64),
    Quotient,
}

impl Operand {
    fn kore(self) -> String {
        match self {
            Self::Variable(index) => format!("{}:SortInt{{}}", NAMES[index]),
            Self::Literal(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
            Self::Quotient => "divInt{}(X:SortInt{}, Y:SortInt{})".to_owned(),
        }
    }

    fn item(self) -> String {
        format!("inj{{SortInt{{}}, SortKItem{{}}}}({})", self.kore())
    }

    fn value(self, assignment: [i64; 3]) -> Option<i64> {
        match self {
            Self::Variable(index) => Some(assignment[index]),
            Self::Literal(value) => Some(value),
            Self::Quotient => (assignment[1] != 0).then(|| assignment[0] / assignment[1]),
        }
    }
}

/// How a membership is written: the hook's symbol, the collection, and how its members are held.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// `inList(inj(e), list of inj(x))`.
    List,
    /// `inListInt(e, list of inj(x))`: an `Int` item of a `KItem` list.
    ListOfIntItem,
    /// `inIntList(e, list of x)`.
    IntList,
    /// `inIntListK(inj(e), list of x)`: a `KItem` item of an `Int` list.
    IntListOfKItem,
    /// `inList(inj(e), values(map))`: `Int` values listed in a `KItem` list.
    Values,
    /// `inIntList(e, valuesInt(map))`.
    IntValues,
    /// `inSet(inj(e), set of inj(x))`.
    Set,
    /// `inSetInt(e, keys(map))`: `Int` keys in a `KItem` set.
    Keys,
    /// `inKeys(e, map)`.
    InKeys,
}

const KINDS: [Kind; 9] = [
    Kind::List,
    Kind::ListOfIntItem,
    Kind::IntList,
    Kind::IntListOfKItem,
    Kind::Values,
    Kind::IntValues,
    Kind::Set,
    Kind::Keys,
    Kind::InKeys,
];

impl Kind {
    const fn is_map(self) -> bool {
        matches!(
            self,
            Self::Values | Self::IntValues | Self::Keys | Self::InKeys
        )
    }

    const fn is_set(self) -> bool {
        matches!(self, Self::Set)
    }
}

/// A membership `e in c`: `items` are the list's or set's elements, or the map's entries; `open`
/// gives the collection a middle (lists) or a rest (sets, maps), a variable of its own.
#[derive(Clone, Debug)]
struct Membership {
    kind: Kind,
    item: Operand,
    elements: Vec<Operand>,
    entries: Vec<(Operand, Operand)>,
    open: Option<usize>,
}

impl Membership {
    fn kore(&self) -> String {
        let concat = |unit: &str, concat: &str, parts: Vec<String>| {
            parts
                .into_iter()
                .rev()
                .reduce(|rest, part| format!("{concat}{{}}({part}, {rest})"))
                .unwrap_or_else(|| format!("{unit}{{}}()"))
        };
        let rest = |sort: &str| self.open.map(|index| format!("R{index}:{sort}{{}}"));
        let map = || {
            let mut parts = self
                .entries
                .iter()
                .map(|(key, value)| format!("mapItem{{}}({}, {})", key.kore(), value.kore()))
                .collect::<Vec<_>>();
            parts.extend(rest("SortMap"));
            concat("mapUnit", "mapConcat", parts)
        };
        let list =
            |item: &dyn Fn(Operand) -> String, element: &str, unit: &str, cat: &str, sort| {
                let mut parts = self
                    .elements
                    .iter()
                    .map(|x| format!("{element}{{}}({})", item(*x)))
                    .collect::<Vec<_>>();
                if let Some(middle) = rest(sort) {
                    // The middle sits after the first element, so that an open list has tails too.
                    parts.insert(parts.len().min(1), middle);
                }
                concat(unit, cat, parts)
            };
        let kitems = || {
            list(
                &Operand::item,
                "listItem",
                "listUnit",
                "listConcat",
                "SortList",
            )
        };
        let ints = || {
            list(
                &Operand::kore,
                "intListItem",
                "intListUnit",
                "intListConcat",
                "SortIntList",
            )
        };
        let e = self.item;
        match self.kind {
            Kind::List => format!("inList{{}}({}, {})", e.item(), kitems()),
            Kind::ListOfIntItem => format!("inListInt{{}}({}, {})", e.kore(), kitems()),
            Kind::IntList => format!("inIntList{{}}({}, {})", e.kore(), ints()),
            Kind::IntListOfKItem => format!("inIntListK{{}}({}, {})", e.item(), ints()),
            Kind::Values => format!("inList{{}}({}, values{{}}({}))", e.item(), map()),
            Kind::IntValues => format!("inIntList{{}}({}, valuesInt{{}}({}))", e.kore(), map()),
            Kind::Set => {
                let mut parts = self
                    .elements
                    .iter()
                    .map(|x| format!("setItem{{}}({})", x.item()))
                    .collect::<Vec<_>>();
                parts.extend(rest("SortSet"));
                format!(
                    "inSet{{}}({}, {})",
                    e.item(),
                    concat("setUnit", "setConcat", parts)
                )
            }
            Kind::Keys => format!("inSetInt{{}}({}, keys{{}}({}))", e.kore(), map()),
            Kind::InKeys => format!("inKeys{{}}({}, {})", e.kore(), map()),
        }
    }

    /// The Boolean values the membership can have at `assignment`, for some value of its own
    /// middle or rest: `(can be true, can be false, can be undefined)`.
    fn values(&self, assignment: [i64; 3]) -> (bool, bool, bool) {
        let value = |operand: Operand| operand.value(assignment);
        let Some(item) = value(self.item) else {
            return (false, false, true);
        };
        let members = if self.kind.is_map() {
            let Some(keys) = self
                .entries
                .iter()
                .map(|(key, _)| value(*key))
                .collect::<Option<Vec<_>>>()
            else {
                return (false, false, true);
            };
            let Some(values) = self
                .entries
                .iter()
                .map(|(_, bound)| value(*bound))
                .collect::<Option<Vec<_>>>()
            else {
                return (false, false, true);
            };
            if (0..keys.len()).any(|i| keys[i + 1..].contains(&keys[i])) {
                return (false, false, true);
            }
            if matches!(self.kind, Kind::Values | Kind::IntValues) {
                values
            } else {
                keys
            }
        } else {
            let Some(elements) = self
                .elements
                .iter()
                .map(|x| value(*x))
                .collect::<Option<Vec<_>>>()
            else {
                return (false, false, true);
            };
            if self.kind.is_set()
                && (0..elements.len()).any(|i| elements[i + 1..].contains(&elements[i]))
            {
                return (false, false, true);
            }
            elements
        };
        let known = members.contains(&item);
        if self.open.is_none() {
            return (known, !known, false);
        }
        // A middle can hold anything; a rest can hold a binding (an element) for the item, and
        // can repeat a key (an element) the term states, which makes it undefined.
        let can_repeat = (self.kind.is_map() && !self.entries.is_empty())
            || (self.kind.is_set() && !self.elements.is_empty());
        (true, !known, can_repeat)
    }
}

/// A conjunct of the generated conjunctions.
#[derive(Clone, Debug)]
enum Conjunct {
    /// The membership under `negations` `notBool`s, required `polarity`.
    Member {
        membership: Membership,
        negations: usize,
        polarity: bool,
    },
    /// `\not(\equals(membership, true))`, which also holds where it is undefined.
    NotMember(Membership),
    /// `eqInt(left, right)` (or `neInt`) required `polarity`.
    Compare {
        equal: bool,
        left: Operand,
        right: Operand,
        polarity: bool,
    },
    /// `\equals(X, operand)`.
    Equality(usize, Operand),
    /// `\or` of two conjuncts.
    Either(Box<Conjunct>, Box<Conjunct>),
}

impl Conjunct {
    fn predicate(&self, definition: &BackendDefinition) -> Predicate {
        match self {
            Self::Member {
                membership,
                negations,
                polarity,
            } => {
                let mut text = membership.kore();
                for _ in 0..*negations {
                    text = format!("notBool{{}}({text})");
                }
                required(definition, &text, *polarity)
            }
            Self::NotMember(membership) => not(required(definition, &membership.kore(), true)),
            Self::Compare {
                equal,
                left,
                right,
                polarity,
            } => {
                let operator = if *equal { "eqInt" } else { "neInt" };
                required(
                    definition,
                    &format!("{operator}{{}}({}, {})", left.kore(), right.kore()),
                    *polarity,
                )
            }
            Self::Equality(variable, operand) => Predicate::Equals(
                term(definition, &Operand::Variable(*variable).kore()),
                term(definition, &operand.kore()),
            ),
            Self::Either(left, right) => {
                Predicate::Or(vec![left.predicate(definition), right.predicate(definition)].into())
            }
        }
    }

    fn satisfied(&self, assignment: [i64; 3]) -> bool {
        match self {
            Self::Member {
                membership,
                negations,
                polarity,
            } => {
                let (can_be_true, can_be_false, _) = membership.values(assignment);
                if *polarity != (negations % 2 == 1) {
                    can_be_true
                } else {
                    can_be_false
                }
            }
            Self::NotMember(membership) => {
                let (_, can_be_false, can_be_undefined) = membership.values(assignment);
                can_be_false || can_be_undefined
            }
            Self::Compare {
                equal,
                left,
                right,
                polarity,
            } => match (left.value(assignment), right.value(assignment)) {
                (Some(left), Some(right)) => ((left == right) == *equal) == *polarity,
                _ => false,
            },
            Self::Equality(variable, operand) => {
                operand.value(assignment) == Some(assignment[*variable])
            }
            Self::Either(left, right) => left.satisfied(assignment) || right.satisfied(assignment),
        }
    }
}

/// The assignments brute force tries: `[-2, 2]^3`. The literals are `-1` to `1`, so a
/// conjunction of equalities and memberships satisfiable over the integers has a witness here
/// (each variable equal to a literal or to one of two further values); the quotient's values
/// are what they are at these points.
fn assignments() -> impl Iterator<Item = [i64; 3]> {
    (-2..=2).flat_map(|x| (-2..=2).flat_map(move |y| (-2..=2).map(move |z| [x, y, z])))
}

/// Random conjunctions of two to four conjuncts, at least one a membership, against brute
/// force: `contradictory` only when no assignment satisfies the conjunction (each membership's
/// middle or rest chosen for it, since none is shared). Returns the failures.
pub(crate) fn random_memberships_agree_with_brute_force(cases: usize) -> Vec<String> {
    let definition = definition();
    let mut state = 0xc011_ec71_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let mut failures = Vec::new();
    for _ in 0..cases {
        let mut rests = 0;
        let operand = |next: &mut dyn FnMut(usize) -> usize| match next(6) {
            0 | 1 => Operand::Literal(i64::try_from(next(3)).unwrap() - 1),
            _ => Operand::Variable(next(3)),
        };
        // A member may also be the partial quotient.
        let member = |next: &mut dyn FnMut(usize) -> usize| {
            if next(8) == 0 {
                Operand::Quotient
            } else {
                operand(next)
            }
        };
        let mut membership = |next: &mut dyn FnMut(usize) -> usize| {
            let kind = KINDS[next(KINDS.len())];
            let (elements, entries) = if kind.is_map() {
                let count = next(3);
                (
                    Vec::new(),
                    (0..count).map(|_| (member(next), member(next))).collect(),
                )
            } else {
                let count = next(4);
                ((0..count).map(|_| member(next)).collect(), Vec::new())
            };
            let open = (next(4) == 0).then(|| {
                rests += 1;
                rests
            });
            Membership {
                kind,
                item: operand(next),
                elements,
                entries,
                open,
            }
        };
        let mut conjunct = |next: &mut dyn FnMut(usize) -> usize, first: bool| match if first {
            0
        } else {
            next(8)
        } {
            0..=2 => Conjunct::Member {
                membership: membership(next),
                negations: usize::from(next(4) == 0),
                polarity: next(2) == 0,
            },
            3 => Conjunct::NotMember(membership(next)),
            4 => Conjunct::Equality(next(3), operand(next)),
            5 => Conjunct::Either(
                Box::new(Conjunct::Compare {
                    equal: true,
                    left: Operand::Variable(next(3)),
                    right: operand(next),
                    polarity: true,
                }),
                Box::new(Conjunct::Compare {
                    equal: true,
                    left: Operand::Variable(next(3)),
                    right: operand(next),
                    polarity: true,
                }),
            ),
            _ => Conjunct::Compare {
                equal: next(2) == 0,
                left: operand(next),
                right: operand(next),
                polarity: next(2) == 0,
            },
        };
        let count = 2 + next(3);
        let conjuncts = (0..count)
            .map(|index| conjunct(&mut next, index == 0))
            .collect::<Vec<_>>();
        let predicates = conjuncts
            .iter()
            .map(|conjunct| conjunct.predicate(&definition))
            .collect::<Vec<_>>();
        if contradictory(&definition, &predicates)
            && let Some(witness) = assignments().find(|assignment| {
                conjuncts
                    .iter()
                    .all(|conjunct| conjunct.satisfied(*assignment))
            })
        {
            failures.push(format!(
                "{conjuncts:?} is called contradictory but {witness:?} satisfies it"
            ));
        }
    }
    failures
}

#[test]
fn random_memberships_agree_with_brute_force_by_default() {
    let failures = random_memberships_agree_with_brute_force(4_000);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Reading a list with a middle or a map with a rest as its known members refutes `E in
/// values(K |-> V R)` beside `E =/=Int V`, which holds where `R` binds `E`; the property test
/// sees it.
#[test]
fn reading_open_collections_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        collection_membership_reads_open: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_memberships_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}
