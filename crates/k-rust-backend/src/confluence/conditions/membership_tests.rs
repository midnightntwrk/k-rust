//! The membership literals of the condition reader (`conditions.rs`, "membership literals")
//! against the predicates' own equations: unit tests of the recognizer and of the decision, and
//! the `membership` oracle, a seeded property test over small definitions built through the
//! loader. The oracle never computes membership from the sort order: each refuted conjunction is
//! evaluated by the backend's simplifier, from the predicates' equations with the priority
//! reading, at every assignment of witnesses to its items, and must hold at none.

use std::sync::Arc;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{contradictory, memberships};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
    term::Term,
};

/// The signature every definition of these tests shares: `K`, `KItem`, `Bool` below `KItem`,
/// the sequence constructors, injections and the Boolean and `K` equality hooks.
const PRELUDE: &str = r#"
    sort SortK{} []
    sort SortKItem{} []
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), functional{}(), injective{}()]
    symbol dotk{}() : SortK{} [constructor{}(), functional{}(), injective{}()]
    symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
    hooked-symbol notBool{}(SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.not")]
    hooked-symbol andBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.and")]
    hooked-symbol andThenBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.andThen")]
    hooked-symbol orBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.or")]
    hooked-symbol eqBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.eq")]
    hooked-symbol neBool{}(SortBool{}, SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.ne")]
    hooked-symbol eqK{}(SortK{}, SortK{}) : SortBool{} [function{}(), total{}(), hook{}("KEQUAL.eq")]
    hooked-symbol neK{}(SortK{}, SortK{}) : SortBool{} [function{}(), total{}(), hook{}("KEQUAL.ne")]
    axiom{R} \exists{R}(V:SortKItem{}, \equals{SortKItem{}, R}(V:SortKItem{}, inj{SortBool{}, SortKItem{}}(F:SortBool{}))) [subsort{SortBool{}, SortKItem{}}()]
"#;

fn sort(name: &str) -> String {
    format!("Sort{name}{{}}")
}

/// `axiom sub < sup`.
fn subsort(sub: &str, sup: &str) -> String {
    format!(
        r"axiom{{R}} \exists{{R}}(V:{sup}, \equals{{{sup}, R}}(V:{sup}, inj{{{sub}, {sup}}}(F:{sub}))) [subsort{{{sub}, {sup}}}()]",
        sub = sort(sub),
        sup = sort(sup)
    )
}

/// The one-element sequence of `item`, of sort `S`, injected into `KItem`.
fn sequence(item: &str, sort_name: &str) -> String {
    format!(
        "kseq{{}}(inj{{{}, SortKItem{{}}}}({item}), dotk{{}}())",
        sort(sort_name)
    )
}

/// An equation `name(X0) = value` where `X0` matches `pattern` (whose variables are `binders`,
/// with their sorts), under `requires` (`None`: `\top`), with `attributes`; with `owise` the
/// antecedent also excludes `excluded`, the patterns (and their binders and requires) of the
/// equations above it.
fn equation(
    name: &str,
    pattern: &str,
    requires: Option<&str>,
    value: bool,
    attributes: &str,
) -> String {
    let requires = requires.map_or_else(|| r"\top{R}()".to_owned(), str::to_owned);
    format!(
        r#"axiom{{R}} \implies{{R}}(
    \and{{R}}({requires}, \and{{R}}(\in{{SortK{{}}, R}}(X0:SortK{{}}, {pattern}), \top{{R}}())),
    \equals{{SortBool{{}}, R}}({name}{{}}(X0:SortK{{}}), \and{{SortBool{{}}}}(\dv{{SortBool{{}}}}("{value}"), \top{{SortBool{{}}}}()))) [{attributes}]"#
    )
}

/// The `owise` equation `name(X0) = false` below equations whose antecedents are `excluded`
/// (each `\exists binders. requires /\ X0 in pattern`).
fn otherwise(name: &str, excluded: &[String]) -> String {
    let mut disjunction = r"\bottom{R}()".to_owned();
    for antecedent in excluded.iter().rev() {
        disjunction = format!(r"\or{{R}}({antecedent}, {disjunction})");
    }
    format!(
        r#"axiom{{R}} \implies{{R}}(
    \and{{R}}(\not{{R}}({disjunction}), \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortK{{}}, R}}(X0:SortK{{}}, K:SortK{{}}), \top{{R}}()))),
    \equals{{SortBool{{}}, R}}({name}{{}}(X0:SortK{{}}), \and{{SortBool{{}}}}(\dv{{SortBool{{}}}}("false"), \top{{SortBool{{}}}}()))) [owise{{}}()]"#
    )
}

/// `\exists binders. requires /\ X0 in pattern`.
fn antecedent(binders: &[String], requires: Option<&str>, pattern: &str) -> String {
    let requires = requires.map_or_else(|| r"\top{R}()".to_owned(), str::to_owned);
    let mut body = format!(
        r"\and{{R}}({requires}, \and{{R}}(\in{{SortK{{}}, R}}(X0:SortK{{}}, {pattern}), \top{{R}}()))"
    );
    for binder in binders.iter().rev() {
        body = format!(r"\exists{{R}}({binder}, {body})");
    }
    body
}

fn declare(name: &str) -> String {
    format!("symbol {name}{{}}(SortK{{}}) : SortBool{{}} [function{{}}(), total{{}}()]")
}

/// The membership predicate `name` of sort `S`, as K generates it.
fn membership(name: &str, sort_name: &str) -> String {
    let variable = format!("V:{}", sort(sort_name));
    let pattern = sequence(&variable, sort_name);
    format!(
        "{}\n{}\n{}",
        declare(name),
        equation(name, &pattern, None, true, ""),
        otherwise(name, &[antecedent(&[variable], None, &pattern)])
    )
}

/// The shapes of near-miss predicates: each differs from a membership predicate of `S` in one
/// respect the recognizer must refuse.
#[derive(Clone, Copy, Debug)]
enum NearMiss {
    /// A second `true` equation, for `other`, in the same group.
    ExtraTrue,
    /// The `true` equation requires `S` also of `other`'s predicate.
    ConditionalTrue,
    /// `false` in the higher group (unconditional), `true` in the lower.
    TrueBelow,
    /// The `true` equation is `concrete`.
    Concrete,
    /// The `true` equation matches any tail, not only `dotk`.
    Tail,
    /// The `true` equation matches one constructor of `S` (`c` + the sort's name).
    Constructor,
}

const NEAR_MISSES: [NearMiss; 6] = [
    NearMiss::ExtraTrue,
    NearMiss::ConditionalTrue,
    NearMiss::TrueBelow,
    NearMiss::Concrete,
    NearMiss::Tail,
    NearMiss::Constructor,
];

/// The near-miss predicate `name` of shape `miss` over `S`; `other` names the second sort and
/// `other_predicate` its membership predicate.
fn near_miss(
    name: &str,
    miss: NearMiss,
    sort_name: &str,
    other: &str,
    other_predicate: &str,
) -> String {
    let variable = format!("V:{}", sort(sort_name));
    let pattern = sequence(&variable, sort_name);
    let plain = antecedent(std::slice::from_ref(&variable), None, &pattern);
    let equations = match miss {
        NearMiss::ExtraTrue => {
            let other_variable = format!("W:{}", sort(other));
            let other_pattern = sequence(&other_variable, other);
            format!(
                "{}\n{}\n{}",
                equation(name, &pattern, None, true, ""),
                equation(name, &other_pattern, None, true, ""),
                otherwise(
                    name,
                    &[plain, antecedent(&[other_variable], None, &other_pattern)]
                )
            )
        }
        NearMiss::ConditionalTrue => {
            let requires = format!(
                r#"\equals{{SortBool{{}}, R}}({other_predicate}{{}}({pattern}), \dv{{SortBool{{}}}}("true"))"#
            );
            format!(
                "{}\n{}",
                equation(name, &pattern, Some(&requires), true, ""),
                otherwise(name, &[antecedent(&[variable], Some(&requires), &pattern)])
            )
        }
        NearMiss::TrueBelow => format!(
            "{}\n{}",
            equation(name, "K:SortK{}", None, false, r#"priority{}("40")"#),
            equation(name, &pattern, None, true, r#"priority{}("60")"#)
        ),
        NearMiss::Concrete => format!(
            "{}\n{}",
            equation(name, &pattern, None, true, "concrete{}()"),
            otherwise(name, &[plain])
        ),
        NearMiss::Tail => {
            let tail_pattern = format!(
                "kseq{{}}(inj{{{}, SortKItem{{}}}}({variable}), T:SortK{{}})",
                sort(sort_name)
            );
            format!(
                "{}\n{}",
                equation(name, &tail_pattern, None, true, ""),
                otherwise(
                    name,
                    &[antecedent(
                        &[variable, "T:SortK{}".to_owned()],
                        None,
                        &tail_pattern
                    )]
                )
            )
        }
        NearMiss::Constructor => {
            let constructed = sequence(&format!("c{sort_name}{{}}()"), sort_name);
            format!(
                "{}\n{}",
                equation(name, &constructed, None, true, ""),
                otherwise(name, &[antecedent(&[], None, &constructed)])
            )
        }
    };
    format!("{}\n{equations}", declare(name))
}

fn load(body: &str) -> BackendDefinition {
    let source = format!("[] module MAIN {PRELUDE} {body} endmodule []");
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

fn dv(value: bool) -> String {
    format!(r#"\dv{{SortBool{{}}}}("{value}")"#)
}

/// Sorts `C < A`, `C < B` (C has no constructor), `D` (no subsort shared with `A` or `B`) and
/// `T` above all four; the membership predicates `isA`, `isB`, `isC`, `isD`, `isT`; and a partial
/// function `pf : T -> T` with no equation.
fn fixed(extra: &str) -> BackendDefinition {
    let mut body = String::new();
    for name in ["A", "B", "C", "D", "T"] {
        body.push_str(&format!("sort {} []\n", sort(name)));
        body.push_str(&subsort(name, "KItem"));
        body.push('\n');
        body.push_str(&membership(&format!("is{name}"), name));
        body.push('\n');
    }
    for (sub, sup) in [
        ("C", "A"),
        ("C", "B"),
        ("A", "T"),
        ("B", "T"),
        ("C", "T"),
        ("D", "T"),
    ] {
        body.push_str(&subsort(sub, sup));
        body.push('\n');
    }
    for name in ["A", "B", "D", "T"] {
        body.push_str(&format!(
            "symbol c{name}{{}}() : {} [constructor{{}}(), functional{{}}(), injective{{}}()]\n",
            sort(name)
        ));
    }
    body.push_str("symbol pf{}(SortT{}) : SortT{} [function{}()]\n");
    body.push_str(extra);
    load(&body)
}

/// `\equals(p(kseq(inj{T, KItem}(item), dotk)), value)`.
fn literal(definition: &BackendDefinition, predicate: &str, item: &str, value: bool) -> Predicate {
    Predicate::Equals(
        term(
            definition,
            &format!("{predicate}{{}}({})", sequence(item, "T")),
        ),
        term(definition, &dv(value)),
    )
}

#[test]
fn membership_predicates_are_recognized_from_their_equations() {
    let definition = fixed("");
    let table = memberships(&definition);
    let mut recognized = table
        .iter()
        .map(|(name, sort)| format!("{name}:{sort:?}"))
        .collect::<Vec<_>>();
    recognized.sort();
    assert_eq!(recognized.len(), 5, "{recognized:?}");
    for name in ["A", "B", "C", "D", "T"] {
        assert!(
            table.contains_key(&crate::term::Name::from(format!("is{name}"))),
            "is{name}: {recognized:?}"
        );
    }
}

/// N1: the recognizer refuses each near miss, a hooked predicate, and every predicate of a
/// definition with an equation at the bare-variable index.
#[test]
fn the_recognizer_refuses_near_misses() {
    for miss in NEAR_MISSES {
        let definition = fixed(&near_miss("nm", miss, "A", "B", "isB"));
        let table = memberships(&definition);
        assert!(
            !table.contains_key(&crate::term::Name::from("nm")),
            "{miss:?} is recognized"
        );
        assert_eq!(table.len(), 5, "{miss:?}");
    }
    // The same equations at a hooked symbol.
    let variable = "V:SortA{}";
    let pattern = sequence(variable, "A");
    let hooked = format!(
        "hooked-symbol hk{{}}(SortK{{}}) : SortBool{{}} [function{{}}(), total{{}}(), hook{{}}(\"MEMBERSHIP.test\")]\n{}\n{}",
        equation("hk", &pattern, None, true, ""),
        otherwise("hk", &[antecedent(&[variable.to_owned()], None, &pattern)])
    );
    let definition = fixed(&hooked);
    assert!(!memberships(&definition).contains_key(&crate::term::Name::from("hk")));
    // A collection equation whose left-hand side normalizes to a bare variable is offered at
    // every index, also at each predicate's: no predicate is recognized.
    let bare = r#"
    sort SortElement{} [hasDomainValues{}()]
    hooked-sort SortList{}
        [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
    hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
    hooked-symbol listItem{}(SortElement{}) : SortList{} [function{}(), total{}(), hook{}("LIST.element")]
    hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), hook{}("LIST.concat"), assoc{}()]
    axiom{R} \implies{R}(
        \and{R}(\top{R}(), \and{R}(\in{SortList{}, R}(X0:SortList{}, L:SortList{}),
            \and{R}(\in{SortList{}, R}(X1:SortList{}, listUnit{}()), \top{R}()))),
        \equals{SortList{}, R}(listConcat{}(X0:SortList{}, X1:SortList{}),
            \and{SortList{}}(listUnit{}(), \top{SortList{}}()))) []
    "#;
    let definition = fixed(bare);
    assert!(
        definition
            .function_theory()
            .contains_key(&crate::rule::TermIndex::Variable),
        "the fixture has a bare-variable equation"
    );
    assert!(memberships(&definition).is_empty());
}

/// The decision: disjoint sorts are refuted, a common subsort with no constructor blocks the
/// refutation (no sort's emptiness is used), a sort required false above every common lower
/// bound refutes, one not above them does not.
#[test]
fn memberships_are_decided_by_the_sort_order() {
    let definition = fixed("");
    let x = "X:SortT{}";
    let refuted = |conjuncts: &[Predicate]| contradictory(&definition, conjuncts);
    // `A` and `D` share no subsort.
    assert!(refuted(&[
        literal(&definition, "isA", x, true),
        literal(&definition, "isD", x, true)
    ]));
    // `C`, below `A` and `B`, has no constructor; `isA(X) /\ isB(X)` is still satisfiable.
    assert!(!refuted(&[
        literal(&definition, "isA", x, true),
        literal(&definition, "isB", x, true)
    ]));
    // `C < A`: `isC(X)` beside `isA(X)` false.
    assert!(refuted(&[
        literal(&definition, "isC", x, true),
        literal(&definition, "isA", x, false)
    ]));
    // `isA(X) /\ isB(X)` puts `X` in `C`, below `T`: `isT(X)` false is refuted, `isD(X)` false
    // is not.
    assert!(refuted(&[
        literal(&definition, "isA", x, true),
        literal(&definition, "isB", x, true),
        literal(&definition, "isT", x, false)
    ]));
    assert!(!refuted(&[
        literal(&definition, "isA", x, true),
        literal(&definition, "isB", x, true),
        literal(&definition, "isD", x, false)
    ]));
    // `isA(cD)`: an item whose own sort shares no subsort with `A`.
    let item = "inj{SortD{}, SortT{}}(cD{}())";
    assert!(refuted(&[literal(&definition, "isA", item, true)]));
    // The item of a sequence with another element is not read (`isA` is false there whatever
    // the first element is).
    let longer = Predicate::Equals(
        term(
            &definition,
            &format!(
                "isA{{}}(kseq{{}}(inj{{SortT{{}}, SortKItem{{}}}}({x}), {}))",
                sequence(x, "T")
            ),
        ),
        term(&definition, &dv(false)),
    );
    assert!(!refuted(&[longer, literal(&definition, "isC", x, true)]));
}

/// A `\not` literal holds also where its item is undefined: over the partial `pf(Z)` it is not
/// read, unless another literal shows the item defined; over a variable it is.
#[test]
fn a_not_literal_over_a_partial_item_is_read_only_where_it_is_defined() {
    let definition = fixed("");
    let not = |predicate: &str, item: &str, value: bool| {
        Predicate::Not(Arc::new(literal(&definition, predicate, item, value)))
    };
    let partial = "pf{}(Z:SortT{})";
    // `\not(isA(pf(Z)) = false) /\ \not(isD(pf(Z)) = false)` holds where `pf(Z)` is undefined.
    let conjuncts = [not("isA", partial, false), not("isD", partial, false)];
    assert!(!contradictory(&definition, &conjuncts));
    // Shown defined by a literal not under `\not`.
    let conjuncts = [
        literal(&definition, "isA", partial, true),
        not("isD", partial, false),
    ];
    assert!(contradictory(&definition, &conjuncts));
    // Over a variable, which is defined.
    let conjuncts = [
        not("isA", "X:SortT{}", false),
        not("isD", "X:SortT{}", false),
    ];
    assert!(contradictory(&definition, &conjuncts));
}

/// A random poset of sorts below `KItem`, its membership predicates and near misses, and the
/// same definition with a witness constructor per sort.
struct Case {
    /// The definition the rule reads, some of whose sorts have no constructor.
    rule: BackendDefinition,
    /// `rule` with one witness constructor `w` + the sort's name per sort.
    truth: BackendDefinition,
    /// `below[i][j]`: sort `i` is below or equal to sort `j`.
    below: Vec<Vec<bool>>,
    /// The predicates: each sort's membership predicate, then the near misses.
    predicates: Vec<String>,
    /// The result sort of the partial function `pf : S0 -> S(partial)`.
    partial: usize,
}

type Rng<'a> = &'a mut dyn FnMut(usize) -> usize;

fn sort_name(index: usize) -> String {
    format!("S{index}")
}

impl Case {
    fn generate(next: Rng<'_>) -> Self {
        let count = 4 + next(3);
        let mut below = (0..count)
            .map(|i| (0..count).map(|j| i == j).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (sub, row) in below.iter_mut().enumerate().skip(1) {
            for edge in row.iter_mut().take(sub) {
                if next(3) == 0 {
                    *edge = true;
                }
            }
        }
        for middle in 0..count {
            for sub in 0..count {
                for sup in 0..count {
                    if below[sub][middle] && below[middle][sup] {
                        below[sub][sup] = true;
                    }
                }
            }
        }
        let constructed = (0..count).map(|_| next(2) == 0).collect::<Vec<_>>();
        let mut body = String::new();
        let mut predicates = Vec::new();
        for (index, &has_constructor) in constructed.iter().enumerate() {
            let name = sort_name(index);
            body.push_str(&format!(
                "sort {} []\n{}\n",
                sort(&name),
                subsort(&name, "KItem")
            ));
            let predicate = format!("is{name}");
            body.push_str(&membership(&predicate, &name));
            body.push('\n');
            predicates.push(predicate);
            if has_constructor {
                body.push_str(&format!(
                    "symbol c{name}{{}}() : {} [constructor{{}}(), functional{{}}(), injective{{}}()]\n",
                    sort(&name)
                ));
            }
        }
        for (sub, row) in below.iter().enumerate() {
            for (sup, &edge) in row.iter().enumerate() {
                if edge && sub != sup {
                    body.push_str(&subsort(&sort_name(sub), &sort_name(sup)));
                    body.push('\n');
                }
            }
        }
        for index in 0..next(3) {
            let miss = NEAR_MISSES[next(NEAR_MISSES.len())];
            let mut target = next(count);
            if matches!(miss, NearMiss::Constructor) {
                match (0..count).find(|sort| constructed[(target + sort) % count]) {
                    Some(offset) => target = (target + offset) % count,
                    None => continue,
                }
            }
            let other = next(count);
            let name = format!("nm{index}");
            body.push_str(&near_miss(
                &name,
                miss,
                &sort_name(target),
                &sort_name(other),
                &predicates[other],
            ));
            body.push('\n');
            predicates.push(name);
        }
        let partial = next(count);
        body.push_str(&format!(
            "symbol pf{{}}({}) : {} [function{{}}()]\n",
            sort(&sort_name(0)),
            sort(&sort_name(partial))
        ));
        let rule = load(&body);
        for index in 0..count {
            body.push_str(&format!(
                "symbol w{name}{{}}() : {} [constructor{{}}(), functional{{}}(), injective{{}}()]\n",
                sort(&sort_name(index)),
                name = sort_name(index)
            ));
        }
        let truth = load(&body);
        Self {
            rule,
            truth,
            below,
            predicates,
            partial,
        }
    }
}

/// An item of a conjunction: a variable of a declared sort, or the partial `pf(Z)`.
#[derive(Clone, Copy, Debug)]
enum Item {
    Variable(&'static str, usize),
    Partial,
}

impl Item {
    fn sort(self, case: &Case) -> usize {
        match self {
            Self::Variable(_, sort) => sort,
            Self::Partial => case.partial,
        }
    }

    fn symbolic(self) -> String {
        match self {
            Self::Variable(name, sort) => format!("{name}:{}", self::sort(&sort_name(sort))),
            Self::Partial => format!("pf{{}}(Z:{})", sort(&sort_name(0))),
        }
    }

    /// The values the item ranges over: the witness of each sort below its declared one (N7),
    /// and, for the partial item, `None` (undefined).
    fn values(self, case: &Case) -> Vec<Option<String>> {
        let declared = self.sort(case);
        let mut values = (0..case.below.len())
            .filter(|witness| case.below[*witness][declared])
            .map(|witness| {
                let constructor = format!("w{}{{}}()", sort_name(witness));
                Some(if witness == declared {
                    constructor
                } else {
                    format!(
                        "inj{{{}, {}}}({constructor})",
                        sort(&sort_name(witness)),
                        sort(&sort_name(declared))
                    )
                })
            })
            .collect::<Vec<_>>();
        if matches!(self, Self::Partial) {
            values.push(None);
        }
        values
    }
}

/// A literal: predicate `predicate` of item `item` required `polarity`; with `tail`, of a
/// two-element sequence (never read, since the predicates are false there).
#[derive(Clone, Copy, Debug)]
struct Literal {
    predicate: usize,
    item: usize,
    polarity: bool,
    tail: bool,
    /// The surface form of the literal as a Boolean term (`term_form`).
    form: usize,
}

impl Literal {
    fn flipped(self) -> Self {
        Self {
            polarity: !self.polarity,
            ..self
        }
    }
}

/// A conjunct over one or two literals, in one of the surface forms of "membership literals".
#[derive(Clone, Debug)]
struct Conjunct {
    literals: Vec<Literal>,
    /// How two literals are joined: `andBool`, `andThenBool`, or `notBool (orBool)` of their
    /// complements.
    join: usize,
    /// The predicate shape: the term, `\equals(term, true)`, or `\equals(atom, polarity)`.
    wrap: usize,
    /// `\not` of a predicate requiring the term false.
    negated: bool,
}

struct Rendering<'a> {
    case: &'a Case,
    items: &'a [Item],
    /// Each item's text.
    texts: &'a [String],
}

impl Rendering<'_> {
    fn atom(&self, literal: Literal) -> String {
        let declared = sort_name(self.items[literal.item].sort(self.case));
        let item = &self.texts[literal.item];
        let argument = if literal.tail {
            format!(
                "kseq{{}}(inj{{{}, SortKItem{{}}}}({item}), {})",
                sort(&declared),
                sequence(item, &declared)
            )
        } else {
            sequence(item, &declared)
        };
        format!(
            "{}{{}}({argument})",
            self.case.predicates[literal.predicate]
        )
    }

    /// A Boolean term true exactly where the literal holds.
    fn term_form(&self, literal: Literal) -> String {
        let atom = self.atom(literal);
        let polarity = literal.polarity;
        let boolean = |value: bool| sequence(&dv(value), "Bool");
        match literal.form {
            0 if polarity => atom,
            0 => format!("notBool{{}}({atom})"),
            1 => format!("eqBool{{}}({atom}, {})", dv(polarity)),
            2 => format!("neBool{{}}({atom}, {})", dv(!polarity)),
            // Forms 3 and 4 are kept, but the reader does not read `==K`/`=/=K` yet
            // (`conditions.rs`, "membership literals"): a literal in them is never read, so
            // they exercise only that the oracle stays sound, not the K-equality reading.
            3 => format!(
                "eqK{{}}({}, {})",
                sequence(&atom, "Bool"),
                boolean(polarity)
            ),
            4 => format!(
                "neK{{}}({}, {})",
                sequence(&atom, "Bool"),
                boolean(!polarity)
            ),
            _ => format!("eqBool{{}}({}, {atom})", dv(polarity)),
        }
    }

    /// A Boolean term true exactly where every literal of `conjunct` holds.
    fn conjunction(&self, conjunct: &Conjunct) -> String {
        match conjunct.literals.as_slice() {
            [literal] => self.term_form(*literal),
            [first, second] => match conjunct.join {
                0 => format!(
                    "andBool{{}}({}, {})",
                    self.term_form(*first),
                    self.term_form(*second)
                ),
                1 => format!(
                    "andThenBool{{}}({}, {})",
                    self.term_form(*first),
                    self.term_form(*second)
                ),
                _ => format!(
                    "notBool{{}}(orBool{{}}({}, {}))",
                    self.term_form(first.flipped()),
                    self.term_form(second.flipped())
                ),
            },
            _ => unreachable!("one or two literals"),
        }
    }

    fn predicate(&self, definition: &BackendDefinition, conjunct: &Conjunct) -> Predicate {
        let conjunction = self.conjunction(conjunct);
        let single = match conjunct.literals.as_slice() {
            [literal] => Some(*literal),
            _ => None,
        };
        // The predicate requiring the conjunction `value`.
        let requiring = |value: bool| match (conjunct.wrap, single) {
            (0, _) if value => Predicate::Term(term(definition, &conjunction)),
            (0, _) => Predicate::Term(term(definition, &format!("notBool{{}}({conjunction})"))),
            (2, Some(literal)) => Predicate::Equals(
                term(definition, &self.atom(literal)),
                term(definition, &dv(literal.polarity == value)),
            ),
            _ => Predicate::Equals(term(definition, &conjunction), term(definition, &dv(value))),
        };
        if conjunct.negated {
            Predicate::Not(Arc::new(requiring(false)))
        } else {
            requiring(true)
        }
    }
}

/// The value of a ground predicate by the simplifier, `None` when it is not decided.
fn evaluate(definition: &BackendDefinition, predicate: &Predicate) -> Option<bool> {
    let simplified = simplify_predicate_with_solver(
        definition,
        predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .ok()?
    .ok()?;
    match simplified {
        Predicate::True => Some(true),
        Predicate::False => Some(false),
        _ => None,
    }
}

/// The `membership` oracle: `cases` random conjunctions of one to four conjuncts over one or two
/// items, ten per generated definition, each refuted one checked against every assignment of
/// witnesses (and "undefined" for the partial item). Returns the failures, and how many
/// conjunctions the reader refuted.
pub(crate) fn membership_oracle(cases: usize) -> (Vec<String>, usize) {
    let mut state = 0x6d65_6d62_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let mut failures = Vec::new();
    let mut refuted = 0;
    let mut case = Case::generate(&mut next);
    for index in 0..cases {
        if index % 10 == 9 {
            case = Case::generate(&mut next);
        }
        let count = case.below.len();
        let pool = [
            Item::Variable("X", next(count)),
            Item::Variable("Y", next(count)),
            Item::Partial,
        ];
        let items = if next(2) == 0 {
            vec![pool[next(3)]]
        } else {
            let first = next(3);
            vec![pool[first], pool[(first + 1 + next(2)) % 3]]
        };
        let literal = |next: Rng<'_>| Literal {
            // A near miss, when the definition has one, a quarter of the time.
            predicate: if case.predicates.len() > count && next(4) == 0 {
                count + next(case.predicates.len() - count)
            } else {
                next(count)
            },
            item: next(items.len()),
            polarity: next(2) == 0,
            tail: next(12) == 0,
            form: next(6),
        };
        let conjuncts = (0..1 + next(4))
            .map(|_| Conjunct {
                literals: if next(4) == 0 {
                    vec![literal(&mut next), literal(&mut next)]
                } else {
                    vec![literal(&mut next)]
                },
                join: next(3),
                wrap: next(3),
                negated: next(3) == 0,
            })
            .collect::<Vec<_>>();
        let symbolic = items.iter().map(|item| item.symbolic()).collect::<Vec<_>>();
        let rendering = Rendering {
            case: &case,
            items: &items,
            texts: &symbolic,
        };
        let predicates = conjuncts
            .iter()
            .map(|conjunct| rendering.predicate(&case.rule, conjunct))
            .collect::<Vec<_>>();
        if !contradictory(&case.rule, &predicates) {
            continue;
        }
        refuted += 1;
        // Every assignment of a value to each item.
        let values = items
            .iter()
            .map(|item| item.values(&case))
            .collect::<Vec<_>>();
        let assignments = values.iter().map(Vec::len).product::<usize>();
        for assignment in 0..assignments {
            let mut rest = assignment;
            let chosen = values
                .iter()
                .map(|options| {
                    let value = options[rest % options.len()].clone();
                    rest /= options.len();
                    value
                })
                .collect::<Vec<_>>();
            let texts = chosen
                .iter()
                .map(|value| value.clone().unwrap_or_default())
                .collect::<Vec<_>>();
            let ground = Rendering {
                case: &case,
                items: &items,
                texts: &texts,
            };
            let mut holds = true;
            for conjunct in &conjuncts {
                // Over an undefined item a literal not under `\not` fails and one under `\not`
                // holds.
                let undefined = conjunct
                    .literals
                    .iter()
                    .any(|literal| chosen[literal.item].is_none());
                let value = if undefined {
                    Some(conjunct.negated)
                } else {
                    evaluate(&case.truth, &ground.predicate(&case.truth, conjunct))
                };
                match value {
                    Some(true) => {}
                    Some(false) => {
                        holds = false;
                        break;
                    }
                    None => {
                        failures.push(format!(
                            "undecided at {chosen:?}: {:?}",
                            ground.predicate(&case.truth, conjunct)
                        ));
                        holds = false;
                        break;
                    }
                }
            }
            if holds {
                failures.push(format!(
                    "refuted, but holds at {chosen:?}: {predicates:?} (predicates {:?}, order {:?})",
                    case.predicates, case.below
                ));
                break;
            }
        }
    }
    (failures, refuted)
}

#[test]
fn the_membership_oracle_agrees_by_default() {
    let (failures, refuted) = membership_oracle(2_000);
    assert!(failures.is_empty(), "{failures:#?}");
    // The oracle is exercised: a good share of the conjunctions is refuted.
    assert!(refuted >= 200, "only {refuted} refuted");
}

fn caught(switches: crate::confluence::switches::Switches) -> usize {
    let (failures, _) = crate::confluence::switches::with(switches, || membership_oracle(2_000));
    failures.len()
}

/// V7: reading two incomparable sorts as disjoint, ignoring their common subsorts, refutes
/// conjunctions satisfiable at a witness of a common subsort.
#[test]
fn disjoint_incomparable_memberships_are_caught_by_the_oracle() {
    assert!(
        caught(crate::confluence::switches::Switches {
            disjoint_incomparable_memberships: true,
            ..Default::default()
        }) > 0
    );
}

/// V7: reading a `\not` literal over an item not shown defined refutes conjunctions that hold
/// where the partial item is undefined.
#[test]
fn a_not_membership_without_definedness_is_caught_by_the_oracle() {
    assert!(
        caught(crate::confluence::switches::Switches {
            membership_not_without_definedness: true,
            ..Default::default()
        }) > 0
    );
}

/// V7: recognizing near misses as membership predicates refutes conjunctions their equations
/// satisfy.
#[test]
fn a_loose_membership_recognition_is_caught_by_the_oracle() {
    assert!(
        caught(crate::confluence::switches::Switches {
            loose_membership_recognition: true,
            ..Default::default()
        }) > 0
    );
}
