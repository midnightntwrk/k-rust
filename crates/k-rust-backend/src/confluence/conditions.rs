//! What the check reads from the conditions of a pair, after the simplifier has simplified their
//! conjunction with every claim withheld.
//!
//! The simplifier refutes a conjunction it evaluates to `\bottom`. Two propositional facts it does
//! not use are decided here, on the conjuncts it leaves. A conjunct states a Boolean literal when
//! it requires a term equal to a domain value of a sort whose domain kind is the Booleans
//! (`\equals(b, true)`), its negation, or a Bool-sorted term itself. A sort of that kind
//! (`SortBool`, or a sort hooked `BOOL.Bool`; `DomainKind::of_declared_sort`) has exactly the
//! domain values `true` and `false`, so a term of it equal to neither is no value, and the two
//! requirements on one term are complementary. A domain value of any other sort is never read as
//! a Boolean, whatever its spelling: a token or a `String` spelled `"true"` is one value of its
//! sort among others.
//!
//! - **complementary literals**: a Boolean atom required true by one conjunct and false by another
//!   (`N >Int M` beside `N <=Int M`, `notBool B` beside `B`). Comparisons are read up to their
//!   arithmetic identities (`a >Int b` is `b <Int a`, `a <=Int b` is `notBool (b <Int a)`,
//!   `a =/=Int b` is `notBool (a ==Int b)`), so the conjunction holds on no instance;
//! - **atoms true on every instance where they are defined**: `K in keys(M)` (`SET.in` of
//!   `MAP.keys`, or `MAP.in_keys`) where `K` is the key of an entry of the map term `M`, and
//!   `A ==K A`. Required false, such an atom makes the conjunction false wherever it is defined,
//!   and undefined elsewhere: a condition holds only where it is defined and true;
//! - **integer bounds**: the conjuncts that compare one integer term, the *key*, up to literal
//!   offsets (`key +Int c`, `c +Int key`, `key -Int c`, nested), with an integer literal state
//!   that the key lies in an interval with optional ends minus finitely many points. `Int` is the
//!   unbounded integers and `INT.lt`, `le`, `gt`, `ge`, `eq`, `ne` are total and exact, and
//!   `+Int` and `-Int` are total, so `key +Int c` is defined exactly where the key is and the set
//!   is exact; over the integers it is empty exactly when the interval is empty, or finite with
//!   every point excluded. The conjunction is refuted when one key's set is empty. Keys are
//!   decided independently, and a comparison of two non-literal terms bounds neither: sound, not
//!   complete for related keys (`X <Int Y` beside `Y <Int X` is not refuted). An integer
//!   literal is a domain value of a sort whose domain kind is the integers (`SortInt`, or a sort
//!   hooked `INT.Int`), read as the integer it denotes: the `INT` hooks interpret their operands
//!   as integers whatever the sort is named.
//!
//! Definedness of a key: a conjunct requiring a comparison atom true or false (`\equals(b, true)`,
//! `\equals(b, false)`, or `b` itself) holds only where `b` is defined, hence where the key is;
//! so does an ML `\equals(t, c)` with an integer literal `c`. A `\not(...)` of such a conjunct
//! also holds where the key is undefined, so its bound is used only when the key is `ceil_free`
//! or another conjunct shows it defined; ignoring a conjunct only weakens the conjunction.
//! After simplification the definedness of a partial key often arrives as a sibling conjunct
//! that no syntactic rule links to the key (`Y =/=Int 0` for `X /Int Y`), so
//! `notBool (X /Int Y >Int 5)` beside `notBool (X /Int Y <Int 6)` is not refuted: a known
//! non-refutation, sound.
//!
//! - **linear integer arithmetic**: each comparison of integer terms (and each ML `\equals`
//!   between them) is read as a linear form `Σ c·a + k` over *atoms*, the maximal integer
//!   subterms that are not `+Int`, `-Int`, `*Int` by a literal or an integer literal (all total
//!   and exact on the unbounded integers, so the form denotes the comparison exactly where its
//!   atoms are defined), compared with 0. A constant form decides its conjunct; a form `a + k`,
//!   `-a + k` or `a - b + k` is a difference constraint `x - y <= w` (strict comparisons tighten
//!   by 1 over the integers); any other form is ignored. The atoms' range facts, theorems of their
//!   hooks wherever the atom is defined, are added: `STRING.length`, `BYTES.length`, `LIST.size`,
//!   `MAP.size`, `SET.size` and `INT.abs` are at least 0, `INT.abs(x)` and `INT.max(x, y)` at
//!   least each operand of the form `atom + k` or a literal `k`, `INT.min(x, y)` at most each
//!   (`maxInt(N, 0) >=Int 0`). Difference
//!   constraints over the integers have a solution exactly when their graph has no negative cycle
//!   (Floyd and Warshall), and a disequality `x - y =/= k` fails where the closure forces
//!   `x - y = k`; then the conjunction is refuted. A conjunct is used only when it shows its atoms
//!   defined (a comparison required true or false, or an `\equals` with a `ceil_free` side), or
//!   every atom it mentions is `ceil_free` or shown defined by another conjunct: a `\not` holds
//!   also where an atom is undefined. Two variables the closure forces equal are an equality the
//!   join may apply. The bounds above are the special case of one atom; they are kept for their
//!   excluded points;
//! - **literals under `\not`**: a `\not` of a literal holds also where its term is undefined, so
//!   it is read as the negated literal only where the term is defined on every instance where the
//!   conjunction holds: it is `ceil_free`, another conjunct requires the same atom, or its only
//!   partial subterms are integer quotients and remainders by divisors another conjunct states
//!   nonzero (`X /Int Y` beside `\not(\equals(Y, 0))`, the definedness the simplifier states for
//!   a condition as a sibling conjunct);
//! - **disjunctions**: a conjunct `\or(d1, ..., dk)`, `a orBool b` or `a orElseBool b` required
//!   true, or `a andBool b` or `a andThenBool b` required false (not under `\not`), holds only
//!   where one of its disjuncts holds (`a` or `b` true, respectively false), so the conjunction is
//!   refuted when, for every choice of one disjunct per such conjunct, the choices with the other
//!   conjuncts are refuted by the rules above; at most three such conjuncts and 16 choices are
//!   split, beyond that the disjunctions are not read;
//! - **equality classes**: the terms the conjuncts require equal form classes: the operands of an
//!   equality atom (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq`, or a negated `ne`) required
//!   true, and the two sides of an ML `\equals(t, u)` neither of which is a Boolean literal. Such
//!   an atom holds only where both operands are defined, and then exactly when they are the same
//!   value (each hook is equality on its domain), and `\equals` is equality of patterns; equality
//!   is an equivalence relation. A class holding two different domain values of one sort (two
//!   different elements: the unifier reads them as a clash too) holds on no instance, nor does a
//!   class two of whose members a negative equality (the atom required false, or `\not` of the
//!   `\equals`) relates. The operands of `KEQUAL.eq` that are one-element sequences of injections
//!   from one sort are compared by their items (`kseq` is a free constructor, `inj` injective).
//!   A class with exactly one domain value gives each of its other members that value on every
//!   instance where the conjuncts hold, so each conjunct with the members replaced by the value
//!   holds there too (symbols denote functions: congruence); `Context::conditions` simplifies the
//!   rewritten conjunction once more and refutes it when that gives `\bottom` or a contradiction
//!   (`substring(S, I, I +Int 1) ==String "t"` beside `findChar(HEX, substring(S, I, I +Int 1), 0)
//!   =/=Int -1` becomes `findChar(HEX, "t", 0) =/=Int -1`, which evaluates to false);
//! - **membership literals**: a symbol `p` is the *membership predicate* of a sort `S` when its
//!   executable equations are exactly `p(kseq(inj{S, KItem}(V:S), dotk)) = true` in its highest
//!   priority group and `p(X) = false`, `X` of the argument's sort, in a lower one, both
//!   unconditional, without `ensures`, `concrete` or `symbolic`, with `p` unhooked and in no
//!   overload relation, and no executable equation is indexed at a bare variable or a
//!   conjunction (such an equation is offered at every index). This is read from the equations,
//!   never from the name (`isS` is what K generates), once per check ([`memberships`]). A conjunct
//!   states a membership literal of an item `u` when its Boolean literal is
//!   `p(kseq(inj{T, KItem}(u), dotk))` (exactly a `dotk` tail: `p` is false at a longer sequence
//!   whatever its first item) with a polarity, read through `notBool`, through `==Bool`,
//!   `=/=Bool`, `==K` and `=/=K` against a Boolean literal (each holds only where its operands
//!   are defined, and a Boolean sort has two values), and through `andBool` or `andThenBool`
//!   required true and `orBool` or `orElseBool` required false, which state both operands. A
//!   literal under `\not` holds also where its term is undefined, so it is read only where its
//!   whole term is shown defined; `p`, `kseq` and the injection are total, so a membership atom is
//!   defined where its item is: `ceil_free`, shown by the definedness rules above, or the item of
//!   a literal not under `\not`. For each item, `L` is the set of maximal common lower bounds of
//!   `T` and the sorts the item is required to lie in (from the sort graph; a sort variable or an
//!   unknown sort decides nothing). The conjunction is refuted when `L` is empty, or when a sort
//!   the item is required not to lie in is above every member of `L`.
//!
//!   This holds in every model of the definition's axioms that also satisfies two axioms of the
//!   matching theory which are no KORE axioms: injection composition,
//!   `inj{B, A}(inj{C, B}(x)) = inj{C, A}(x)`, and no confusion, `inj{A, K}(x) = inj{B, K}(y)`
//!   only through a common subsort of `A` and `B`. Where `p(...) = true` and the item lay in no
//!   image of `S`, the `false` equation, read with the priority antecedent, would give `false`; so
//!   the item lies in `S`'s image (`kseq` and `inj` are injective). By no confusion, the images of
//!   incomparable sorts meet only in the images of their common subsorts, so the item lies in the
//!   image of a sort below every sort required, hence below a member of `L` (the order is finite),
//!   and no such sort exists when `L` is empty. When every member `l` of `L` is below a sort `S'`
//!   required false, the item is `inj{l, KItem}(w) = inj{S', KItem}(inj{l, S'}(w))` by
//!   composition, where the `true` equation, which has no antecedent, gives `true`. No sort's
//!   emptiness is used: a common subsort with no constructor blocks the refutation, since
//!   carriers are nonempty. That class is the one every reader of the verdicts reads: the
//!   evaluator matches modulo both axioms, so on ground instances the rule decides what
//!   evaluation decides; the data judgement reads normal forms modulo them; and the normal-form
//!   model that follows from the pairs when evaluation terminates (the premise kink reads)
//!   satisfies composition (`Term::injection` composes chains), no confusion and the overload
//!   axioms (lowest forms are unique).
//! - **collection memberships**: a conjunct requiring `LIST.in(e, l)`, `SET.in(e, s)` or
//!   `MAP.in_keys(e, m)` true or false (not under `\not`, through `notBool`) is read against the
//!   collection's *members* when the collection is a list term without middle, a set or map term
//!   without rest, or `MAP.values(m)` (for `LIST.in`) or `MAP.keys(m)` (for `SET.in`) of a map
//!   term `m` without rest. The members are built as the hooks build them: a list's or set's
//!   elements as held, a map's keys (`in_keys`), and `m`'s values or keys converted to the element
//!   sort of the list or set the applied `values` or `keys` symbol declares, as those hooks
//!   convert them. `e` is read at the element sort as the membership hooks read it
//!   (`collection_item::read`), and only an item read as an element is used. Required true, the
//!   conjunct adds `\equals(e, x)` for its one member `x`, the disjunction of the `\equals(e, x_i)`
//!   for several members, and is refuted for none; required false, it adds
//!   `\not(\equals(e, x_i))` for each member. Two injections from one sort into one sort are
//!   compared by their operands (`inj` is injective). The conjunct holds only where `e` and the
//!   collection are defined, hence their members, and then the hook is true exactly when `e`
//!   equals a member: a defined list is the sequence of its elements, a defined set or map (its
//!   elements or keys pairwise distinct, none in its rest) the finite set or map of its elements
//!   or bindings, and `values` and `keys` list each binding's value or key once, in an order not
//!   read here (only the multiset is). So every added conjunct holds wherever the conjunction
//!   does. Not read: a list with a middle or a collection with a rest, which may hold `e`, and a
//!   `\not` of a membership, which also holds where an operand is undefined. The conjunction is
//!   refuted when it is contradictory as it is or with the added conjuncts: an added disjunction
//!   may push the cases past 16, and the conjunction as it is keeps every refutation it has. The
//!   added conjuncts serve only this decision; the equalities the join may apply and the
//!   literals of the equality classes are read from the conjuncts as they are.
//!
//! Every remaining conjunct `X = t` (a variable equal to a term without `X`) is an equality every
//! instance satisfying the conditions has, which the join may apply (`confluence.rs`).

use std::{collections::BTreeSet, sync::Arc};

use num_bigint::BigInt;
use rustc_hash::FxHashMap;

use crate::{
    builtin::{CollectionOperand, ResultCollection, read_collection_item},
    definition::BackendDefinition,
    matching::SortGraph,
    rule::{Concreteness, Predicate, RewriteRule, RuleRhs, TermIndex},
    substitution::{Substitution, substitute},
    term::{DomainKind, Name, Sort, Term, TermKind},
};

/// A Boolean atom up to the arithmetic identities above.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Atom {
    /// `left <Int right`.
    Less(Term, Term),
    /// `left == right` (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq`), arguments in term order.
    Equal(Term, Term),
    Other(Term),
}

/// Whether the conjuncts are contradictory by the rules of the module documentation, the domain
/// kinds of their sorts and the membership predicates read in `definition`.
#[cfg(test)]
pub(super) fn contradictory(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    contradictory_in(definition, &memberships(definition), conjuncts)
}

/// [`contradictory`] with the definition's membership predicates already read ([`memberships`]).
/// The conjuncts are tried as they are and, when their collection memberships add conjuncts
/// ([`collection_memberships`]), with those too: an added disjunction may push the cases past
/// [`DISJUNCT_CASES`], so the conjuncts as they are keep every refutation they have.
pub(super) fn contradictory_in(
    definition: &BackendDefinition,
    memberships: &Memberships,
    conjuncts: &[Predicate],
) -> bool {
    let contradictory = |conjuncts: &[Predicate]| {
        contradictory_without_cases(definition, memberships, conjuncts)
            || cases_contradictory(definition, memberships, conjuncts)
    };
    match collection_memberships(definition, conjuncts) {
        Expansion::Refuted => true,
        Expansion::Unchanged => contradictory(conjuncts),
        Expansion::Added(expanded) => contradictory(conjuncts) || contradictory(&expanded),
    }
}

/// What the collection memberships among the conjuncts add (module documentation, "collection
/// memberships").
enum Expansion {
    /// No membership is read.
    Unchanged,
    /// A membership is required true in a collection without members.
    Refuted,
    /// The conjuncts, then the conjuncts the memberships imply.
    Added(Vec<Predicate>),
}

/// The conjuncts each collection membership implies about its item and the collection's members
/// (module documentation, "collection memberships").
fn collection_memberships(definition: &BackendDefinition, conjuncts: &[Predicate]) -> Expansion {
    let open = super::switches::active().collection_membership_reads_open;
    let sorts = Some(definition.sort_graph());
    let mut added = Vec::new();
    for conjunct in conjuncts {
        if matches!(conjunct, Predicate::Not(_)) {
            continue;
        }
        let Some((term, polarity)) = literal(definition, conjunct) else {
            continue;
        };
        let (Atom::Other(term), polarity) = atom(&term, polarity) else {
            continue;
        };
        let Some((hook, [item, collection])) = hooked(&term) else {
            continue;
        };
        let Some((element_sort, members)) = collection_members(sorts, hook, collection, open)
        else {
            continue;
        };
        let item = match read_collection_item(sorts, item, &element_sort) {
            CollectionOperand::Element(item) => item.into_owned(),
            CollectionOperand::Wider { .. } | CollectionOperand::Unrelated => continue,
        };
        let equal = |member: &Term| {
            let (left, right) = peel_injections(&item, member);
            Predicate::Equals(left, right)
        };
        if polarity {
            match members.as_slice() {
                [] => return Expansion::Refuted,
                [member] => added.push(equal(member)),
                _ => added.push(Predicate::Or(members.iter().map(equal).collect())),
            }
        } else {
            added.extend(
                members
                    .iter()
                    .map(|member| Predicate::Not(Arc::new(equal(member)))),
            );
        }
    }
    if added.is_empty() {
        return Expansion::Unchanged;
    }
    let mut expanded = conjuncts.to_vec();
    expanded.extend(added);
    Expansion::Added(expanded)
}

/// The element sort of the collection a membership hook (`LIST.in`, `SET.in`, `MAP.in_keys`)
/// reads, and its members as the hooks hold them: the elements of a list term without middle or
/// of a set term without rest, the keys of a map term without rest, and the values (`LIST.in` of
/// `MAP.values`) or keys (`SET.in` of `MAP.keys`) of a map term without rest, converted to the
/// element sort of the list or set the applied symbol declares, as `MAP.values` and `MAP.keys`
/// build them. `open` (a defect switch) also takes the known members of a list with a middle or
/// of a collection with a rest.
fn collection_members(
    sorts: Option<&SortGraph>,
    hook: &str,
    collection: &Term,
    open: bool,
) -> Option<(Sort, Vec<Term>)> {
    match (hook, collection.kind()) {
        (
            "LIST.in",
            TermKind::List {
                definition,
                heads,
                rest,
            },
        ) => {
            let mut members = heads.iter().cloned().collect::<Vec<_>>();
            match rest {
                None => {}
                Some((_, tails)) if open => members.extend(tails.iter().cloned()),
                Some(_) => return None,
            }
            Some((definition.element_sort, members))
        }
        (
            "SET.in",
            TermKind::Set {
                definition,
                elements,
                rest,
            },
        ) if rest.is_none() || open => {
            Some((definition.element_sort, elements.iter().cloned().collect()))
        }
        (
            "MAP.in_keys",
            TermKind::Map {
                definition,
                entries,
                rest,
            },
        ) if rest.is_none() || open => Some((
            definition.key_sort,
            entries.iter().map(|(key, _)| key.clone()).collect(),
        )),
        (
            "LIST.in" | "SET.in",
            TermKind::Application {
                symbol, arguments, ..
            },
        ) => {
            let [map] = arguments.as_slice() else {
                return None;
            };
            let TermKind::Map {
                definition,
                entries,
                rest,
            } = map.kind()
            else {
                return None;
            };
            if rest.is_some() && !open {
                return None;
            }
            let result =
                ResultCollection::declared(symbol.attributes.result_collection.as_ref(), sorts);
            match (hook, symbol.attributes.hook.as_deref()) {
                ("LIST.in", Some("MAP.values")) => result.list_elements(
                    entries.iter().map(|(_, value)| value.clone()).collect(),
                    &definition.value_sort,
                ),
                ("SET.in", Some("MAP.keys")) => result.set_elements(
                    entries.iter().map(|(key, _)| key.clone()).collect(),
                    &definition.key_sort,
                ),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Two injections from one sort into one sort, compared by their operands (`inj` is injective);
/// any other two terms as they are.
fn peel_injections(left: &Term, right: &Term) -> (Term, Term) {
    match (left.kind(), right.kind()) {
        (
            TermKind::Injection {
                source: left_source,
                target: left_target,
                term: left_term,
            },
            TermKind::Injection {
                source: right_source,
                target: right_target,
                term: right_term,
            },
        ) if left_source == right_source && left_target == right_target => {
            (left_term.clone(), right_term.clone())
        }
        _ => (left.clone(), right.clone()),
    }
}

/// The most disjunctive conjuncts, and the most combinations of their disjuncts, that
/// [`cases_contradictory`] splits on.
const DISJUNCTIONS: usize = 3;
const DISJUNCT_CASES: usize = 16;

/// The disjuncts of a conjunct that holds only where one of them does: an ML `\or`, or a
/// connective required true or false not under `\not` (`a orBool b` or `a orElseBool b`
/// required true holds only where `a` or `b` is `true`; `a andBool b` or `a andThenBool b`
/// required false, also written `notBool (a andBool b)`, only where one is `false`).
fn disjuncts(definition: &BackendDefinition, conjunct: &Predicate) -> Option<Vec<Predicate>> {
    if let Predicate::Or(items) = conjunct {
        return Some(items.to_vec());
    }
    if matches!(conjunct, Predicate::Not(_)) {
        return None;
    }
    let (mut term, mut polarity) = literal(definition, conjunct)?;
    while let Some(("BOOL.not", [inner])) = hooked(&term) {
        let inner = inner.clone();
        term = inner;
        polarity = !polarity;
    }
    let (value, [left, right]) = (match hooked(&term)? {
        ("BOOL.or" | "BOOL.orElse", operands) if polarity => Some((true, operands)),
        ("BOOL.and" | "BOOL.andThen", operands) if !polarity => Some((false, operands)),
        _ => None,
    })?
    else {
        return None;
    };
    let side = |operand: &Term| {
        let literal = definition
            .domain_value(operand.sort(), if value { "true" } else { "false" })
            .ok()?;
        Some(Predicate::Equals(operand.clone(), literal))
    };
    Some(vec![side(left)?, side(right)?])
}

/// Whether the conjuncts are contradictory by cases: for at most [`DISJUNCTIONS`] disjunctive
/// conjuncts and [`DISJUNCT_CASES`] combinations of their disjuncts, every combination with the
/// other conjuncts is contradictory ([`contradictory_without_cases`]). A disjunctive conjunct
/// holds only where one of its disjuncts does, so the conjunction holds only where one of the
/// combinations does.
fn cases_contradictory(
    definition: &BackendDefinition,
    memberships: &Memberships,
    conjuncts: &[Predicate],
) -> bool {
    let mut split = Vec::new();
    let mut rest = Vec::new();
    for conjunct in conjuncts {
        match disjuncts(definition, conjunct) {
            Some(disjuncts) if split.len() < DISJUNCTIONS => split.push(disjuncts),
            _ => rest.push(conjunct.clone()),
        }
    }
    let cases = split.iter().map(Vec::len).product::<usize>();
    if split.is_empty() || cases > DISJUNCT_CASES {
        return false;
    }
    let misread = super::switches::active().misread_disjunction;
    let mut refuted = 0;
    for case in 0..cases {
        let mut conjunction = rest.clone();
        let mut index = case;
        for disjuncts in &split {
            let mut chosen = BTreeSet::new();
            super::flatten(disjuncts[index % disjuncts.len()].clone(), &mut chosen);
            conjunction.extend(chosen);
            index /= disjuncts.len();
        }
        if conjunction.contains(&Predicate::False)
            || contradictory_without_cases(definition, memberships, &conjunction)
        {
            refuted += 1;
            if misread {
                return true;
            }
        }
    }
    refuted == cases
}

/// [`contradictory`] without splitting disjunctions.
fn contradictory_without_cases(
    definition: &BackendDefinition,
    memberships: &Memberships,
    conjuncts: &[Predicate],
) -> bool {
    let mut seen = FxHashMap::<Atom, bool>::default();
    // A literal under `\not` holds also where its term is undefined: it is read only where the
    // term is shown defined wherever the conjunction holds (`Definedness`), or a literal not
    // under `\not` requires the same atom.
    let facts = Definedness::of(definition, conjuncts);
    let read = conjuncts
        .iter()
        .filter_map(|conjunct| {
            let (term, polarity) = literal(definition, conjunct)?;
            let defined = !matches!(conjunct, Predicate::Not(_)) || facts.defined(&term);
            let (atom, polarity) = atom(&term, polarity);
            Some((atom, polarity, defined))
        })
        .collect::<Vec<_>>();
    let shown = read
        .iter()
        .filter(|(_, _, defined)| *defined)
        .map(|(atom, _, _)| atom.clone())
        .collect::<rustc_hash::FxHashSet<_>>();
    for (atom, polarity, defined) in read {
        if !defined && !shown.contains(&atom) {
            continue;
        }
        if !polarity && holds_where_defined(&atom) {
            return true;
        }
        if polarity && fails_where_defined(&atom) {
            return true;
        }
        match seen.get(&atom) {
            Some(known) if *known != polarity => return true,
            Some(_) => {}
            None => {
                seen.insert(atom, polarity);
            }
        }
    }
    let merging = super::switches::active().misread_literal_classes;
    Classes::of(definition, conjuncts, merging).is_none()
        || integer_bounds_empty(definition, conjuncts)
        || Differences::of(definition, conjuncts).is_none()
        || memberships_contradictory(definition, memberships, &facts, conjuncts)
}

/// The membership predicates of a definition, each with its sort (module documentation,
/// "membership literals").
pub(super) type Memberships = FxHashMap<Name, Sort>;

/// The membership predicates of `definition`: each symbol `p` whose executable equations are
/// exactly `p(kseq(inj{S, KItem}(V:S), dotk)) = true` in its highest priority group and `p(X) =
/// false` in a lower one, with `X` of the argument's sort, both unconditional, without `ensures`,
/// `concrete` or `symbolic`, with `p` unhooked and in no overload relation, mapped to `S`. None
/// when some executable equation is indexed at a bare variable or a conjunction, since such an
/// equation is offered at every index. The meaning is read from the equations, never from the
/// symbol's name.
pub(super) fn memberships(definition: &BackendDefinition) -> Memberships {
    if super::switches::active().loose_membership_recognition {
        return loose_memberships(definition);
    }
    let theory = definition.function_theory();
    let offered_everywhere = [TermIndex::Variable, TermIndex::And].iter().any(|index| {
        theory
            .get(index)
            .is_some_and(|groups| groups.values().any(|group| !group.is_empty()))
    });
    if offered_everywhere {
        return Memberships::default();
    }
    theory
        .iter()
        .filter_map(|(index, groups)| {
            let TermIndex::Symbol(name) = index else {
                return None;
            };
            membership_sort(definition, name, groups).map(|sort| (name.clone(), sort))
        })
        .collect()
}

/// The sort `S` of which `name`, with the equations `groups` by priority, is the membership
/// predicate ([`memberships`]).
fn membership_sort(
    definition: &BackendDefinition,
    name: &Name,
    groups: &std::collections::BTreeMap<u8, Vec<std::sync::Arc<RewriteRule>>>,
) -> Option<Sort> {
    if definition.overloads().is_overloaded(name) {
        return None;
    }
    let mut groups = groups.values();
    let (Some(high), Some(low), None) = (groups.next(), groups.next(), groups.next()) else {
        return None;
    };
    let ([high], [low]) = (high.as_slice(), low.as_slice()) else {
        return None;
    };
    let value = |rule: &RewriteRule| match &rule.rhs {
        RuleRhs::Term(term)
            if rule.requires.is_empty()
                && rule.ensures.is_empty()
                && rule.existentials.is_empty()
                && rule.attributes.executable
                && !rule.attributes.simplification
                && matches!(rule.attributes.concreteness, Concreteness::Unconstrained) =>
        {
            boolean(definition, term)
        }
        _ => None,
    };
    if value(high) != Some(true) || value(low) != Some(false) {
        return None;
    }
    let argument = |rule: &RewriteRule| match rule.lhs.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.name == *name && symbol.attributes.hook.is_none() => match arguments.as_slice()
        {
            [argument] => Some(argument.clone()),
            _ => None,
        },
        _ => None,
    };
    let (high, low) = (argument(high)?, argument(low)?);
    if !matches!(low.kind(), TermKind::Variable(_)) || low.sort() != high.sort() {
        return None;
    }
    let item = crate::builtin::k_sequence_item(&high)?;
    matches!(item.kind(), TermKind::Variable(_)).then(|| item.sort())
}

/// A defect switch's recognition: the sort of the first equation of each symbol whose result is
/// `true` and whose argument is a sequence starting with an injection, whatever its other
/// equations, conditions, priorities, tail and injected pattern.
fn loose_memberships(definition: &BackendDefinition) -> Memberships {
    let mut memberships = Memberships::default();
    for (index, groups) in definition.function_theory() {
        let TermIndex::Symbol(name) = index else {
            continue;
        };
        let sort = groups.values().flatten().find_map(|rule| {
            let RuleRhs::Term(result) = &rule.rhs else {
                return None;
            };
            if boolean(definition, result) != Some(true) {
                return None;
            }
            let TermKind::Application { arguments, .. } = rule.lhs.kind() else {
                return None;
            };
            let TermKind::Application {
                arguments: sequence,
                ..
            } = arguments.first()?.kind()
            else {
                return None;
            };
            match sequence.first()?.kind() {
                TermKind::Injection { term, .. } => Some(term.sort()),
                _ => None,
            }
        });
        if let Some(sort) = sort {
            memberships.insert(name.clone(), sort);
        }
    }
    memberships
}

/// The item `u` and sort `S` of a membership atom `p(kseq(inj{T, KItem}(u), dotk))`, `p` the
/// membership predicate of `S`.
fn membership_atom(memberships: &Memberships, term: &Term) -> Option<(Term, Sort)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let [argument] = arguments.as_slice() else {
        return None;
    };
    if symbol.attributes.hook.is_some() {
        return None;
    }
    let sort = *memberships.get(&symbol.name)?;
    Some((crate::builtin::k_sequence_item(argument)?.clone(), sort))
}

/// The membership literals of the Boolean term `term` required with `polarity`: `(u, S, b)`
/// says that `u` lies in `S` when `b`, and does not when not `b`. The term is read through
/// `notBool`, `==Bool`, `=/=Bool`, `==K` and `=/=K` against a Boolean literal (each holds only
/// where its operands are defined, so the operand is the literal or its complement there),
/// `andBool` and `andThenBool` required true and `orBool` and `orElseBool` required false (both
/// operands hold, respectively fail).
fn membership_literals(
    definition: &BackendDefinition,
    memberships: &Memberships,
    term: &Term,
    polarity: bool,
    literals: &mut Vec<(Term, Sort, bool)>,
) {
    let both = |left: &Term, right: &Term, literals: &mut Vec<_>| {
        membership_literals(definition, memberships, left, polarity, literals);
        membership_literals(definition, memberships, right, polarity, literals);
    };
    match hooked(term) {
        Some(("BOOL.not", [inner])) => {
            membership_literals(definition, memberships, inner, !polarity, literals);
        }
        Some(("BOOL.and" | "BOOL.andThen", [left, right])) if polarity => {
            both(left, right, literals);
        }
        Some(("BOOL.or" | "BOOL.orElse", [left, right])) if !polarity => {
            both(left, right, literals);
        }
        Some((hook @ ("BOOL.eq" | "BOOL.ne" | "KEQUAL.eq" | "KEQUAL.ne"), [left, right])) => {
            let (left, right) = if hook.starts_with("KEQUAL") {
                match (sequence_item(left), sequence_item(right)) {
                    (Some(left), Some(right)) => (left, right),
                    _ => return,
                }
            } else {
                (left.clone(), right.clone())
            };
            if left.sort() != right.sort() {
                return;
            }
            let (operand, value) = match (boolean(definition, &left), boolean(definition, &right)) {
                (None, Some(value)) => (left, value),
                (Some(value), None) => (right, value),
                _ => return,
            };
            // `operand == value` required true gives the operand `value`, required false its
            // complement (a Boolean sort has the two values); `=/=` the other way round.
            let equal = hook.ends_with(".eq");
            membership_literals(
                definition,
                memberships,
                &operand,
                (value == polarity) == equal,
                literals,
            );
        }
        _ => {
            if let Some((item, sort)) = membership_atom(memberships, term) {
                literals.push((item, sort, polarity));
            }
        }
    }
}

/// Whether the Boolean term `term` is defined on every instance where the conjuncts hold: a
/// membership atom whose item is (its predicate, `kseq` and the injection are total), or an
/// application of a total symbol or a constructor, or an injection, of such terms, or a term
/// [`Definedness::defined`] shows defined.
fn membership_defined(
    memberships: &Memberships,
    facts: &Definedness,
    items: &rustc_hash::FxHashSet<Term>,
    term: &Term,
) -> bool {
    use crate::term::{FunctionType, SymbolType};
    if let Some((item, _)) = membership_atom(memberships, term) {
        return items.contains(&item) || facts.defined(&item);
    }
    if facts.defined(term) {
        return true;
    }
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            matches!(
                symbol.attributes.symbol_type,
                SymbolType::Constructor | SymbolType::Function(FunctionType::Total)
            ) && symbol.attributes.collection.is_none()
                && arguments
                    .iter()
                    .all(|argument| membership_defined(memberships, facts, items, argument))
        }
        TermKind::Injection { term, .. } => membership_defined(memberships, facts, items, term),
        _ => false,
    }
}

/// Whether the membership literals of the conjuncts are contradictory (module documentation,
/// "membership literals"): for some item, the sorts it is required to lie in, with its own sort,
/// have no common lower bound, or one it is required not to lie in is above each of their
/// maximal common lower bounds.
fn memberships_contradictory(
    definition: &BackendDefinition,
    memberships: &Memberships,
    facts: &Definedness,
    conjuncts: &[Predicate],
) -> bool {
    if memberships.is_empty() {
        return false;
    }
    let unguarded = super::switches::active().membership_not_without_definedness;
    let disjoint = super::switches::active().disjoint_incomparable_memberships;
    let mut read = Vec::new();
    for conjunct in conjuncts {
        let Some((term, polarity)) = literal(definition, conjunct) else {
            continue;
        };
        let mut literals = Vec::new();
        membership_literals(definition, memberships, &term, polarity, &mut literals);
        if !literals.is_empty() {
            read.push((term, matches!(conjunct, Predicate::Not(_)), literals));
        }
    }
    // A literal not under `\not` holds only where its term is defined, hence where its items
    // are; one under `\not` holds also where its term is undefined, so it is read only where its
    // whole term is shown defined.
    let defined_items = read
        .iter()
        .filter(|(_, under_not, _)| !under_not)
        .flat_map(|(_, _, literals)| literals.iter().map(|(item, _, _)| item.clone()))
        .collect::<rustc_hash::FxHashSet<_>>();
    let mut by_item = FxHashMap::<Term, (Vec<Sort>, Vec<Sort>)>::default();
    for (term, under_not, literals) in read {
        if under_not && !unguarded && !membership_defined(memberships, facts, &defined_items, &term)
        {
            continue;
        }
        for (item, sort, member) in literals {
            let entry = by_item.entry(item).or_default();
            if member {
                entry.0.push(sort);
            } else {
                entry.1.push(sort);
            }
        }
    }
    let graph = definition.sort_graph();
    let below = |sub: &Sort, sup: &Sort| matches!(graph.check_subsort(sub, sup), Ok(true));
    'items: for (item, (inside, outside)) in by_item {
        // The maximal common lower bounds of the item's sort and the sorts it lies in: every
        // common lower bound is below one of them (a finite order).
        let mut bounds = vec![item.sort()];
        for sort in &inside {
            let mut next = Vec::new();
            for bound in &bounds {
                if below(bound, sort) {
                    next.push(*bound);
                } else if below(sort, bound) {
                    next.push(*sort);
                } else if !disjoint {
                    let Some(common) = graph.maximal_common_subsorts(bound, sort) else {
                        // A sort variable or an unknown sort: the order does not decide it.
                        continue 'items;
                    };
                    next.extend(common);
                }
            }
            next.sort();
            next.dedup();
            bounds = next;
        }
        if bounds.is_empty() {
            return true;
        }
        if outside
            .iter()
            .any(|sort| bounds.iter().all(|bound| below(bound, sort)))
        {
            return true;
        }
    }
    false
}

/// What the conjuncts show about the definedness of terms, wherever they hold: the integer terms
/// they require nonzero (`d =/=Int 0` required true, or `\not(\equals(d, 0))`, which also holds
/// where `d` is undefined: [`Self::defined`] asks `d` defined too), and the keys they require
/// absent from a map (`MAP.in_keys(k, m)` or `k in keys(m)` required false, under `\not` only
/// when the atom is `ceil_free`, or a `Predicate::Absent`).
struct Definedness {
    nonzero: BTreeSet<Term>,
    absent: BTreeSet<(Term, Term)>,
}

impl Definedness {
    fn of(definition: &BackendDefinition, conjuncts: &[Predicate]) -> Self {
        let zero = |term: &Term| integer(definition, term) == Some(BigInt::from(0));
        let mut facts = Self {
            nonzero: BTreeSet::new(),
            absent: BTreeSet::new(),
        };
        for conjunct in conjuncts {
            if let Predicate::Absent(absence) = conjunct
                && matches!(absence.collection(), crate::rule::KeyedCollection::Map(_))
            {
                facts
                    .absent
                    .insert((absence.key().clone(), absence.rest().clone()));
                continue;
            }
            if let Predicate::Not(inner) = conjunct
                && let Predicate::Equals(left, right) = &**inner
            {
                if zero(right) {
                    facts.nonzero.insert(left.clone());
                    continue;
                }
                if zero(left) {
                    facts.nonzero.insert(right.clone());
                    continue;
                }
            }
            let Some((term, polarity)) = literal(definition, conjunct) else {
                continue;
            };
            let under_not = matches!(conjunct, Predicate::Not(_));
            match atom(&term, polarity) {
                (Atom::Equal(left, right), false) if !under_not => {
                    if zero(&right) {
                        facts.nonzero.insert(left);
                    } else if zero(&left) {
                        facts.nonzero.insert(right);
                    }
                }
                (Atom::Other(term), false) if !under_not || term.attributes().ceil_free() => {
                    match hooked(&term) {
                        Some(("MAP.in_keys", [key, map])) => {
                            facts.absent.insert((key.clone(), map.clone()));
                        }
                        Some(("SET.in", [key, set])) => {
                            if let Some(("MAP.keys", [map])) = hooked(set) {
                                facts.absent.insert((key.clone(), map.clone()));
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        facts
    }

    /// Whether `term` is defined on every instance where the conjuncts hold: it is `ceil_free`;
    /// an application of a total symbol (or a constructor) to such terms; an integer quotient or
    /// remainder (`INT.tdiv`, `tmod`, `ediv`, `emod`, each defined exactly where its divisor is
    /// nonzero) of such terms by a nonzero divisor; or a map of such keys and values with one
    /// entry whose key is absent from its rest, or with distinct domain values as keys and no
    /// rest (a map is defined exactly where its keys are pairwise distinct and absent from its
    /// rest).
    fn defined(&self, term: &Term) -> bool {
        use crate::term::{FunctionType, SymbolType};
        if term.attributes().ceil_free() {
            return true;
        }
        match term.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => {
                let arguments_defined = || arguments.iter().all(|argument| self.defined(argument));
                match (symbol.attributes.hook.as_deref(), arguments.as_slice()) {
                    (Some("INT.tdiv" | "INT.tmod" | "INT.ediv" | "INT.emod"), [_, divisor]) => {
                        self.nonzero.contains(divisor) && arguments_defined()
                    }
                    _ => {
                        matches!(
                            symbol.attributes.symbol_type,
                            SymbolType::Constructor | SymbolType::Function(FunctionType::Total)
                        ) && symbol.attributes.collection.is_none()
                            && arguments_defined()
                    }
                }
            }
            TermKind::Injection { term, .. } => self.defined(term),
            TermKind::Map { entries, rest, .. } => {
                let parts = entries
                    .iter()
                    .all(|(key, value)| self.defined(key) && self.defined(value))
                    && rest.as_ref().is_none_or(|rest| self.defined(rest));
                let entries = entries.iter().cloned().collect::<Vec<_>>();
                let distinct = match (entries.as_slice(), rest) {
                    ([(key, _)], Some(rest)) => self.absent.contains(&(key.clone(), rest.clone())),
                    (_, None) => entries.iter().enumerate().all(|(index, (key, _))| {
                        matches!(key.kind(), TermKind::DomainValue { .. })
                            && entries[index + 1..].iter().all(|(other, _)| {
                                matches!(other.kind(), TermKind::DomainValue { .. }) && other != key
                            })
                    }),
                    _ => false,
                };
                parts && distinct
            }
            _ => false,
        }
    }
}

/// The classes of the terms the conjuncts require equal (module documentation, "equality
/// classes"), with a union-find over the terms.
struct Classes {
    index: FxHashMap<Term, usize>,
    terms: Vec<Term>,
    parent: Vec<usize>,
}

impl Classes {
    fn node(&mut self, term: &Term) -> usize {
        if let Some(index) = self.index.get(term) {
            return *index;
        }
        let index = self.terms.len();
        self.index.insert(term.clone(), index);
        self.terms.push(term.clone());
        self.parent.push(index);
        index
    }

    fn find(&mut self, mut index: usize) -> usize {
        while self.parent[index] != index {
            self.parent[index] = self.parent[self.parent[index]];
            index = self.parent[index];
        }
        index
    }

    fn union(&mut self, left: &Term, right: &Term) {
        let (left, right) = (self.node(left), self.node(right));
        let (left, right) = (self.find(left), self.find(right));
        self.parent[left] = right;
    }

    /// The classes of the positive equalities among `conjuncts`, or `None` when the conjuncts
    /// are contradictory by them: a class holds two different domain values of one sort, or a
    /// negative equality relates two members of one class. `merging` also merges the operands
    /// of each negative equality (a defect switch).
    fn of(definition: &BackendDefinition, conjuncts: &[Predicate], merging: bool) -> Option<Self> {
        let mut classes = Self {
            index: FxHashMap::default(),
            terms: Vec::new(),
            parent: Vec::new(),
        };
        let mut apart = Vec::new();
        for conjunct in conjuncts {
            let Some((left, right, positive)) = equality(definition, conjunct) else {
                continue;
            };
            if positive || merging {
                classes.union(&left, &right);
            } else {
                apart.push((left, right));
            }
        }
        for (left, right) in apart {
            let (left, right) = (classes.node(&left), classes.node(&right));
            if classes.find(left) == classes.find(right) {
                return None;
            }
        }
        let mut literals = FxHashMap::<usize, Vec<Term>>::default();
        for index in 0..classes.terms.len() {
            if matches!(classes.terms[index].kind(), TermKind::DomainValue { .. }) {
                let root = classes.find(index);
                literals
                    .entry(root)
                    .or_default()
                    .push(classes.terms[index].clone());
            }
        }
        let clash = literals.values().any(|values| {
            values.iter().enumerate().any(|(position, value)| {
                values[position + 1..]
                    .iter()
                    .any(|other| other.sort() == value.sort() && other != value)
            })
        });
        (!clash).then_some(classes)
    }
}

/// The equality or disequality a conjunct states between two terms, and whether it is positive:
/// an equality atom (`INT.eq`, `KEQUAL.eq`, `BOOL.eq`, `STRING.eq` and their negations) required
/// true or false (not under `\not`), an ML `\equals(t, u)` neither of whose sides is a Boolean
/// literal, or its `\not`. The operands of `KEQUAL.eq` that are one-element sequences of an injection from one
/// sort are compared by the injected items: `kseq` is a free constructor and `inj` injective.
fn equality(definition: &BackendDefinition, conjunct: &Predicate) -> Option<(Term, Term, bool)> {
    let plain = |predicate: &Predicate| match predicate {
        Predicate::Equals(left, right)
            if boolean(definition, left).is_none() && boolean(definition, right).is_none() =>
        {
            Some((left.clone(), right.clone()))
        }
        _ => None,
    };
    if let Some((left, right)) = plain(conjunct) {
        return Some((left, right, true));
    }
    if let Predicate::Not(inner) = conjunct
        && let Some((left, right)) = plain(inner)
    {
        return Some((left, right, false));
    }
    // An atom required true or false holds only where its operands are defined; a `\not` of
    // such a requirement holds also where one is undefined, which no class describes.
    if matches!(conjunct, Predicate::Not(_)) {
        return None;
    }
    let (term, polarity) = literal(definition, conjunct)?;
    let (Atom::Equal(left, right), polarity) = atom(&term, polarity) else {
        return None;
    };
    let (left, right) = match (sequence_item(&left), sequence_item(&right)) {
        (Some(left), Some(right)) if left.sort() == right.sort() => (left, right),
        _ => (left, right),
    };
    Some((left, right, polarity))
}

/// The item of a one-element `K` sequence `kseq(inj{S, KItem}(item), dotk)`.
fn sequence_item(term: &Term) -> Option<Term> {
    let item = crate::builtin::k_sequence_item(term)?;
    match item.kind() {
        TermKind::Injection { term, .. } => Some(term.clone()),
        _ => None,
    }
}

/// The values the conjuncts give terms: each member of an equality class that holds exactly one
/// domain value, other than that value, with the value (module documentation, "equality
/// classes"). Empty when the conjuncts are contradictory by their classes.
pub(super) fn literal_values(
    definition: &BackendDefinition,
    conjuncts: &[Predicate],
) -> Vec<(Term, Term)> {
    let merging = super::switches::active().substitute_without_class;
    let Some(mut classes) = Classes::of(definition, conjuncts, merging) else {
        return Vec::new();
    };
    let mut literal_of = FxHashMap::<usize, Option<Term>>::default();
    for index in 0..classes.terms.len() {
        let term = classes.terms[index].clone();
        if matches!(term.kind(), TermKind::DomainValue { .. }) {
            let root = classes.find(index);
            let entry = literal_of.entry(root).or_insert(Some(term.clone()));
            if entry.as_ref() != Some(&term) {
                *entry = None;
            }
        }
    }
    let mut values = Vec::new();
    for index in 0..classes.terms.len() {
        let root = classes.find(index);
        let term = &classes.terms[index];
        if let Some(Some(literal)) = literal_of.get(&root)
            && term != literal
            && term.sort() == literal.sort()
        {
            values.push((term.clone(), literal.clone()));
        }
    }
    values.sort_by(|left, right| left.0.cmp(&right.0));
    if super::switches::active().misplace_class_literal {
        let literals = values
            .iter()
            .map(|(_, literal)| literal.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        for (_, literal) in &mut values {
            let position = literals
                .iter()
                .position(|known| known == literal)
                .unwrap_or(0);
            *literal = literals[(position + 1) % literals.len()].clone();
        }
    }
    values
}

/// Whether the conjuncts are refuted once each member of an equality class with one literal is
/// replaced by that literal and the rewritten conjunction is simplified again by `simplify`
/// (module documentation, "equality classes").
pub(super) fn refuted_by_literals(
    definition: &BackendDefinition,
    memberships: &Memberships,
    conjuncts: &[Predicate],
    simplify: &mut dyn FnMut(Predicate) -> Option<Predicate>,
) -> bool {
    let values = literal_values(definition, conjuncts);
    let Some(rewritten) = substituted(&values, conjuncts) else {
        return false;
    };
    let Some(simplified) = simplify(Predicate::And(rewritten.into())) else {
        return false;
    };
    let mut again = BTreeSet::new();
    super::flatten(simplified, &mut again);
    let again = again.into_iter().collect::<Vec<_>>();
    again.contains(&Predicate::False) || contradictory_in(definition, memberships, &again)
}

/// `conjuncts` with every innermost occurrence of a term of `values` replaced by its value, outside
/// quantifiers; `None` when nothing is replaced.
pub(super) fn substituted(
    values: &[(Term, Term)],
    conjuncts: &[Predicate],
) -> Option<Vec<Predicate>> {
    if values.is_empty() {
        return None;
    }
    let map = values.iter().cloned().collect::<FxHashMap<_, _>>();
    let mut changed = false;
    let rewritten = conjuncts
        .iter()
        .map(|conjunct| replace_in_predicate(conjunct, &map, &mut changed))
        .collect();
    changed.then_some(rewritten)
}

/// `term` with the innermost occurrences of the terms of `map` replaced by their values: a member
/// that holds another member keeps its own structure with the inner one replaced, which says
/// more (`lengthString(S +String T)` with `S +String T = "ab"` becomes `lengthString("ab")`, not
/// the literal its own class gives it). Each replaced occurrence has its value wherever the
/// conjuncts hold, so either choice is sound.
fn replace_in_term(term: &Term, map: &FxHashMap<Term, Term>, changed: &mut bool) -> Term {
    let mut local = false;
    let replaced = super::children(term)
        .iter()
        .map(|child| replace_in_term(child, map, &mut local))
        .collect();
    if local {
        *changed = true;
        return super::with_children(term, replaced);
    }
    if let Some(value) = map.get(term) {
        *changed = true;
        return value.clone();
    }
    term.clone()
}

fn replace_in_predicate(
    predicate: &Predicate,
    map: &FxHashMap<Term, Term>,
    changed: &mut bool,
) -> Predicate {
    let term = |term: &Term, changed: &mut bool| replace_in_term(term, map, changed);
    let arc = |inner: &std::sync::Arc<Predicate>, changed: &mut bool| {
        std::sync::Arc::new(replace_in_predicate(inner, map, changed))
    };
    match predicate {
        Predicate::Term(inner) => Predicate::Term(term(inner, changed)),
        Predicate::Equals(left, right) => {
            Predicate::Equals(term(left, changed), term(right, changed))
        }
        Predicate::Ceil(inner) => Predicate::Ceil(term(inner, changed)),
        Predicate::Floor(inner) => Predicate::Floor(term(inner, changed)),
        Predicate::Defined(inner) => Predicate::Defined(term(inner, changed)),
        Predicate::In(left, right) => Predicate::In(term(left, changed), term(right, changed)),
        Predicate::Not(inner) => Predicate::Not(arc(inner, changed)),
        Predicate::Implies(left, right) => {
            Predicate::Implies(arc(left, changed), arc(right, changed))
        }
        Predicate::Iff(left, right) => Predicate::Iff(arc(left, changed), arc(right, changed)),
        Predicate::And(items) => Predicate::And(
            items
                .iter()
                .map(|item| replace_in_predicate(item, map, changed))
                .collect(),
        ),
        Predicate::Or(items) => Predicate::Or(
            items
                .iter()
                .map(|item| replace_in_predicate(item, map, changed))
                .collect(),
        ),
        // Under a binder a member may mention the bound variable; leaving it as written only
        // decides less.
        Predicate::True
        | Predicate::False
        | Predicate::Exists(..)
        | Predicate::Forall(..)
        | Predicate::Absent(_) => predicate.clone(),
    }
}

/// The integers a key may take under the conjuncts that compare it with literals: an interval
/// with optional ends, minus finitely many excluded points.
#[derive(Default)]
struct Bounds {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
    excluded: BTreeSet<BigInt>,
}

impl Bounds {
    fn constrain(&mut self, relation: Relation, value: BigInt) {
        let at_least = |bounds: &mut Self, value: BigInt| {
            if bounds.lower.as_ref().is_none_or(|lower| *lower < value) {
                bounds.lower = Some(value);
            }
        };
        let at_most = |bounds: &mut Self, value: BigInt| {
            if bounds.upper.as_ref().is_none_or(|upper| *upper > value) {
                bounds.upper = Some(value);
            }
        };
        match relation {
            Relation::Less => at_most(self, value - 1),
            Relation::LessEqual => at_most(self, value),
            Relation::Greater => at_least(self, value + 1),
            Relation::GreaterEqual => at_least(self, value),
            Relation::Equal => {
                at_least(self, value.clone());
                at_most(self, value);
            }
            Relation::NotEqual => {
                self.excluded.insert(value);
            }
        }
    }

    /// Whether no integer is within the bounds: the interval is empty, or finite with each of its
    /// points excluded. The walk over the points runs only when the interval has at most as many
    /// points as are excluded.
    fn empty(&self) -> bool {
        let (Some(lower), Some(upper)) = (&self.lower, &self.upper) else {
            return false;
        };
        if lower > upper {
            return true;
        }
        if BigInt::from(self.excluded.len()) < upper - lower + 1 {
            return false;
        }
        let mut point = lower.clone();
        while &point <= upper {
            if !self.excluded.contains(&point) {
                return false;
            }
            point += 1;
        }
        true
    }
}

/// `key <relation> literal`.
#[derive(Clone, Copy, Debug)]
enum Relation {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl Relation {
    /// The relation that holds exactly where this one fails, on defined operands.
    fn negated(self) -> Self {
        match self {
            Self::Less => Self::GreaterEqual,
            Self::LessEqual => Self::Greater,
            Self::Greater => Self::LessEqual,
            Self::GreaterEqual => Self::Less,
            Self::Equal => Self::NotEqual,
            Self::NotEqual => Self::Equal,
        }
    }

    /// The relation with its operands swapped: `a < b` is `b > a`.
    fn mirrored(self) -> Self {
        match self {
            Self::Less => Self::Greater,
            Self::LessEqual => Self::GreaterEqual,
            Self::Greater => Self::Less,
            Self::GreaterEqual => Self::LessEqual,
            Self::Equal | Self::NotEqual => self,
        }
    }
}

/// The integer an integer literal denotes: a domain value of a sort whose domain kind in
/// `definition` is the integers, whose canonical text is its decimal (`DomainKind::Int`).
fn integer(definition: &BackendDefinition, term: &Term) -> Option<BigInt> {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if definition.domain_kind(sort) == Some(DomainKind::Int) =>
        {
            value.as_utf8().ok()?.parse().ok()
        }
        _ => None,
    }
}

/// `term` as `key + offset`, peeling `+Int` with an integer literal on either side and `-Int`
/// with one on the right (both total, so the sum is defined exactly where `key` is); `None` for
/// an integer literal, which has no key.
fn shifted(definition: &BackendDefinition, term: &Term) -> Option<(Term, BigInt)> {
    if integer(definition, term).is_some() {
        return None;
    }
    let peeled = match hooked(term) {
        Some(("INT.add", [left, right])) => {
            match (integer(definition, left), integer(definition, right)) {
                (None, Some(value)) => Some((left, value)),
                (Some(value), None) => Some((right, value)),
                _ => None,
            }
        }
        Some(("INT.sub", [left, right])) => integer(definition, right).map(|value| (left, -value)),
        _ => None,
    };
    match peeled {
        Some((inner, offset)) => {
            let (key, inner_offset) = shifted(definition, inner)?;
            Some((key, inner_offset + offset))
        }
        None => Some((term.clone(), BigInt::from(0))),
    }
}

/// `left <relation> right` as `key <relation'> literal`, when one side is an integer literal and
/// the other a shifted key; `None` when both or neither are literals.
fn compared(
    definition: &BackendDefinition,
    left: &Term,
    relation: Relation,
    right: &Term,
) -> Option<(Term, Relation, BigInt)> {
    match (integer(definition, left), integer(definition, right)) {
        (None, Some(value)) => {
            let (key, offset) = shifted(definition, left)?;
            Some((key, relation, value - offset))
        }
        (Some(value), None) => {
            let (key, offset) = shifted(definition, right)?;
            Some((key, relation.mirrored(), value - offset))
        }
        _ => None,
    }
}

/// The integer constraint `key <relation> literal` a conjunct states, and whether the conjunct
/// holding shows its key defined (module documentation, "Definedness of a key").
fn integer_constraint(
    definition: &BackendDefinition,
    conjunct: &Predicate,
) -> Option<(Term, Relation, BigInt, bool)> {
    let (mut term, mut polarity) = match conjunct {
        Predicate::Not(inner) => {
            let (key, relation, value, _) = integer_constraint(definition, inner)?;
            return Some((key, relation.negated(), value, false));
        }
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => (right.clone(), value),
                (None, Some(value)) => (left.clone(), value),
                (None, None) => {
                    let (key, relation, value) =
                        compared(definition, left, Relation::Equal, right)?;
                    return Some((key, relation, value, true));
                }
                (Some(_), Some(_)) => return None,
            }
        }
        Predicate::Term(term) => (term.clone(), true),
        _ => return None,
    };
    while let Some(("BOOL.not", [inner])) = hooked(&term) {
        let inner = inner.clone();
        term = inner;
        polarity = !polarity;
    }
    let Some((hook, [left, right])) = hooked(&term) else {
        return None;
    };
    let relation = match hook {
        "INT.lt" if super::switches::active().misread_interval_bound => Relation::LessEqual,
        "INT.lt" => Relation::Less,
        "INT.le" => Relation::LessEqual,
        "INT.gt" => Relation::Greater,
        "INT.ge" => Relation::GreaterEqual,
        "INT.eq" => Relation::Equal,
        "INT.ne" => Relation::NotEqual,
        _ => return None,
    };
    let relation = if polarity {
        relation
    } else {
        relation.negated()
    };
    let (key, relation, value) = compared(definition, left, relation, right)?;
    Some((key, relation, value, true))
}

/// Whether the conjuncts that compare one integer key with integer literals leave that key no
/// integer value (module documentation, "integer bounds"). A key's constraints are used only
/// when some conjunct shows it defined or it is `ceil_free`: otherwise a `\not` constraint also
/// holds where the key is undefined, which no interval describes.
fn integer_bounds_empty(definition: &BackendDefinition, conjuncts: &[Predicate]) -> bool {
    let mut constraints = FxHashMap::<Term, (bool, Vec<(Relation, BigInt)>)>::default();
    for conjunct in conjuncts {
        let Some((key, relation, value, shows_defined)) = integer_constraint(definition, conjunct)
        else {
            continue;
        };
        let entry = constraints.entry(key).or_default();
        entry.0 |= shows_defined;
        entry.1.push((relation, value));
    }
    constraints
        .into_iter()
        .any(|(key, (shown_defined, found))| {
            if !shown_defined && !key.attributes().ceil_free() {
                return false;
            }
            let mut bounds = Bounds::default();
            for (relation, value) in found {
                bounds.constrain(relation, value);
            }
            bounds.empty()
        })
}

/// A linear integer form `constant + Σ coefficient · atom` over atoms, the maximal subterms of
/// integer kind that are not `+Int`, `-Int`, `*Int` by a literal, or an integer literal.
#[derive(Clone, Debug, Default)]
struct Linear {
    constant: BigInt,
    atoms: std::collections::BTreeMap<Term, BigInt>,
    /// Every atom the terms mention, also those whose coefficients cancel: the form denotes the
    /// terms only where all of them are defined.
    mentioned: BTreeSet<Term>,
}

impl Linear {
    fn atom(term: &Term) -> Self {
        Self {
            constant: BigInt::from(0),
            atoms: [(term.clone(), BigInt::from(1))].into(),
            mentioned: [term.clone()].into(),
        }
    }

    fn add(mut self, other: Self, sign: i32) -> Self {
        self.mentioned.extend(other.mentioned);
        self.constant += BigInt::from(sign) * other.constant;
        for (atom, coefficient) in other.atoms {
            *self.atoms.entry(atom).or_default() += BigInt::from(sign) * coefficient;
        }
        self.atoms
            .retain(|_, coefficient| *coefficient != BigInt::from(0));
        self
    }

    fn scale(mut self, factor: &BigInt) -> Self {
        self.constant *= factor;
        for coefficient in self.atoms.values_mut() {
            *coefficient *= factor;
        }
        self.atoms
            .retain(|_, coefficient| *coefficient != BigInt::from(0));
        self
    }
}

/// `term`, of integer kind, as a linear form: `+Int`, `-Int` and `*Int` by an integer literal
/// are total and exact on the unbounded integers, so the form denotes the term exactly where its
/// atoms are defined.
fn linear(definition: &BackendDefinition, term: &Term) -> Linear {
    if let Some(value) = integer(definition, term) {
        return Linear {
            constant: value,
            ..Linear::default()
        };
    }
    match hooked(term) {
        Some(("INT.add", [left, right])) => {
            linear(definition, left).add(linear(definition, right), 1)
        }
        Some(("INT.sub", [left, right])) => {
            linear(definition, left).add(linear(definition, right), -1)
        }
        Some(("INT.mul", [left, right])) => {
            let (left, right) = (linear(definition, left), linear(definition, right));
            if left.mentioned.is_empty() {
                right.scale(&left.constant)
            } else if right.mentioned.is_empty() {
                left.scale(&right.constant)
            } else {
                Linear::atom(term)
            }
        }
        _ => Linear::atom(term),
    }
}

/// The linear constraint `form <relation> 0` a conjunct states between two integer terms, and
/// whether the conjunct holding shows its atoms defined: a comparison required true or false (or
/// written as a term), and an ML `\equals` with a `ceil_free` side; a `\not` of either holds also
/// where an atom is undefined.
fn linear_constraint(
    definition: &BackendDefinition,
    conjunct: &Predicate,
) -> Option<(Linear, Relation, bool)> {
    let is_int = |term: &Term| definition.domain_kind(&term.sort()) == Some(DomainKind::Int);
    let (mut term, mut polarity) = match conjunct {
        Predicate::Not(inner) => {
            let (form, relation, _) = linear_constraint(definition, inner)?;
            return Some((form, relation.negated(), false));
        }
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => (right.clone(), value),
                (None, Some(value)) => (left.clone(), value),
                (None, None) if is_int(left) && is_int(right) => {
                    let form = linear(definition, left).add(linear(definition, right), -1);
                    let shows = left.attributes().ceil_free()
                        || right.attributes().ceil_free()
                        || super::switches::active().misread_equals_definedness;
                    return Some((form, Relation::Equal, shows));
                }
                _ => return None,
            }
        }
        Predicate::Term(term) => (term.clone(), true),
        _ => return None,
    };
    while let Some(("BOOL.not", [inner])) = hooked(&term) {
        let inner = inner.clone();
        term = inner;
        polarity = !polarity;
    }
    let (hook, [left, right]) = hooked(&term)? else {
        return None;
    };
    let relation = match hook {
        "INT.lt" => Relation::Less,
        "INT.le" => Relation::LessEqual,
        "INT.gt" => Relation::Greater,
        "INT.ge" => Relation::GreaterEqual,
        "INT.eq" => Relation::Equal,
        "INT.ne" => Relation::NotEqual,
        _ => return None,
    };
    let relation = if polarity {
        relation
    } else {
        relation.negated()
    };
    let form = linear(definition, left).add(linear(definition, right), -1);
    Some((form, relation, true))
}

/// The difference constraints `x - y <= w` between the atoms of the conjuncts' linear
/// constraints (and a zero node), closed by Floyd and Warshall (module documentation, "linear
/// integer arithmetic").
struct Differences {
    atoms: Vec<Term>,
    /// `bound[i][j]`: an upper bound of `atom i - atom j` (index 0 is the constant 0).
    bound: Vec<Vec<Option<BigInt>>>,
}

impl Differences {
    fn index(&mut self, atom: &Term) -> usize {
        if let Some(position) = self.atoms.iter().position(|known| known == atom) {
            return position + 1;
        }
        self.atoms.push(atom.clone());
        for row in &mut self.bound {
            row.push(None);
        }
        self.bound.push(vec![None; self.atoms.len() + 1]);
        self.atoms.len()
    }

    /// Record `x - y <= weight`.
    fn edge(&mut self, x: usize, y: usize, weight: BigInt) {
        let cell = &mut self.bound[x][y];
        if cell.as_ref().is_none_or(|known| *known > weight) {
            *cell = Some(weight);
        }
    }

    /// The node and sign of a unit term of a form: `None` for any other coefficient.
    fn unit(&mut self, atom: &Term, coefficient: &BigInt) -> Option<(usize, bool)> {
        let positive = *coefficient == BigInt::from(1);
        (positive || *coefficient == BigInt::from(-1)).then(|| (self.index(atom), positive))
    }

    /// The nodes `(x, y)` and constant `k` with `form = x - y + k`, when the form is a unit or a
    /// difference form (`y` or `x` the zero node for a unit form).
    fn difference(&mut self, form: &Linear) -> Option<(usize, usize, BigInt)> {
        let terms = form.atoms.iter().collect::<Vec<_>>();
        let (x, y) = match terms.as_slice() {
            [(atom, coefficient)] => {
                let (node, positive) = self.unit(atom, coefficient)?;
                if positive { (node, 0) } else { (0, node) }
            }
            [(first, a), (second, b)] => {
                let (first, first_positive) = self.unit(first, a)?;
                let (second, second_positive) = self.unit(second, b)?;
                match (first_positive, second_positive) {
                    (true, false) => (first, second),
                    (false, true) => (second, first),
                    _ => return None,
                }
            }
            _ => return None,
        };
        Some((x, y, form.constant.clone()))
    }

    /// The closure of the conjuncts' difference constraints, with the range facts of their atoms;
    /// `None` when they leave no integer valuation: a constant form false, a negative cycle, or a
    /// disequality the closure forces to fail.
    fn of(definition: &BackendDefinition, conjuncts: &[Predicate]) -> Option<Self> {
        let constraints = conjuncts
            .iter()
            .filter_map(|conjunct| linear_constraint(definition, conjunct))
            .collect::<Vec<_>>();
        // An atom is defined on every instance where the conjunction holds when a conjunct that
        // shows its atoms defined mentions it, or it is `ceil_free`.
        let mut defined = BTreeSet::new();
        for (form, _, shows) in &constraints {
            if *shows {
                defined.extend(form.mentioned.iter().cloned());
            }
        }
        let guard = !super::switches::active().drop_dbm_definedness_guard;
        let mut differences = Self {
            atoms: Vec::new(),
            bound: vec![vec![None]],
        };
        let mut apart = Vec::new();
        for (form, relation, shows) in constraints {
            let usable = shows
                || !guard
                || form
                    .mentioned
                    .iter()
                    .all(|atom| defined.contains(atom) || atom.attributes().ceil_free());
            if !usable {
                continue;
            }
            if form.atoms.is_empty() {
                let zero = BigInt::from(0);
                let holds = match relation {
                    Relation::Less => form.constant < zero,
                    Relation::LessEqual => form.constant <= zero,
                    Relation::Greater => form.constant > zero,
                    Relation::GreaterEqual => form.constant >= zero,
                    Relation::Equal => form.constant == zero,
                    Relation::NotEqual => form.constant != zero,
                };
                if !holds {
                    return None;
                }
                continue;
            }
            let Some((x, y, k)) = differences.difference(&form) else {
                continue;
            };
            // x - y + k <relation> 0.
            match relation {
                Relation::Less => differences.edge(x, y, -k - 1),
                Relation::LessEqual => differences.edge(x, y, -k),
                Relation::Greater => differences.edge(y, x, k - 1),
                Relation::GreaterEqual => differences.edge(y, x, k),
                Relation::Equal => {
                    differences.edge(x, y, -k.clone());
                    differences.edge(y, x, k);
                }
                Relation::NotEqual => apart.push((x, y, -k)),
            }
        }
        differences.range_facts(definition);
        let nodes = differences.bound.len();
        for via in 0..nodes {
            for from in 0..nodes {
                let Some(first) = differences.bound[from][via].clone() else {
                    continue;
                };
                for to in 0..nodes {
                    if let Some(second) = differences.bound[via][to].clone() {
                        differences.edge(from, to, first.clone() + second);
                    }
                }
            }
        }
        if (0..nodes).any(|node| {
            differences.bound[node][node]
                .as_ref()
                .is_some_and(|weight| *weight < BigInt::from(0))
        }) {
            return None;
        }
        for (x, y, value) in apart {
            let at_most = differences.bound[x][y].as_ref() == Some(&value);
            let at_least = differences.bound[y][x].as_ref() == Some(&-value.clone());
            if at_most && at_least {
                return None;
            }
        }
        Some(differences)
    }

    /// The range facts of the atoms (module documentation): each holds wherever its atom is
    /// defined, and every atom here occurs in a constraint that holds only where it is defined.
    fn range_facts(&mut self, definition: &BackendDefinition) {
        let misread = super::switches::active().misread_range_fact;
        let lowest = BigInt::from(if misread { 1 } else { 0 });
        let flipped = super::switches::active().misread_min_max;
        let mut index = 0;
        while index < self.atoms.len() {
            let atom = self.atoms[index].clone();
            let node = index + 1;
            index += 1;
            match hooked(&atom) {
                Some((
                    "STRING.length" | "BYTES.length" | "LIST.size" | "MAP.size" | "SET.size",
                    _,
                )) => self.edge(0, node, -lowest.clone()),
                Some(("INT.abs", [operand])) => {
                    self.edge(0, node, -lowest.clone());
                    self.below(definition, node, operand);
                }
                // `misread_min_max` swaps the two directions (a defect switch).
                Some(("INT.max", [left, right])) if !flipped => {
                    self.below(definition, node, left);
                    self.below(definition, node, right);
                }
                Some(("INT.min", [left, right])) if flipped => {
                    self.below(definition, node, left);
                    self.below(definition, node, right);
                }
                Some(("INT.min" | "INT.max", [left, right])) => {
                    self.above(definition, node, left);
                    self.above(definition, node, right);
                }
                _ => {}
            }
        }
    }

    /// Record `operand <= atom node`, when the operand is a unit form or a literal.
    fn below(&mut self, definition: &BackendDefinition, node: usize, operand: &Term) {
        let form = linear(definition, operand);
        // A literal operand `k <= node`: 0 - node <= -k, node 0 standing for the integer 0.
        if form.atoms.is_empty() {
            self.edge(0, node, -form.constant.clone());
            return;
        }
        // operand = x + k (a positive unit form) <= node: x - node <= -k. A negative unit form
        // `k - y <= node` bounds a sum, which is no difference constraint.
        if let Some((x, 0, k)) = self.difference(&form)
            && x != 0
        {
            self.edge(x, node, -k);
        }
    }

    /// Record `atom node <= operand`, when the operand is a unit form or a literal.
    fn above(&mut self, definition: &BackendDefinition, node: usize, operand: &Term) {
        let form = linear(definition, operand);
        // A literal operand `node <= k`: node - 0 <= k.
        if form.atoms.is_empty() {
            self.edge(node, 0, form.constant.clone());
            return;
        }
        // node <= x + k: node - x <= k.
        if let Some((x, 0, k)) = self.difference(&form)
            && x != 0
        {
            self.edge(node, x, k);
        }
    }

    /// The pairs of atoms that are variables the closure forces equal.
    fn forced_equal(&self) -> Vec<(Term, Term)> {
        let mut pairs = Vec::new();
        for (i, left) in self.atoms.iter().enumerate() {
            for (j, right) in self.atoms.iter().enumerate().skip(i + 1) {
                let zero = Some(BigInt::from(0));
                if matches!(left.kind(), TermKind::Variable(_))
                    && matches!(right.kind(), TermKind::Variable(_))
                    && self.bound[i + 1][j + 1] == zero
                    && self.bound[j + 1][i + 1] == zero
                {
                    pairs.push((left.clone(), right.clone()));
                }
            }
        }
        pairs
    }
}

/// [`equalities`] of the conjuncts and of the equalities between variables their difference
/// constraints force (`X <=Int Y` beside `Y <=Int X`).
pub(super) fn equalities_with_bounds(
    definition: &BackendDefinition,
    conjuncts: &[Predicate],
) -> Substitution {
    let mut all = conjuncts.to_vec();
    if let Some(differences) = Differences::of(definition, conjuncts) {
        all.extend(
            differences
                .forced_equal()
                .into_iter()
                .map(|(left, right)| Predicate::Equals(left, right)),
        );
    }
    equalities(&all)
}

/// The equalities `X = t` among the conjuncts, as one idempotent substitution: each conjunct
/// `\equals(X, t)` (either orientation) with `X` not in `t`, applied to the ones found before.
pub(super) fn equalities(conjuncts: &[Predicate]) -> Substitution {
    let mut substitution = Substitution::new();
    for conjunct in conjuncts {
        let Predicate::Equals(left, right) = conjunct else {
            continue;
        };
        let (left, right) = (
            substitute(left, &substitution),
            substitute(right, &substitution),
        );
        let (variable, value) = match (left.kind(), right.kind()) {
            (TermKind::Variable(variable), _) => (variable.clone(), right.clone()),
            (_, TermKind::Variable(variable)) => (variable.clone(), left.clone()),
            _ => continue,
        };
        if value.attributes().variables.contains(&variable) {
            continue;
        }
        let single = Substitution::from([(variable.clone(), value.clone())]);
        for bound in substitution.values_mut() {
            *bound = substitute(bound, &single);
        }
        substitution.insert(variable, value);
    }
    substitution
}

/// The Boolean term a conjunct requires, and whether it requires it true.
fn literal(definition: &BackendDefinition, conjunct: &Predicate) -> Option<(Term, bool)> {
    match conjunct {
        Predicate::Equals(left, right) => {
            match (boolean(definition, left), boolean(definition, right)) {
                (Some(value), None) => Some((right.clone(), value)),
                (None, Some(value)) => Some((left.clone(), value)),
                _ => None,
            }
        }
        Predicate::Term(term) => Some((term.clone(), true)),
        Predicate::Not(inner) => {
            literal(definition, inner).map(|(term, polarity)| (term, !polarity))
        }
        _ => None,
    }
}

/// The value of a Boolean literal: a domain value of a sort whose domain kind in `definition` is
/// [`DomainKind::Bool`], which has exactly the values `true` and `false`. A domain value of any
/// other sort is one value of that sort whatever its spelling (a token or a `String` may read
/// `"true"`), so it is not a literal, and a conjunct comparing a term with it states no Boolean.
fn boolean(definition: &BackendDefinition, term: &Term) -> Option<bool> {
    match term.kind() {
        TermKind::DomainValue { sort, value }
            if definition.domain_kind(sort) == Some(DomainKind::Bool) =>
        {
            match value.as_bytes() {
                b"true" => Some(true),
                b"false" => Some(false),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The hook of an application's symbol, and its arguments.
fn hooked(term: &Term) -> Option<(&str, &[Term])> {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => symbol
            .attributes
            .hook
            .as_deref()
            .map(|hook| (hook, arguments.as_slice())),
        _ => None,
    }
}

/// The atom of `term` required with `polarity`, up to negation and the comparison identities.
fn atom(term: &Term, polarity: bool) -> (Atom, bool) {
    let ordered = |left: &Term, right: &Term| {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    };
    match hooked(term) {
        Some(("BOOL.not", [inner])) => atom(inner, !polarity),
        Some(("INT.lt", [left, right])) => (Atom::Less(left.clone(), right.clone()), polarity),
        Some(("INT.gt", [left, right])) => (Atom::Less(right.clone(), left.clone()), polarity),
        Some(("INT.le", [left, right])) if super::switches::active().misread_int_le => {
            (Atom::Less(left.clone(), right.clone()), !polarity)
        }
        Some(("INT.le", [left, right])) => (Atom::Less(right.clone(), left.clone()), !polarity),
        Some(("INT.ge", [left, right])) => (Atom::Less(left.clone(), right.clone()), !polarity),
        Some(("INT.eq" | "KEQUAL.eq" | "BOOL.eq" | "STRING.eq", [left, right])) => {
            let (left, right) = ordered(left, right);
            (Atom::Equal(left, right), polarity)
        }
        Some(("INT.ne" | "KEQUAL.ne" | "BOOL.ne" | "STRING.ne", [left, right])) => {
            let (left, right) = ordered(left, right);
            (Atom::Equal(left, right), !polarity)
        }
        _ => (Atom::Other(term.clone()), polarity),
    }
}

/// Whether the atom is true on every instance where it is defined.
fn holds_where_defined(atom: &Atom) -> bool {
    match atom {
        Atom::Equal(left, right) => left == right,
        Atom::Less(..) => false,
        Atom::Other(term) => match hooked(term) {
            Some(("SET.in", [key, set])) => {
                matches!(hooked(set), Some(("MAP.keys", [map])) if has_key(map, key))
            }
            Some(("MAP.in_keys", [key, map])) => has_key(map, key),
            _ => false,
        },
    }
}

/// Whether the atom is false on every instance where it is defined.
fn fails_where_defined(atom: &Atom) -> bool {
    matches!(atom, Atom::Less(left, right) if left == right)
}

/// Whether the map term `map` has an entry with the key `key`.
fn has_key(map: &Term, key: &Term) -> bool {
    matches!(map.kind(), TermKind::Map { entries, .. } if entries.iter().any(|(entry, _)| entry == key))
}

#[cfg(test)]
mod collection_membership_tests;
#[cfg(test)]
mod membership_tests;
#[cfg(test)]
mod string_tests;
#[cfg(test)]
mod tests;
