//! K7's generator data: every spelling states what it matches and denotes, every slot has a
//! driver or says why not, every static production of the terms base has a spelling, and the
//! drivers write the programs and the cells their documentation describes.

use std::collections::{BTreeMap, BTreeSet};

use krs_test_support::class_matrix::k7::{Ground, K7, Meaning, Removed, SkipKind, Status};
use krs_test_support::class_matrix::{self, Base, Case, Command, Extent, Family, Side};

fn term_case(cases: &[Case], id: &str) -> Case {
    cases
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("no case {id}"))
        .clone()
}

/// The spellings with no witness or no value, by reason: what K7 cannot run them on. A spelling
/// that states neither (the defaults) would show as `no witness is stated` or `no value is
/// stated`, which no spelling may keep.
#[test]
fn every_spelling_states_its_witness_and_its_value_or_why_not() {
    let mut missing = BTreeMap::<String, Vec<String>>::new();
    for meaning in class_matrix::spelling_meanings() {
        let family = meaning.family.name();
        if let Err(reason) = meaning.witness {
            missing
                .entry(format!("no witness: {reason}"))
                .or_default()
                .push(format!("{family} {}", meaning.text));
        }
        if let Meaning::Undefined(reason) | Meaning::Unstated(reason) | Meaning::NoTerm(reason) =
            meaning.value
        {
            missing
                .entry(format!("no value: {reason}"))
                .or_default()
                .push(format!("{family} {}", meaning.text));
        }
    }
    for reason in [
        "no witness: no witness is stated",
        "no value: no value is stated",
    ] {
        assert!(
            !missing.contains_key(reason),
            "{reason}: {:?}",
            missing[reason]
        );
    }
    let listed = missing
        .iter()
        .map(|(reason, spellings)| format!("{reason}: {}", spellings.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, MISSING, "{listed:#?}");
}

const MISSING: &[&str] = &[
    "no value: Size is partial and the base gives it no equation, so its application has no value: a function has a value only where its equations give one: terms Size(x)",
    "no value: a cell's value, which the generator's ground terms do not write: terms k::fragment![crate::Frame { ret: 1 }]",
    "no value: a matching-logic predicate, which only a prover reads: terms k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "no value: a pattern, which names or tests a term and builds none: terms _ | terms y @ Cmd::Hold(_) | terms Cmd::Go() | Cmd::Hold(_) | terms Cmd::Pair { a: x, .. } | terms [x, ..] | terms Cmd::Tw(y @ Cmd::Hold(x)) | terms Cmd::Pair(1 | 2, 3 | 4)",
    "no value: an anonymous variable, which names no value: terms k::anonymous!(Int, \"_V\")",
    "no value: its expansion depends on what a program writes, or there is none: terms Cmd::Dn(x) | terms Cmd::Tw(_) | terms Cmd::Dn(2) | terms Cmd::Lp(0) | terms Cmd::Pb(Cmd::Go())",
    "no value: the empty map has no entry at x: notation k::builtin::map::empty()[x] | notation k::builtin::map::get(k::builtin::map::empty(), x)",
    "no value: the let's pattern does not match x: terms { let y @ Cmd::Hold(_) = x; y } | terms { let (Cmd::Go() | Cmd::Hold(_)) = x; x } | terms { let Cmd::Pair { a: _, b } = x; Cmd::Pair { a: 1, b } }",
    "no value: the update's base, x, is no Pair: terms Cmd::Pair { a: x, ..x }",
    "no value: x is no Bool: terms x && true | terms x || true",
    "no witness: a cell's value, which a program writes no syntax for: terms k::fragment![crate::Frame { ret: 1 }]",
    "no witness: a computed term, which no evaluated term is: terms k::builtin::int::add(1, 2) | terms Size(x) | terms k::or_bool!(true, false) | terms k::is!(Int, x) | terms k::project!(Int, x) | terms k::matches!(x, Cmd::Hold(_)) | terms { let y = x; y } | terms { let y @ Cmd::Hold(_) = x; y } | terms { let (Cmd::Go() | Cmd::Hold(_)) = x; x } | terms Cmd::Pair { a: x, ..x } | terms { let Cmd::Pair { a: _, b } = x; Cmd::Pair { a: 1, b } } | terms x + 1 | terms x & 1 | terms x << 1 | terms x / 2 | terms x % 2 | terms x >> 1 | terms x < 1 | terms x == 1 | terms x && true | terms x || true | terms !(x < 1) | terms -(x + 1) | terms x.add::<Int>(1) | terms k::builtin::int::add(x, 1) | terms k::map![x -> 1] | terms map![x -> 1] | notation k::builtin::map::empty()[x] | notation k::builtin::map::get(k::builtin::map::empty(), x) | notation k::builtin::list::item(x)[0] | notation k::builtin::list::get(k::builtin::list::item(x), 0) | notation k::builtin::map::empty().update(x, 1) | notation k::builtin::map::update(k::builtin::map::empty(), x, 1) | notation k::builtin::list::item(x).len() | notation k::builtin::list::size(k::builtin::list::item(x)) | notation k::builtin::set::item(x).to_list() | notation k::builtin::set::to_list(k::builtin::set::item(x)) | notation k::builtin::map::empty().contains_key(x) | notation k::builtin::map::in_keys(x, k::builtin::map::empty()) | notation map![x -> 1, 2 -> 3] | notation k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), 2, 3) | notation map![x -> 1, ..k::builtin::map::empty()] | notation map![0 -> 1] | notation k::builtin::map::update(k::builtin::map::empty(), 0, 1) | notation set![x, 1] | notation k::builtin::set::union(k::builtin::set::item(x), k::builtin::set::item(1)) | notation set![x, ..k::builtin::set::empty()] | notation k::builtin::set::union(k::builtin::set::empty(), k::builtin::set::item(x))",
    "no witness: a matching-logic predicate, which only a prover reads: terms k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "no witness: its expansion depends on what a program writes, or there is none: terms Cmd::Dn(x) | terms Cmd::Tw(_) | terms Cmd::Dn(2) | terms Cmd::Lp(0) | terms Cmd::Pb(Cmd::Go())",
];

/// The slots K7 runs no case of, by reason: the forms a run cannot exercise, and the one slot
/// whose hole a fixed binder value cannot drive. No slot falls through to "no driver is
/// written".
#[test]
fn every_slot_has_a_driver_or_says_why_not() {
    let cases = class_matrix::cases();
    let mut undriven = BTreeMap::<String, Vec<String>>::new();
    for case in cases.iter().filter(|case| case.term.is_some()) {
        if let K7::Skip(skip) = &case.k7
            && skip.kind == SkipKind::Form
        {
            let slot = case
                .id
                .strip_suffix(case.construct.as_str())
                .and_then(|slot| slot.strip_suffix('/'))
                .unwrap_or(case.id.as_str());
            let slot = slot
                .split_once('/')
                .map_or(slot, |(_, slot)| slot)
                .to_owned();
            let slots = undriven.entry(skip.reason.clone()).or_default();
            if !slots.contains(&slot) {
                slots.push(slot);
            }
        }
    }
    assert!(
        !undriven
            .keys()
            .any(|reason| reason.starts_with("no driver is written")),
        "{undriven:#?}"
    );
    let listed = undriven
        .iter()
        .map(|(reason, slots)| format!("{reason}: {}", slots.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, UNDRIVEN, "{listed:#?}");
}

const UNDRIVEN: &[&str] = &[
    "a claim is proved, not run, and needs a prover (L4 keeps claims in the fixture gates): cells-claim/guard | cells-claim/item-root | cells-claim/result-item-root | cells-claim/result | cells-claim/subject | claim/item-root | claim/result-item-root | claim/result | claim/subject | cells-claim/guard/closure-body",
    "a constant has no program syntax, and no base sentence can name the case's constant: constant/value-root | constant/value",
    "a context alias acts only through a production strict in it, and neither the base nor the case declares one: context-alias/item-root | context-alias/map-key | context-alias/subject",
    "the base applies no function but Probe, ProbeK and Size from a rule: equation/subject-root",
    "the function is internal: it has no program syntax, and no base sentence can name the case's function: shorthand/result-root | shorthand/result",
    "the simplification holds under the condition false only, which no input satisfies, so its twin has nothing to evaluate: simplification/result-root | simplification/subject-root",
];

/// Every case's K7 status, a skip by its kind and reason, with its count, the cases that run a
/// counter-witness, and those that run at another input: a change that moves cases into a skip,
/// or out of a counter run or another input, fails here, whatever reason the skip gives.
#[test]
fn every_cases_k7_status_is_counted() {
    let cases = class_matrix::cases();
    let mut statuses = BTreeMap::<String, usize>::new();
    // The run families' statuses are pinned by family ([`RUN_STATUSES`]).
    for case in cases.iter().filter(|case| case.family.twin().is_none()) {
        let status = match &case.k7 {
            K7::Run(run) => format!("runs, {}", run.status.name()),
            K7::Skip(skip) => format!("{}: {}", skip.kind.name(), skip.reason),
        };
        *statuses.entry(status).or_default() += 1;
        if !case.k7_counters.is_empty() {
            *statuses
                .entry("runs a counter-witness".to_owned())
                .or_default() += 1;
        }
        if !case.k7_inputs.is_empty() {
            *statuses
                .entry("runs at another input".to_owned())
                .or_default() += 1;
        }
    }
    let listed = statuses
        .iter()
        .map(|(status, count)| format!("{count} {status}"))
        .collect::<Vec<_>>();
    assert_eq!(listed, STATUSES, "{listed:#?}");
}

/// The initializer cases whose run reads nothing of their spelling, by reason: their plans are
/// liveness only (the run starts, and the configuration's other cells hold the base's values).
#[test]
fn every_initializer_case_that_reads_nothing_of_its_spelling_says_why() {
    let cases = class_matrix::cases();
    let mut unread = BTreeMap::<&str, Vec<&str>>::new();
    for case in &cases {
        let Some(reason) = class_matrix::initializer_unread(case) else {
            continue;
        };
        assert!(
            matches!(&case.k7, K7::Run(run) if run.status == Status::Liveness),
            "{}: {:?}",
            case.id,
            case.k7
        );
        unread
            .entry(reason)
            .or_default()
            .push(case.id.strip_prefix("init/").expect("an initializer case"));
    }
    let listed = unread
        .iter()
        .map(|(reason, cases)| format!("{reason}: {}", cases.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, UNREAD, "{listed:#?}");
}

const UNREAD: &[&str] = &[
    "a collection's initializer writes one instance's template, and the collection starts with no instance: no driver command of the machine or the typed base creates one, so no run reads the template: job/0 | job/Frame { ret: 0 } | job/Job { payload: 0 } | job/None | job/Some(0) | job/[0] | job/[] | job/[pgm] | job/k::absent!(0) | job/k::builtin::map::empty() | job/k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), pgm, 1), 0, 2) | job/k::k![0] | job/k::k![] | job/k::k![pgm] | job/k::map![0 -> 1] | job/k::map![] | job/k::map![pgm -> 1, 0 -> 2] | job/list::empty() | job/pgm | typed/slot/1 | typed/slot/Cmd::Go() | typed/slot/Val::Unit() | typed/slot/any",
];

const STATUSES: &[&str] = &[
    "858 no driver: a claim is proved, not run, and needs a prover (L4 keeps claims in the fixture gates)",
    "186 no driver: a constant has no program syntax, and no base sentence can name the case's constant",
    "200 no driver: a context alias acts only through a production strict in it, and neither the base nor the case declares one",
    "26 no driver: a malformed attribute is refused",
    "26 no driver: a simplification only rewrites what a prover simplifies, and needs a prover",
    "79 no driver: the base applies no function but Probe, ProbeK and Size from a rule",
    "3559 no driver: the compiled sweep's cases witness the compiler's verdict on each root sweep cell; the sweep base has no driver commands to set its cells up",
    "186 no driver: the function is internal: it has no program syntax, and no base sentence can name the case's function",
    "3 no driver: the function the case declares for the solver has no driver command",
    "154 no driver: the kinds base's initializer cases have no K7 plan yet: the values its cells' initializers denote are not written as K7 grounds (S5.0g part (b))",
    "1206 no driver: the readable, claim and `cells!` families read cells the machine, typed and kinds bases start at fixed values, and those bases have no driver commands to set them up (a claim needs a prover besides)",
    "4 no driver: the sentence cannot take both attributes, and is refused",
    "160 no driver: the simplification holds under the condition false only, which no input satisfies, so its twin has nothing to evaluate",
    "7 no value: a cell's value, which the generator's ground terms do not write",
    "113 no value: a matching-logic predicate, which only a prover reads",
    "175 no value: a pattern, which names or tests a term and builds none",
    "35 no value: an anonymous variable, which names no value",
    "21 no value: refused at K2, so no definition is emitted to run",
    "5 no value: the condition's stated value, \"s\", is no Bool",
    "5 no value: the condition's stated value, $x, is no Bool",
    "5 no value: the condition's stated value, -1, is no Bool",
    "5 no value: the condition's stated value, -2, is no Bool",
    "10 no value: the condition's stated value, 0, is no Bool",
    "60 no value: the condition's stated value, 1, is no Bool",
    "5 no value: the condition's stated value, 1.5, is no Bool",
    "20 no value: the condition's stated value, 2, is no Bool",
    "5 no value: the condition's stated value, 3, is no Bool",
    "16 no value: the condition's stated value, Cmd::Go(), is no Bool",
    "11 no value: the condition's stated value, Cmd::Hold(1), is no Bool",
    "5 no value: the condition's stated value, Wrap(1), is no Bool",
    "10 no value: the condition's stated value, [1], is no Bool",
    "5 no value: the condition's stated value, b\"ab\", is no Bool",
    "10 no value: the condition's stated value, map{0 -> 1}, is no Bool",
    "10 no value: the condition's stated value, map{1 -> 1, 2 -> 3}, is no Bool",
    "25 no value: the condition's stated value, map{1 -> 1}, is no Bool",
    "10 no value: the condition's stated value, map{}, is no Bool",
    "35 no value: the condition's stated value, set{1}, is no Bool",
    "10 no value: the condition's stated value, set{}, is no Bool",
    "5 no value: the condition's stated value, word, is no Bool",
    "1 no value: the function context looks up a key with no value, and an equation that does not apply leaves its application with the configuration it read, which the generator does not state",
    "6 no value: the hole has no value at the input, where the simplification's condition does not hold, so it states nothing there",
    "2 no value: the let's pattern does not match x",
    "6 no value: x is no Bool",
    "43 no witness: a cell's value, which a program writes no syntax for",
    "1872 no witness: a computed term, which no evaluated term is",
    "43 no witness: a matching-logic predicate, which only a prover reads",
    "4 no witness: a program writes $x only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "4 no witness: a program writes Wrap(1) only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "4 no witness: a program writes [1, 2] only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "8 no witness: a program writes map{} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "2 no witness: a program writes set{1, Cmd::Hold(1)} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "16 no witness: a program writes set{1} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "8 no witness: a program writes set{} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "20 no witness: its expansion depends on what a program writes, or there is none",
    "12 no witness: the clause's result leaves `y` to the sentence it is expanded in, and a program binds no name",
    "80 no witness: the context's hole is the construct's x, which K7 binds to 1, a KResult no context heats",
    "3 no witness: the program would hold a value the generator does not state",
    "1203 runs a counter-witness",
    "2131 runs at another input",
    "1630 runs, liveness",
    "245 runs, undefined",
    "266 runs, undefined result",
    "2773 runs, value",
];

/// Every spelling that reads `x` states the values of `x` besides 1 its cases run at, or why it
/// has none; at one of them at least its witness or its value differs from its witness or value
/// at 1, so that a run there can fail where the run at 1 conforms (a constant folded in); an input
/// at which it agrees with 1 is there to separate it from another operator
/// (`every_operator_spelling_differs_from_every_other_operator_of_its_class_on_its_inputs`). A pattern spelling that reads `x` and does not
/// match 1 has `Int` inputs, which it does not match either (its `matches_x` holds at every
/// input), and those that match 1 are the binder and its alternative, which match every term.
#[test]
fn every_spelling_that_reads_x_states_its_inputs_or_why_not() {
    let mut none = BTreeMap::<&str, Vec<String>>::new();
    let mut matching = Vec::new();
    for meaning in class_matrix::spelling_meanings() {
        let name = format!("{} {}", meaning.family.name(), meaning.text);
        if meaning.reads_x && meaning.matches_x {
            matching.push(name.clone());
        }
        match &meaning.inputs {
            Err(reason) if meaning.reads_x => {
                assert_ne!(*reason, "no other input is stated", "{name}");
                none.entry(reason).or_default().push(name);
            }
            Err(_) => {}
            Ok(inputs) => {
                assert!(meaning.reads_x, "{name} states an input but reads no x");
                let differs = |input: &class_matrix::SecondInput| {
                    let witness_differs =
                        meaning.witness.is_ok() && meaning.witness != input.witness;
                    let value_differs = matches!(
                        (&meaning.value, &input.value),
                        (Meaning::Value(_) | Meaning::Undefined(_), Meaning::Value(_))
                            | (Meaning::Value(_), Meaning::Undefined(_))
                    ) && meaning.value != input.value;
                    witness_differs || value_differs
                };
                assert!(
                    inputs.iter().any(differs),
                    "{name}: at {:?} it matches and denotes what it does at 1",
                    inputs
                        .iter()
                        .map(|input| input.x.to_string())
                        .collect::<Vec<_>>()
                );
                for input in inputs {
                    assert_ne!(input.x, Ground::Int(1), "{name}");
                    if meaning.witness.is_ok() && !meaning.matches_x {
                        assert!(matches!(input.x, Ground::Int(_)), "{name}: {}", input.x);
                    }
                }
            }
        }
    }
    assert_eq!(matching, ["terms x", "terms x | 1"]);
    let listed = none
        .iter()
        .map(|(reason, spellings)| format!("{reason}: {}", spellings.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, AT_ONE_ONLY, "{listed:#?}");
}

/// An operator spelling over `x` and a literal, read from its text: `x OP c`, under a unary
/// operator (`!(x OP c)`, `-(x OP c)`), as a method (`x.add::<Int>(c)`) or as the call the
/// notation denotes (`k::builtin::int::add(x, c)`), with the operator's class and the operators of
/// that class; `None` for every other spelling.
struct OperatorSpelling {
    outer: Option<char>,
    operator: &'static str,
    literal: Operand,
    class: &'static [&'static str],
}

#[derive(Clone, Copy)]
enum Operand {
    Int(i64),
    Bool(bool),
}

/// The binary operators of each class: what a lowering could write for an operator in its place.
/// `/` and `%` stand beside their Euclidean (flooring) readings, `div_euclid` and `rem_euclid`,
/// and `>>` beside a truncating division by its power of two.
const CLASSES: [&[&str]; 5] = [
    &["+", "-", "*", "/", "%", "div_euclid", "rem_euclid"],
    &["&", "|", "^"],
    &["<<", ">>", "/pow2"],
    &["<", "<=", ">", ">=", "==", "!="],
    &["&&", "||"],
];

fn operator_spelling(text: &str) -> Option<OperatorSpelling> {
    let (outer, inner) = match text.as_bytes().first() {
        Some(b'!') => (Some('!'), text.strip_prefix("!(")?.strip_suffix(')')?),
        Some(b'-') => (Some('-'), text.strip_prefix("-(")?.strip_suffix(')')?),
        _ => (None, text),
    };
    let (operator, literal) = if let Some(literal) = inner
        .strip_prefix("x.add::<Int>(")
        .or_else(|| inner.strip_prefix("k::builtin::int::add(x, "))
    {
        ("+", literal.strip_suffix(')')?)
    } else {
        let (operator, literal) = inner.strip_prefix("x ")?.split_once(' ')?;
        (operator, literal)
    };
    let literal = match literal {
        "true" => Operand::Bool(true),
        "false" => Operand::Bool(false),
        _ => Operand::Int(literal.parse().ok()?),
    };
    let class = CLASSES
        .into_iter()
        .find(|class| class.contains(&operator))?;
    let operator = class.iter().copied().find(|other| *other == operator)?;
    Some(OperatorSpelling {
        outer,
        operator,
        literal,
        class,
    })
}

/// What `x OP c`, under `outer`, denotes at `x`, by Rust's `i64` and `bool` operators, which the
/// KRS operator table states each `Int` and `Bool` operator is; `None` where it has no value
/// (`x` not in the operator's domain).
fn operate(outer: Option<char>, operator: &str, x: &Ground, literal: Operand) -> Option<Ground> {
    let value = match (x, literal) {
        (Ground::Int(x), Operand::Int(c)) => {
            let (x, c) = (*x, c);
            match operator {
                "+" => Ground::Int(x + c),
                "-" => Ground::Int(x - c),
                "*" => Ground::Int(x * c),
                "/" => Ground::Int(x / c),
                "%" => Ground::Int(x % c),
                "div_euclid" => Ground::Int(x.div_euclid(c)),
                "rem_euclid" => Ground::Int(x.rem_euclid(c)),
                "&" => Ground::Int(x & c),
                "|" => Ground::Int(x | c),
                "^" => Ground::Int(x ^ c),
                "<<" => Ground::Int(x << c),
                ">>" => Ground::Int(x >> c),
                "/pow2" => Ground::Int(x / (1 << c)),
                "<" => Ground::Bool(x < c),
                "<=" => Ground::Bool(x <= c),
                ">" => Ground::Bool(x > c),
                ">=" => Ground::Bool(x >= c),
                "==" => Ground::Bool(x == c),
                "!=" => Ground::Bool(x != c),
                _ => return None,
            }
        }
        (Ground::Bool(x), Operand::Bool(c)) => match operator {
            "&&" => Ground::Bool(*x && c),
            "||" => Ground::Bool(*x || c),
            _ => return None,
        },
        _ => return None,
    };
    Some(match (outer, value) {
        (Some('!'), Ground::Bool(value)) => Ground::Bool(!value),
        (Some('-'), Ground::Int(value)) => Ground::Int(-value),
        (None, value) => value,
        _ => return None,
    })
}

/// Every operator spelling's inputs (1 and those it states) separate it from every other operator
/// of its class substituted in (a comparison from the other comparisons, an arithmetic operator
/// from the others and `/` and `%` from their Euclidean readings, a bitwise one, a shift and a
/// connective likewise): at some input the two differ, so a lowering that wrote the other operator
/// does not run as stated at every input. The spelling's own meaning is checked against the
/// operator's at each input first, so the test reads the operator it substitutes for.
#[test]
fn every_operator_spelling_differs_from_every_other_operator_of_its_class_on_its_inputs() {
    let mut read = Vec::new();
    for meaning in class_matrix::spelling_meanings() {
        let Some(spelling) = operator_spelling(meaning.text) else {
            continue;
        };
        let name = format!("{} {}", meaning.family.name(), meaning.text);
        read.push(meaning.text);
        let mut inputs = vec![(Ground::Int(1), meaning.value.clone())];
        inputs.extend(
            meaning
                .inputs
                .clone()
                .unwrap_or_default()
                .into_iter()
                .map(|input| (input.x, input.value)),
        );
        for (x, value) in &inputs {
            let expected = operate(spelling.outer, spelling.operator, x, spelling.literal);
            match (value, &expected) {
                (Meaning::Value(value), Some(expected)) => {
                    assert_eq!(value, expected, "{name} at {x}");
                }
                (Meaning::Undefined(_), None) => {}
                _ => panic!("{name} at {x}: {value:?}, where the operator gives {expected:?}"),
            }
        }
        for other in spelling.class {
            if *other == spelling.operator {
                continue;
            }
            assert!(
                inputs.iter().any(|(x, _)| {
                    operate(spelling.outer, spelling.operator, x, spelling.literal)
                        != operate(spelling.outer, other, x, spelling.literal)
                }),
                "{name}: `{other}` in its place agrees with it at every input, {:?}",
                inputs
                    .iter()
                    .map(|(x, _)| x.to_string())
                    .collect::<Vec<_>>()
            );
        }
    }
    assert_eq!(
        read,
        [
            "x + 1",
            "x & 1",
            "x << 1",
            "x / 2",
            "x % 2",
            "x >> 1",
            "x < 1",
            "x == 1",
            "x && true",
            "x || true",
            "!(x < 1)",
            "-(x + 1)",
            "x.add::<Int>(1)",
            "k::builtin::int::add(x, 1)",
            "x | 1",
        ]
    );
}

const AT_ONE_ONLY: &[&str] = &[
    "Size's application has no value at any input: terms Size(x)",
    "a one-element list's size is 1 at every x: notation k::builtin::list::item(x).len() | notation k::builtin::list::size(k::builtin::list::item(x))",
    "its expansion depends on what a program writes at every x: terms Cmd::Dn(x)",
    "the empty map has no entry at any x: notation k::builtin::map::empty()[x] | notation k::builtin::map::get(k::builtin::map::empty(), x)",
    "the empty map holds no key at any x: notation k::builtin::map::empty().contains_key(x) | notation k::builtin::map::in_keys(x, k::builtin::map::empty())",
];

/// The pattern spellings (those with a witness) without a counter-witness, by reason; no pattern
/// spelling may keep the default, `no counter-witness is stated`.
#[test]
fn every_pattern_spelling_states_a_counter_witness_or_why_not() {
    let mut missing = BTreeMap::<String, Vec<String>>::new();
    for meaning in class_matrix::spelling_meanings() {
        if meaning.witness.is_err() {
            continue;
        }
        if let Err(reason) = meaning.counter {
            missing.entry(reason.to_owned()).or_default().push(format!(
                "{} {}",
                meaning.family.name(),
                meaning.text
            ));
        }
    }
    assert!(
        !missing.contains_key("no counter-witness is stated"),
        "{:?}",
        missing.get("no counter-witness is stated")
    );
    let listed = missing
        .iter()
        .map(|(reason, spellings)| format!("{reason}: {}", spellings.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, COUNTERLESS, "{listed:#?}");
}

const COUNTERLESS: &[&str] = &[
    "`_` matches every term: terms _",
    "a binder matches every term where it is the only occurrence of its name: terms x",
    "a program writes no Id but `$x`, through its maker: terms k::id!(\"$x\")",
    "its alternative `x` matches every term where the template does not bind `x`: terms x | 1",
    "its left side `_` matches every term: terms k::rewrite!(_ => 1)",
];

/// Each production of the terms base that a static clause expands (a `Cmd` variant marked
/// `#[k::desugar]` or `#[k::alias]`) is applied by a spelling, so a static production kind the
/// base gains without a spelling is named here. The aliases there for printing (`Ah`, `Am`, `Av`,
/// `Ac`, `Bp`, `Bq`, `Ak`) are the exception: printing reverses them on the states K7 reads back,
/// and no spelling writes them.
#[test]
fn every_static_production_of_the_terms_base_has_a_spelling() {
    const PRINTING: &[&str] = &["Ah", "Am", "Av", "Ac", "Bp", "Bq", "Ak", "An"];
    let base = Base::Terms.preamble();
    let cases = class_matrix::cases();
    // The variants of `Cmd` whose attributes mark them, read from the parsed base, so that a
    // marker's place among the variant's attributes does not matter.
    let file = syn::parse_file(&base).expect("the terms base parses");
    let mut marked = Vec::new();
    for item in &file.items {
        let syn::Item::Enum(family) = item else {
            continue;
        };
        if family.ident != "Cmd" {
            continue;
        }
        for variant in &family.variants {
            for attribute in &variant.attrs {
                let path = attribute.path();
                let segments = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.to_string())
                    .collect::<Vec<_>>();
                let attribute_name = match segments.as_slice() {
                    [facade, name] if facade == "k" && name == "desugar" => "#[k::desugar]",
                    [facade, name] if facade == "k" && name == "alias" => "#[k::alias]",
                    _ => continue,
                };
                marked.push((attribute_name, variant.ident.to_string()));
            }
        }
    }
    assert_eq!(
        marked,
        [
            ("#[k::desugar]", "Dz".to_owned()),
            ("#[k::alias]", "Az".to_owned()),
            ("#[k::alias]", "Ah".to_owned()),
            ("#[k::alias]", "Am".to_owned()),
            ("#[k::alias]", "Av".to_owned()),
            ("#[k::alias]", "Ac".to_owned()),
            ("#[k::alias]", "Bp".to_owned()),
            ("#[k::alias]", "Bq".to_owned()),
            ("#[k::alias]", "Ak".to_owned()),
            ("#[k::alias]", "An".to_owned()),
            ("#[k::desugar]", "Dn".to_owned()),
            ("#[k::desugar]", "Rc".to_owned()),
            ("#[k::desugar]", "Tw".to_owned()),
            ("#[k::desugar]", "Lp".to_owned()),
            ("#[k::desugar]", "Pb".to_owned()),
            ("#[k::desugar]", "Qb".to_owned()),
        ],
        "the terms base's static productions"
    );
    for (marker, name) in marked
        .into_iter()
        .filter(|(_, name)| !PRINTING.contains(&name.as_str()))
    {
        let application = format!("Cmd::{name}(");
        assert!(
            cases.iter().any(
                |case| case.family == Family::Terms && case.construct.starts_with(&application)
            ),
            "the production {name}, marked {marker}, has no spelling"
        );
    }
}

/// What a case's run program is and what the run must end with, for one case of each kind of
/// driver: a matched hole, a built one, a key set up before the command, a condition, an
/// equation applied from a rule, a static clause, and an initializer.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One pinned plan per driver kind, each a few lines."
)]
fn the_drivers_write_their_programs_and_cells() {
    let cases = class_matrix::cases();
    let plan = |id: &str| {
        let case = term_case(&cases, id);
        let (terminal, path) = case.command().map_or_else(
            || ("NAME".to_owned(), "Cmd::NAME".to_owned()),
            |command| (command.terminal(), format!("Cmd::{}", command.name)),
        );
        match &case.k7 {
            K7::Run(run) => (
                run.program.replace(&terminal, "NAME"),
                run.steps,
                run.cells
                    .iter()
                    .map(|(cell, term)| format!("{cell} = {term}").replace(&path, "Cmd::NAME"))
                    .collect::<Vec<_>>()
                    .join(", "),
                run.status,
            ),
            K7::Skip(skip) => panic!("{id}: {skip:?}"),
        }
    };
    let k = |items: &str| format!("k = k[{items}]");
    assert_eq!(
        plan("terms/rule/subject/Cmd::Hold(x)"),
        (
            "NAME(1, hold(1))".to_owned(),
            1,
            k("Cmd::Hold(1)"),
            Status::Liveness
        )
    );
    assert_eq!(
        plan("terms/rule/result/x + 1"),
        ("NAME(1, 0)".to_owned(), 1, k("Cmd::Hold(2)"), Status::Value)
    );
    assert_eq!(
        plan("terms/readable/map-key/x + 1"),
        (
            "then(setenv(mput(mput(memp, 2, 0), 99, 0)), NAME(1, 0))".to_owned(),
            3,
            k(""),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/rule/guard/x < 1"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            k("Cmd::NAME(1, 0)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/equation/result/x + 1"),
        (
            "callk(NAME, 1)".to_owned(),
            1,
            k("Cmd::Hold(Wrap(2))"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/desugar/subject/Cmd::Dz()"),
        (
            "NAME(1, pair(2, 3))".to_owned(),
            0,
            k("Cmd::Hold(1)"),
            Status::Liveness
        )
    );
    assert_eq!(
        plan("terms/sort-rule/result/matches-pattern/x"),
        (
            "NAME(1, 0)".to_owned(),
            1,
            k("Cmd::Hold(true)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/cells/result-map-framed/Cmd::Hold(x)"),
        (
            "then(setenv(mput(mput(memp, 1, 0), 99, 0)), NAME(1, 0))".to_owned(),
            3,
            format!("{}, env = map{{1 -> Cmd::Hold(1), 99 -> 0}}", k("")),
            Status::Value
        )
    );
    // A computed set element is looked up by its value, as a key is (D2).
    assert_eq!(
        plan("terms/rule/subject/set-element/k::builtin::int::add(x, 1)"),
        (
            "NAME(1, sone(2))".to_owned(),
            1,
            k("Cmd::Hold(1)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/readable/set-instance-child/x + 1"),
        (
            "then(then(addtoken(go), addtoken(hold(2))), NAME(1, 0))".to_owned(),
            5,
            k(""),
            Status::Value
        )
    );
    // A set's singleton around the hole is exact: its counter run holds an element more.
    let case = term_case(
        &cases,
        "terms/rule/subject/set-element/k::builtin::int::add(x, 1)",
    );
    let terminal = case
        .command()
        .expect("a rule case has a command")
        .terminal();
    assert_eq!(
        case.k7_counters
            .iter()
            .map(|counter| (counter.program.replace(&terminal, "NAME"), counter.steps))
            .collect::<Vec<_>>(),
        [("NAME(1, sunion(sone(2), sone(99)))".to_owned(), 0)]
    );
    // A condition with no value at x = 1 does not hold: the rule must not apply.
    assert_eq!(
        plan("terms/rule/guard/let-pattern/Cmd::Hold(x)"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            k("Cmd::NAME(1, 0)"),
            Status::Undefined
        )
    );
    // A computed key with no value looks nothing up, though the map holds `x`: the rule must not
    // apply, and the run ends stuck after the setup's two steps, the command in the computation
    // cell.
    assert_eq!(
        plan("notation/cells/map-key/k::builtin::map::empty()[x]"),
        (
            "then(setenv(mput(mput(memp, 1, 0), 99, 0)), NAME(1, 0))".to_owned(),
            2,
            k("Cmd::NAME(1, 0)"),
            Status::Undefined
        )
    );
    // A result with no value at 1: the rule applies, and its next state is undefined (NT-37 D3),
    // so the run ends undefined after the steps before the rule's, none here.
    assert_eq!(
        plan("terms/rule/result/{ let y @ Cmd::Hold(_) = x; y }"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            String::new(),
            Status::UndefinedResult
        )
    );
    assert_eq!(
        plan("terms/rule/result/Size(x)"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            String::new(),
            Status::UndefinedResult
        )
    );
    // A static clause's result is expanded as the program is read: its first state is undefined.
    assert_eq!(
        plan("terms/desugar/result-root/Size(x)"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            String::new(),
            Status::UndefinedResult
        )
    );
    // A simplification's twin: the right side `Kz(HOLE)` at the hole's value, and the left side
    // `Zero(Cmd::NAME(), x)` at each input, each 0 by the definition's equations.
    assert_eq!(
        plan("terms/simplification/result/x + 1"),
        ("callkz(2)".to_owned(), 1, k("Cmd::Hold(0)"), Status::Value)
    );
    assert_eq!(
        plan("terms/simplification/subject/Cmd::Hold(x)"),
        (
            "callz(NAME, hold(1))".to_owned(),
            1,
            k("Cmd::Hold(0)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/simplification/guard/x < 1"),
        (
            "callz(NAME, 1)".to_owned(),
            1,
            k("Cmd::Hold(0)"),
            Status::Value
        )
    );
    // The second input: the plan at x = -2, with the value the spelling denotes there.
    let at_second = |id: &str| {
        let case = term_case(&cases, id);
        let (terminal, path) = case.command().map_or_else(
            || ("NAME".to_owned(), "Cmd::NAME".to_owned()),
            |command| (command.terminal(), format!("Cmd::{}", command.name)),
        );
        case.k7_inputs
            .iter()
            .map(|run| {
                (
                    run.program.replace(&terminal, "NAME"),
                    run.steps,
                    run.cells
                        .iter()
                        .map(|(cell, term)| format!("{cell} = {term}").replace(&path, "Cmd::NAME"))
                        .collect::<Vec<_>>()
                        .join(", "),
                    run.status,
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        at_second("terms/rule/result/x + 1"),
        [(
            "NAME(-2, 0)".to_owned(),
            1,
            k("Cmd::Hold(-1)"),
            Status::Value
        )]
    );
    assert_eq!(
        at_second("terms/readable/map-key/x & 1"),
        [(
            "then(setenv(mput(mput(memp, 0, 0), 99, 0)), NAME(-2, 0))".to_owned(),
            3,
            k(""),
            Status::Value
        )]
    );
    // `x < 1` holds at -2: the rule applies there; at 3 it does not.
    assert_eq!(
        at_second("terms/rule/guard/x < 1"),
        [
            (
                "NAME(-2, 0)".to_owned(),
                1,
                k("Cmd::Hold(-2)"),
                Status::Value
            ),
            (
                "NAME(3, 0)".to_owned(),
                0,
                k("Cmd::NAME(3, 0)"),
                Status::Value
            )
        ]
    );
    assert_eq!(
        at_second("terms/init/variable-item/x + 1"),
        [(
            "go".to_owned(),
            0,
            k("Cmd::Go(), -2, Cmd::Hold(-1)"),
            Status::Value
        )]
    );
    // The construct with no value at 1 has one at its other input, where the case runs too.
    assert_eq!(
        at_second("terms/rule/result/{ let y @ Cmd::Hold(_) = x; y }"),
        [(
            "NAME(hold(-2), 0)".to_owned(),
            1,
            k("Cmd::Hold(Cmd::Hold(-2))"),
            Status::Value
        )]
    );
    // A comparison runs at -2 and at 3, where `<` and `!=` part.
    assert_eq!(
        at_second("terms/rule/result/x < 1")
            .into_iter()
            .map(|(program, _, cells, _)| (program, cells))
            .collect::<Vec<_>>(),
        [
            ("NAME(-2, 0)".to_owned(), k("Cmd::Hold(true)")),
            ("NAME(3, 0)".to_owned(), k("Cmd::Hold(false)")),
        ]
    );
    // A division truncates: -3 / 2 is -1.
    assert_eq!(
        at_second("terms/rule/result/x / 2"),
        [(
            "NAME(-3, 0)".to_owned(),
            1,
            k("Cmd::Hold(-1)"),
            Status::Value
        )]
    );
    // Of two equal keys the later entry is the map's: at 2, `{2 ↦ 3}`.
    assert_eq!(
        at_second("notation/rule/result/map![x -> 1, 2 -> 3]")
            .into_iter()
            .map(|(program, _, cells, _)| (program, cells))
            .collect::<Vec<_>>(),
        [
            (
                "NAME(-2, 0)".to_owned(),
                k("Cmd::Hold(map{-2 -> 1, 2 -> 3})")
            ),
            ("NAME(2, 0)".to_owned(), k("Cmd::Hold(map{2 -> 3})")),
        ]
    );
    // A simplification's result twin evaluates its left side at each input beside the right.
    assert_eq!(
        at_second("terms/simplification/result/x + 1")
            .into_iter()
            .map(|(program, ..)| program)
            .collect::<Vec<_>>(),
        ["callkz(-1)", "callz(NAME, 1)", "callz(NAME, -2)"]
    );
    // A clause's own rule writes the witness at 1 into the source: no second input reaches it.
    assert!(at_second("terms/alias/subject-written/Cmd::Hold(x)").is_empty());
    // A spelling that does not read `x` runs at 1 only.
    assert!(at_second("terms/rule/result/1").is_empty());
    // A counter-witness's run stops before the case's sentence.
    let case = term_case(&cases, "terms/rule/subject/Cmd::Hold(x)");
    let counter = case
        .k7_counters
        .first()
        .expect("Cmd::Hold(x) has a counter-witness");
    let terminal = case
        .command()
        .expect("a rule case has a command")
        .terminal();
    assert_eq!(
        (
            counter.program.replace(&terminal, "NAME"),
            counter.depth,
            counter.steps
        ),
        ("NAME(1, pair(0, 0))".to_owned(), 1, 0)
    );
    assert_eq!(
        plan("terms/init/variable-item/x + 1"),
        (
            "go".to_owned(),
            0,
            k("Cmd::Go(), 1, Cmd::Hold(2)"),
            Status::Value
        )
    );
}

/// A ground term's program and its agreement with what a run shows.
#[test]
fn ground_terms_are_written_and_compared_by_value() {
    let one = Ground::Int(1);
    let map = Ground::map(vec![
        (one.clone(), Ground::Int(2)),
        (one.clone(), Ground::Int(3)),
    ]);
    assert_eq!(map, Ground::Map(vec![(one.clone(), Ground::Int(3))]));
    assert_eq!(map.program().as_deref(), Some("mput(memp, 1, 3)"));
    assert_eq!(map.literal_program(), None);
    let set = Ground::set(vec![one.clone(), one.clone()]);
    assert_eq!(set, Ground::Set(vec![one.clone()]));
    assert_eq!(set.program().as_deref(), Some("sone(1)"));
    let held = Ground::ctor("Cmd::Hold", vec![Ground::Any]);
    assert!(held.agrees(&Ground::ctor("Cmd::Hold", vec![Ground::string("s")])));
    assert!(!held.agrees(&Ground::ctor("Cmd::Go", Vec::new())));
    assert!(Ground::ctor("Cmd::Go", Vec::new()).agrees(&Ground::ctor("pkg::Cmd::Go", Vec::new())));
    assert!(!Ground::ctor("Cmd::Go", Vec::new()).agrees(&Ground::ctor("XCmd::Go", Vec::new())));
    assert_eq!(
        Ground::ctor("Wrap", vec![one.clone()]).program().as_deref(),
        Some("wk(1)")
    );
    assert_eq!(Ground::ctor("Wrap", vec![one]).literal_program(), None);
    assert_eq!(Ground::float(1.5).program().as_deref(), Some("1.5"));
    assert_eq!(
        Ground::Bytes(b"ab".to_vec()).program().as_deref(),
        Some("b\"ab\"")
    );
}

/// Each run family's cases (the readable records and `cells!` rules on the run base) by K7 status,
/// a skip by its kind and reason, with its count, and the subject cases that run a counter-witness
/// or why they do not.
#[test]
fn every_run_cases_k7_status_is_counted() {
    let cases = class_matrix::cases();
    let mut statuses = BTreeMap::<String, usize>::new();
    for case in cases.iter().filter(|case| case.family.twin().is_some()) {
        let family = case.family.name();
        let status = match &case.k7 {
            K7::Run(run) => format!("{family}: runs, {}", run.status.name()),
            K7::Skip(skip) => format!("{family}: {}: {}", skip.kind.name(), skip.reason),
        };
        *statuses.entry(status).or_default() += 1;
        if case.side == Side::Subject && matches!(case.k7, K7::Run(_)) {
            let counter = match class_matrix::run_counterless(case) {
                None => "runs a counter-witness".to_owned(),
                Some(reason) => format!("no counter-witness: {reason}"),
            };
            *statuses.entry(format!("{family}: {counter}")).or_default() += 1;
        }
    }
    let listed = statuses
        .iter()
        .map(|(status, count)| format!("{count} {status}"))
        .collect::<Vec<_>>();
    assert_eq!(listed, RUN_STATUSES, "{listed:#?}");
}

const RUN_STATUSES: &[&str] = &[
    "4 cells-run: no counter-witness: `_` matches every value of the cell",
    "4 cells-run: no counter-witness: a binder matches every value of the cell",
    "1 cells-run: no counter-witness: a group record whose every child is a binder matches every group",
    "1 cells-run: no value: a map literal's rest is the map its entries are written over, and an anonymous `..` names none",
    "76 cells-run: no value: the spelling is no notation of its cell's kind, so it denotes nothing there",
    "3 cells-run: no value: x = 1 is no value of the cell's sort",
    "74 cells-run: no witness: the spelling is no notation of its cell's kind, so it denotes nothing there",
    "14 cells-run: runs a counter-witness",
    "23 cells-run: runs, liveness",
    "24 cells-run: runs, value",
    "4 readable-run: no counter-witness: `..` alone matches every value of the cell",
    "4 readable-run: no counter-witness: `_` matches every value of the cell",
    "4 readable-run: no counter-witness: a binder matches every value of the cell",
    "1 readable-run: no counter-witness: a group record whose every child is a binder matches every group",
    "6 readable-run: no value: `..` in a result is the rest a `..` of the subject's entry matched, and the subject's `old` matches the cell whole",
    "7 readable-run: no value: `_` builds no value",
    "1 readable-run: no value: a map literal's rest is the map its entries are written over, and an anonymous `..` names none",
    "1 readable-run: no value: the result's instance list does not line up with the subject's, which reads the front one",
    "60 readable-run: no value: the spelling is no notation of its cell's kind, so it denotes nothing there",
    "3 readable-run: no value: x = 1 is no value of the cell's sort",
    "2 readable-run: no witness: a cell record as a List cell's element, which no driver command writes: a readable result reads `[Job { .. }, ..]` on a List cell as a collection's instances, which it refuses, and no other spelling builds a cell record",
    "1 readable-run: no witness: a cell record behind the computation's first item, which no driver command writes: a driver command acts at the front of the computation",
    "1 readable-run: no witness: a map literal's rest is the map its entries are written over, and an anonymous `..` names none",
    "63 readable-run: no witness: the spelling is no notation of its cell's kind, so it denotes nothing there",
    "18 readable-run: runs a counter-witness",
    "33 readable-run: runs, liveness",
    "16 readable-run: runs, value",
];

/// The run families' cases K7 does not run for another reason than a spelling in another kind's
/// notation than its cell's, and the subject cases it runs without a counter-witness, by reason:
/// what the drivers cannot run and why ([`every_run_cases_k7_status_is_counted`] counts them).
#[test]
fn every_run_case_without_a_witness_value_or_counter_witness_says_why() {
    let cases = class_matrix::cases();
    let mut missing = BTreeMap::<String, Vec<String>>::new();
    for case in cases.iter().filter(|case| case.family.twin().is_some()) {
        let slot = case
            .id
            .split_once('/')
            .map_or(case.id.as_str(), |(_, slot)| slot);
        let slot = format!("{} {slot}", case.family.name());
        match &case.k7 {
            K7::Skip(skip) if !skip.reason.starts_with("the spelling is no notation") => {
                missing
                    .entry(format!("{}: {}", skip.kind.name(), skip.reason))
                    .or_default()
                    .push(slot);
            }
            K7::Run(_) if case.side == Side::Subject => {
                if let Some(reason) = class_matrix::run_counterless(case) {
                    missing
                        .entry(format!("no counter-witness: {reason}"))
                        .or_default()
                        .push(slot);
                }
            }
            _ => {}
        }
    }
    let listed = missing
        .iter()
        .map(|(reason, slots)| format!("{reason}: {}", slots.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, RUN_UNSTATED, "{listed:#?}");
}

const RUN_UNSTATED: &[&str] = &[
    "no counter-witness: `..` alone matches every value of the cell: readable-run subject/env/{ .. } | readable-run subject/job/[..] | readable-run subject/k/[..] | readable-run subject/stack/[..]",
    "no counter-witness: `_` matches every value of the cell: cells-run subject/env/k::configuration::Cell(_) | cells-run subject/frame/_ | cells-run subject/pc/k::configuration::Cell(_) | cells-run subject/stack/k::configuration::Cell(_) | readable-run subject/env/_ | readable-run subject/frame/_ | readable-run subject/pc/_ | readable-run subject/stack/_",
    "no counter-witness: a binder matches every value of the cell: cells-run subject/env/k::configuration::Cell(x) | cells-run subject/frame/x | cells-run subject/pc/k::configuration::Cell(x) | cells-run subject/stack/k::configuration::Cell(x) | readable-run subject/env/x | readable-run subject/frame/x | readable-run subject/pc/x | readable-run subject/stack/x",
    "no counter-witness: a group record whose every child is a binder matches every group: cells-run subject/frame/k::fragment![crate::Frame { ret: x }] | readable-run subject/frame/Frame { ret: x }",
    "no value: `..` in a result is the rest a `..` of the subject's entry matched, and the subject's `old` matches the cell whole: readable-run result/env/{ .. } | readable-run result/env/{ y -> x, .. } | readable-run result/stack/[.., Job { payload: 0, .. }] | readable-run result/stack/[..] | readable-run result/stack/[Job { payload: x, .. }, ..] | readable-run result/stack/[x, ..]",
    "no value: `_` builds no value: readable-run result/counter/_ | readable-run result/env/_ | readable-run result/frame/_ | readable-run result/job/_ | readable-run result/k/_ | readable-run result/pc/_ | readable-run result/stack/_",
    "no value: a map literal's rest is the map its entries are written over, and an anonymous `..` names none: cells-run result/bag/{ k::fragment![crate::Obj { key: x, m: k::map![x -> y, ..] }], ..instances0 } | readable-run result/bag/{ Obj { key: x, m: map![x -> y, ..] }, .. }",
    "no value: the result's instance list does not line up with the subject's, which reads the front one: readable-run result/job/[.., Job { payload: 0, .. }]",
    "no value: x = 1 is no value of the cell's sort: cells-run result/env/k::configuration::Cell(x) | cells-run result/frame/x | cells-run result/stack/k::configuration::Cell(x) | readable-run result/env/x | readable-run result/frame/x | readable-run result/stack/x",
    "no witness: a cell record as a List cell's element, which no driver command writes: a readable result reads `[Job { .. }, ..]` on a List cell as a collection's instances, which it refuses, and no other spelling builds a cell record: readable-run subject/stack/[.., Job { payload: 0, .. }] | readable-run subject/stack/[Job { payload: x, .. }, ..]",
    "no witness: a cell record behind the computation's first item, which no driver command writes: a driver command acts at the front of the computation: readable-run subject/k/[.., Job { payload: 0, .. }]",
    "no witness: a map literal's rest is the map its entries are written over, and an anonymous `..` names none: readable-run subject/bag/{ Obj { key: 1, m: map![1 -> 2, ..] }, .. }",
];

/// What a run family's case's program is, what the run must end with, and its counter run, for one
/// case of each kind of plan: a subject whose witness a driver command writes, one the start
/// configuration holds, the computation cell's own subject and result, a result over the old value
/// a driver writes first, a map written twice at one key, an absent optional cell, a List
/// collection's and a Set collection's instances.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "One pinned plan per kind of run plan, each a few lines."
)]
fn the_run_drivers_write_their_programs_and_cells() {
    let cases = class_matrix::cases();
    let plans = |id: &str| {
        let case = term_case(&cases, id);
        let terminal = case
            .command()
            .map_or_else(|| "NAME".to_owned(), Command::terminal);
        let run = |run: &krs_test_support::class_matrix::k7::Run| {
            let cells = run
                .cells
                .iter()
                .map(|(cell, term)| format!("{cell} = {term}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "{} in {} of {} steps; {cells}",
                run.program.replace(&terminal, "NAME"),
                run.steps,
                run.depth
            )
        };
        let K7::Run(plan) = &case.k7 else {
            panic!("{id}: {:?}", case.k7);
        };
        (
            run(plan),
            case.k7_counters.iter().map(run).collect::<Vec<_>>(),
        )
    };
    let cases_of = [
        (
            "readable-run/subject/pc/0",
            "then(setpc(0), NAME) in 3 of 3 steps; k = k[]",
            &["then(setpc(1), NAME) in 2 of 3 steps; "][..],
        ),
        (
            "readable-run/subject/pc/x",
            "NAME in 1 of 1 steps; k = k[]",
            &[][..],
        ),
        (
            "readable-run/subject/k/[]",
            "skip in 2 of 2 steps; pc = 1",
            &["go in 0 of 1 steps; "][..],
        ),
        (
            "cells-run/subject/k/k::configuration::KCell(x, ..)",
            "then(go, go) in 2 of 2 steps; pc = 1",
            &["skip in 1 of 2 steps; "][..],
        ),
        (
            "readable-run/result/k/[x, ..]",
            "then(NAME(1, 2), go) in 2 of 2 steps; k = k[1, Cmd::Go()]",
            &[][..],
        ),
        (
            "readable-run/subject/counter/Some(x)",
            "then(setcounter(0), NAME) in 3 of 3 steps; k = k[]",
            &["then(then(setcounter(0), dropcounter), NAME) in 4 of 5 steps; "][..],
        ),
        (
            "readable-run/result/counter/None",
            "then(setcounter(5), NAME(1, 2)) in 3 of 3 steps; k = k[], counter = absent",
            &[][..],
        ),
        (
            "cells-run/result/env/k::configuration::Cell(k::map![x -> 1, y -> 2])",
            "then(setenv(mput(memp, 5, 5)), NAME(1, 1)) in 3 of 3 steps; k = k[], env = map{1 -> 2}",
            &[][..],
        ),
        (
            "cells-run/result/job/[k::fragment![crate::Job { payload: x, ..old }], ..instances0]",
            "then(then(addjob(6), addjob(5)), NAME(1, 2)) in 5 of 5 steps; k = k[], queue.job[payload] = [job(1), job(6)]",
            &[][..],
        ),
        (
            "readable-run/subject/bag/{ Obj { key: 1, m: map![1 -> 2] }, .. }",
            "then(then(addobj(9, memp), addobj(1, mput(memp, 1, 2))), NAME) in 5 of 5 steps; k = k[]",
            &[
                "then(then(addobj(9, memp), addobj(1, mput(mput(memp, 1, 2), 3, 4))), NAME) in 4 of 5 steps; ",
            ][..],
        ),
        (
            "cells-run/subject/bag/{ k::fragment![crate::Obj { key: k::builtin::int::add(0, 1), m: k::map![1 -> 2] }], instances0 @ .. }",
            "then(then(addobj(9, memp), addobj(1, mput(memp, 1, 2))), NAME) in 5 of 5 steps; k = k[]",
            &[
                "then(then(addobj(9, memp), addobj(2, mput(memp, 1, 2))), NAME) in 4 of 5 steps; ",
                "then(then(addobj(9, memp), addobj(1, mput(mput(memp, 1, 2), 3, 4))), NAME) in 4 of 5 steps; ",
            ][..],
        ),
        (
            "readable-run/subject/bag/{ Obj { key: 1, .. }, .. }",
            "then(then(addobj(9, memp), addobj(1, mput(memp, 1, 2))), NAME) in 5 of 5 steps; k = k[]",
            &["then(then(addobj(9, memp), addobj(2, mput(memp, 1, 2))), NAME) in 4 of 5 steps; "][..],
        ),
        (
            "readable-run/subject/env/{ y -> x, .. }",
            "then(setenv(mput(mput(memp, 1, 0), 2, 0)), NAME) in 3 of 3 steps; k = k[]",
            &["then(setenv(memp), NAME) in 2 of 3 steps; "][..],
        ),
        (
            "readable-run/subject/k/[Job { payload: x, .. }, ..]",
            "then(pushjob(0), go) in 3 of 3 steps; pc = 1",
            &["go in 0 of 1 steps; "][..],
        ),
        (
            "cells-run/result/bag/{ k::fragment![crate::Obj { key: x, m: k::map![x -> k::builtin::int::add(y, 1)] }], ..instances0 }",
            "then(addobj(5, mput(memp, 5, 5)), NAME(1, 2)) in 3 of 3 steps; k = k[], shelf.bag{key,m} = set{bag(1, map{1 -> 3}), bag(5, map{5 -> 5})}",
            &[][..],
        ),
    ];
    for (id, plan, counter) in cases_of {
        assert_eq!(
            plans(id),
            (
                plan.to_owned(),
                counter
                    .iter()
                    .map(|counter| (*counter).to_owned())
                    .collect::<Vec<_>>()
            ),
            "{id}"
        );
    }
}

/// Exact and open, the rule of the run families' plans: a subject spelling that reads a
/// collection whole (`[]`, the map of `Obj { key: 1, m: map![1 -> 2] }`) has a counter-witness
/// with one item more than it writes, and one whose `..` leaves items open (`[x, ..]`,
/// `{ y -> x, .. }`, the instances beside `{ Obj { .. }, .. }`, the map of `Obj { key: 1, .. }`)
/// has a witness with more items than it writes, so a lowering that reads an exact collection as
/// open, or an open one as exact, is caught. Checked on the items each driver program writes;
/// the subject cases that read no collection say why.
#[test]
fn every_run_spelling_reads_its_collections_by_the_rule() {
    let cases = class_matrix::cases();
    let mut unread = BTreeMap::<String, usize>::new();
    let mut read = BTreeMap::<String, usize>::new();
    for case in cases.iter().filter(|case| {
        case.family.twin().is_some() && case.side == Side::Subject && matches!(case.k7, K7::Run(_))
    }) {
        let readings = class_matrix::run_readings(case)
            .unwrap_or_else(|| panic!("{} runs and states no reading", case.id));
        match readings {
            Err(reason) => *unread.entry(reason.to_owned()).or_default() += 1,
            Ok(readings) => {
                assert!(!readings.is_empty(), "{} reads nothing", case.id);
                for reading in readings {
                    match reading.extent {
                        Extent::Exact(written) => {
                            assert_eq!(reading.witness, written, "{}: {reading:?}", case.id);
                            assert!(
                                reading.counters.contains(&(written + 1)),
                                "{}: no counter-witness has an item more: {reading:?}",
                                case.id
                            );
                        }
                        Extent::Open(written) => assert!(
                            reading.witness > written,
                            "{}: the witness has no item more: {reading:?}",
                            case.id
                        ),
                    }
                    *read
                        .entry(format!("{:?} {:?}", reading.part, reading.extent))
                        .or_default() += 1;
                }
            }
        }
    }
    let listed = |counts: BTreeMap<String, usize>| {
        counts
            .into_iter()
            .map(|(what, count)| format!("{count} {what}"))
            .collect::<Vec<_>>()
    };
    let read = listed(read);
    assert_eq!(read, RUN_READS, "{read:#?}");
    let unread = listed(unread);
    assert_eq!(unread, RUN_UNREAD, "{unread:#?}");
}

const RUN_UNREAD: &[&str] = &[
    "8 `_` matches every value of the cell",
    "8 a binder matches every value of the cell",
    "2 a leaf holds one value, no collection",
    "4 an optional cell holds one value or none, no collection",
    "2 the group has one child, which the record names: no child is left over",
];

const RUN_READS: &[&str] = &[
    "2 Computation Exact(0)",
    "1 Computation Open(0)",
    "3 Computation Open(1)",
    "1 Jobs Exact(0)",
    "1 Jobs Open(0)",
    "3 Jobs Open(1)",
    "1 List Exact(0)",
    "1 List Open(0)",
    "2 List Open(1)",
    "1 Map Open(0)",
    "2 Map Open(1)",
    "8 ObjectMap Exact(1)",
    "2 ObjectMap Open(0)",
    "2 ObjectMap Open(1)",
    "12 Objects Open(1)",
];

/// The rule on the term family's spellings: an exact collection a spelling matches (a set's
/// singleton, the empty map and set) has a counter-witness with an item more, and an open one
/// (`[x, ..]`) a witness with an item more than it writes; an open record (`Cmd::Pair { a: x, .. }`)
/// has a witness whose field the record leaves holds a value. Every spelling whose witness or
/// counter-witness is a collection is listed. The slots' own collections (a map read's `..`, a
/// list's, a collection's instances, a set's singleton around the hole) are pinned in
/// `the_drivers_write_their_programs_and_cells`.
#[test]
fn every_term_collection_spelling_follows_the_rule() {
    // (spelling, open, the items it writes)
    const COLLECTIONS: &[(&str, bool, usize)] = &[
        ("[x, ..]", true, 1),
        ("k::builtin::map::empty()", false, 0),
        ("k::builtin::set::empty()", false, 0),
        ("k::builtin::set::item(x)", false, 1),
        ("map![]", false, 0),
        ("set![]", false, 0),
        ("set![x]", false, 1),
    ];
    let size = |term: &Ground| match term {
        Ground::List(items) | Ground::Set(items) => Some(items.len()),
        Ground::Map(entries) => Some(entries.len()),
        _ => None,
    };
    let mut seen = BTreeSet::new();
    for meaning in class_matrix::spelling_meanings() {
        let witness = meaning.witness.as_ref().ok().and_then(size);
        let counters = meaning
            .counter
            .as_ref()
            .map(|counters| counters.iter().filter_map(size).collect::<Vec<_>>())
            .unwrap_or_default();
        if witness.is_none() && counters.is_empty() {
            continue;
        }
        let (_, open, written) = COLLECTIONS
            .iter()
            .find(|(text, ..)| *text == meaning.text)
            .unwrap_or_else(|| {
                panic!(
                    "{} matches a collection the rule does not list",
                    meaning.text
                )
            });
        seen.insert(meaning.text);
        if *open {
            assert!(witness > Some(*written), "{}: {witness:?}", meaning.text);
        } else {
            assert_eq!(witness, Some(*written), "{}", meaning.text);
            assert!(
                counters.contains(&(written + 1)),
                "{}: {counters:?}",
                meaning.text
            );
        }
    }
    assert_eq!(seen.len(), COLLECTIONS.len());
    let record = class_matrix::spelling_meanings()
        .into_iter()
        .find(|meaning| meaning.text == "Cmd::Pair { a: x, .. }")
        .expect("the open record is a spelling");
    assert_eq!(
        record.witness,
        Ok(Ground::ctor(
            "Cmd::Pair",
            vec![Ground::Int(1), Ground::Int(0)]
        ))
    );
}

/// The twin check's pairs ([`class_matrix::twins`]): every case at a desugar's or an alias's
/// result has its twin at a `#[k::rule]` fn's result, the same construct at the same openings,
/// and both have the twin check's runs ([`class_matrix::twin_runs`]) on every witness the static
/// case binds, whatever K7's plans state: the check compares the pairs no plan runs too, by how
/// their runs end. The runs' programs are pinned for one pair of each form.
#[test]
fn every_static_result_has_a_rule_twin_with_runs_on_each_witness() {
    let cases = class_matrix::cases();
    let twins = class_matrix::twins(&cases);
    let paired = twins
        .iter()
        .map(|(case, _)| case.id.as_str())
        .collect::<BTreeSet<_>>();
    let unpaired = cases
        .iter()
        .filter(|case| {
            case.term.as_ref().is_some_and(|term| {
                term.position.slot == class_matrix::positions::Slot::Result
                    && matches!(
                        term.position.form,
                        class_matrix::positions::Form::Alias
                            | class_matrix::positions::Form::Desugar
                    )
            }) && !paired.contains(case.id.as_str())
        })
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert_eq!(unpaired, Vec::<&str>::new());
    assert_eq!(twins.len(), 329);
    for (case, twin) in &twins {
        let witnesses = |case: &Case| {
            class_matrix::twin_runs(case)
                .into_iter()
                .map(|(witness, _)| witness)
                .collect::<Vec<_>>()
        };
        let (own, rule) = (witnesses(case), witnesses(twin));
        assert!(
            !own.is_empty() && own.iter().all(|witness| rule.contains(witness)),
            "{}: {own:?}, its twin {}: {rule:?}",
            case.id,
            twin.id
        );
    }
    let programs = |id: &str| {
        class_matrix::twin_runs(&term_case(&cases, id))
            .into_iter()
            .map(|(witness, run)| format!("{witness}: {} ({} steps)", run.program, run.steps))
            .collect::<Vec<_>>()
    };
    let rule = term_case(&cases, "terms/rule/result/x");
    let name = rule
        .command()
        .expect("a rule case has a command")
        .terminal();
    assert_eq!(
        programs("terms/rule/result/x"),
        [
            format!("1: {name}(1, 0) (1 steps)"),
            format!("go: {name}(go, 0) (1 steps)")
        ]
    );
    let alias = term_case(&cases, "terms/alias/result/x");
    let name = alias
        .command()
        .expect("an alias case has a command")
        .terminal();
    assert_eq!(
        programs("terms/alias/result/x"),
        [
            format!("1: {name}(1) (0 steps)"),
            format!("go: {name}(go) (0 steps)")
        ]
    );
    let ground = term_case(&cases, "terms/alias/result-root-ground/1");
    let name = ground
        .command()
        .expect("an alias case has a command")
        .terminal();
    assert_eq!(
        programs("terms/alias/result-root-ground/1"),
        [format!("1: {name} (0 steps)")]
    );
}

/// K7's dependency check runs an attribute case's plans on the case without its attribute: that
/// case has the same ID, command and plans, its own source lacks the attribute as written (a
/// production's key leaves the command's marker), and only the attribute's text differs.
#[test]
fn every_attribute_case_without_its_attribute_writes_no_attribute() {
    let mut cases = 0;
    for case in class_matrix::cases() {
        let Some(pair) = case.attribute else {
            continue;
        };
        let without = class_matrix::without_attribute(&case)
            .unwrap_or_else(|| panic!("{}: no case without its attribute", case.id));
        assert_eq!(without.id, case.id);
        assert_eq!(without.k7, case.k7, "{}", case.id);
        assert_eq!(without.k7_counters, case.k7_counters, "{}", case.id);
        assert_eq!(without.removed(), case.removed(), "{}", case.id);
        assert_eq!(
            without.command().map(|command| &command.name),
            case.command().map(|command| &command.name),
            "{}",
            case.id
        );
        let (own, bare) = (case.own_source(), without.own_source());
        assert_ne!(own, bare, "{}: the attribute is not removed", case.id);
        let text = pair.written().text().replace("TAG", &case.tag());
        let written = match pair.written() {
            class_matrix::attributes::Written::Production(key) => key.to_owned(),
            _ => text,
        };
        assert_eq!(
            own.matches(&written).count(),
            bare.matches(&written).count() + 1,
            "{}: `{written}` is not what is removed:\n{own}\n--\n{bare}",
            case.id
        );
        for empty in ["()]", "(, ", ", )"] {
            assert!(
                own.contains(empty) || !bare.contains(empty),
                "{}: an empty key left in `{bare}`",
                case.id
            );
        }
        cases += 1;
    }
    assert!(cases > 0);
}

/// A run whose plan states that its sentence does not apply changes nothing without the
/// sentence, so K7's dependency check shows nothing of it: each names a case at its slot (in its
/// own family, or another family's at the same position) whose sentence applies, which the
/// check judges.
#[test]
fn every_unapplied_run_names_a_case_at_its_slot_that_applies() {
    let cases = class_matrix::cases();
    let mut unapplied = 0;
    let mut missing = Vec::new();
    for case in &cases {
        let K7::Run(plan) = &case.k7 else {
            continue;
        };
        if plan.applies || case.attribute.is_some() {
            continue;
        }
        unapplied += 1;
        match class_matrix::applied_sibling(&cases, case) {
            Some(sibling) => assert_eq!(sibling.removed(), Removed::Changes, "{}", case.id),
            None => missing.push(case.id.clone()),
        }
    }
    assert!(unapplied > 0);
    assert!(
        missing.is_empty(),
        "unapplied runs with no applied case at their slot: {missing:#?}"
    );
}

/// A static clause's result case whose plan states only that the computation ends with one item
/// changes nothing without the clause ([`class_matrix::BUILT_UNSTATED`]), so K7's dependency
/// check shows nothing of it: each has a rule twin, which the twin check compares the term it
/// builds with, and the twin's own run takes the rule's step, which the check judges as changed.
/// No other case is stated so, and every other static clause's result run is judged as changed.
#[test]
fn every_static_result_that_states_one_item_only_has_a_rule_twin_that_takes_a_step() {
    let cases = class_matrix::cases();
    let twins = class_matrix::twins(&cases);
    let mut stated = BTreeSet::new();
    for (case, twin) in &twins {
        let K7::Run(run) = &case.k7 else {
            continue;
        };
        if case.removed() != Removed::Unchanged(class_matrix::BUILT_UNSTATED) {
            assert_eq!(case.removed(), Removed::Changes, "{}", case.id);
            continue;
        }
        stated.insert(case.id.as_str());
        assert_eq!(run.steps, 0, "{}", case.id);
        assert_eq!(twin.removed(), Removed::Changes, "{}", twin.id);
        assert!(
            matches!(&twin.k7, K7::Run(run) if run.steps > 0 && run.applies),
            "{}: its rule twin {} takes no step",
            case.id,
            twin.id
        );
    }
    assert!(stated.contains("terms/desugar/result-root/k::fragment![crate::Frame { ret: 1 }]"));
    let elsewhere = cases
        .iter()
        .filter(|case| case.removed() == Removed::Unchanged(class_matrix::BUILT_UNSTATED))
        .filter(|case| !stated.contains(case.id.as_str()))
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert!(
        elsewhere.is_empty(),
        "stated with no rule twin: {elsewhere:#?}"
    );
}
