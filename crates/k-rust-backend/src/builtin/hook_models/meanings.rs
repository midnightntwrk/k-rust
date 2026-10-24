//! The written meanings of the hooks (`confluence/hooks.rs`) against the builtins themselves.
//!
//! Each written meaning is a set of equations at a hooked symbol that the critical-pair check
//! reads as true, so each must be an identity of the builtin: on every tuple of argument values
//! where the builtin takes a step, each entry whose left-hand side matches and whose `requires`
//! holds has a right-hand side that evaluates to the builtin's result (`\bottom` included), and
//! some entry applies (coverage). The left-hand side is evaluated by the builtin
//! (`evaluate_in_definition`) and the right-hand side by the backend, in FUN's prelude
//! (`tests/fixtures/fun-prelude-hooked-equations.kore`), which declares every hook the table
//! names. The argument values reach the builtins' edges (empty and multibyte strings, integers
//! beyond 64 bits, zero divisors, negative and huge indices and lengths).
//!
//! Coverage is also checked on applications that are not ground: wherever the builtin takes a
//! step on them (`BOOL.and(X, false)`, `KEQUAL.ite(true, X, Y)`, `INT.ne(X, X)`), some entry applies
//! and gives the builtin's result.

use std::collections::BTreeSet;

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    builtin::{BuiltinResult, evaluate_in_definition},
    confluence::hooks::{self, HookSymbols, Meaning},
    definition::BackendDefinition,
    rule::{Predicate, RewriteRule, RuleRhs},
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{Term, TermKind},
};

const FUN_PRELUDE: &str = include_str!("../../../tests/fixtures/fun-prelude-hooked-equations.kore");

fn prelude() -> BackendDefinition {
    let syntax = parse_definition(FUN_PRELUDE).expect("the fixture parses");
    BackendDefinition::internalize(&syntax, "FUN-UNTYPED").expect("the fixture internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

/// An argument value of the tests.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Val {
    Bool(bool),
    Int(i128),
    Str(String),
    /// A `K` sequence: one injected integer item, or the empty sequence (`None`).
    K(Option<i64>),
    Set(BTreeSet<i64>),
}

/// The KORE string literal of `text`: printable ASCII as written (with `"` and `\\` escaped),
/// every other code point as a `\\u`/`\\U` escape.
fn string_literal(text: &str) -> String {
    let mut literal = String::new();
    for character in text.chars() {
        match character {
            '"' => literal.push_str("\\\""),
            '\\' => literal.push_str("\\\\"),
            ' '..='~' => literal.push(character),
            _ if u32::from(character) <= 0xffff => {
                literal.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            _ => literal.push_str(&format!("\\U{:08x}", u32::from(character))),
        }
    }
    literal
}

impl Val {
    fn kore(&self) -> String {
        let int = |value: i128| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        match self {
            Self::Bool(value) => format!(r#"\dv{{SortBool{{}}}}("{value}")"#),
            Self::Int(value) => int(*value),
            Self::Str(value) => format!(r#"\dv{{SortString{{}}}}("{}")"#, string_literal(value)),
            Self::K(None) => "dotk{}()".into(),
            Self::K(Some(value)) => format!(
                "kseq{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}), dotk{{}}())",
                int(i128::from(*value))
            ),
            Self::Set(elements) => elements
                .iter()
                .fold("Lbl'Stop'Set{}()".into(), |set, value| {
                    format!(
                        "Lbl'Unds'Set'Unds'{{}}({set}, LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({})))",
                        int(i128::from(*value))
                    )
                }),
        }
    }
}

/// The argument values a hook's tests draw from, each a list of choices per argument, reaching
/// the builtins' edges: empty and multibyte strings (code-point indices), patterns that overlap
/// themselves, integers beyond 64 bits, zero divisors, negative and huge indices and lengths.
fn domains(hook: &str) -> Vec<Vec<Val>> {
    let bools = || vec![Val::Bool(false), Val::Bool(true)];
    let ints = |values: &[i128]| values.iter().copied().map(Val::Int).collect::<Vec<_>>();
    let wide = || {
        ints(&[
            0,
            1,
            -1,
            2,
            -3,
            7,
            -8,
            i128::from(i64::MAX),
            i128::from(i64::MIN),
            1 << 70,
            -(1 << 70) - 1,
        ])
    };
    let strings = || {
        [
            "",
            "a",
            "b",
            "aa",
            "aaa",
            "ab",
            "aba",
            "abab",
            "é",
            "aé",
            "éa",
            "éé",
            "日本",
            "a日a",
            "日a日",
            "\u{1F600}a",
            "a\u{1F600}",
        ]
        .iter()
        .map(|text| Val::Str((*text).into()))
        .collect::<Vec<_>>()
    };
    let patterns = || {
        ["", "a", "aa", "é", "日", "\u{1F600}", "ab"]
            .iter()
            .map(|text| Val::Str((*text).into()))
            .collect::<Vec<_>>()
    };
    let ks = || {
        vec![
            Val::K(None),
            Val::K(Some(0)),
            Val::K(Some(1)),
            Val::K(Some(2)),
        ]
    };
    let sets = || {
        (0..8)
            .map(|bits: i64| Val::Set((0..3).filter(|bit| bits >> bit & 1 == 1).collect()))
            .collect::<Vec<_>>()
    };
    match hook {
        "BOOL.not" => vec![bools()],
        "KEQUAL.ite" => vec![bools(), ks(), ks()],
        "KEQUAL.ne" => vec![ks(), ks()],
        "INT.ne" | "INT.min" | "INT.ediv" => vec![wide(), wide()],
        "INT.bitRange" | "INT.signExtendBitRange" => vec![
            ints(&[
                0,
                5,
                -5,
                255,
                -256,
                i128::from(i64::MIN),
                (1 << 70) + 3,
                -(1 << 70),
            ]),
            ints(&[0, 1, 3, -1, 64, 80]),
            ints(&[0, 1, 4, 8, -1, 65, 1 << 40]),
        ],
        "STRING.ne" | "STRING.le" | "STRING.gt" | "STRING.ge" => vec![strings(), strings()],
        "STRING.countAllOccurrences" => vec![strings(), patterns()],
        "STRING.replaceAll" => vec![
            strings(),
            patterns(),
            vec![
                Val::Str(String::new()),
                Val::Str("c".into()),
                Val::Str("é日".into()),
            ],
        ],
        "SET.union" => vec![sets(), sets()],
        _ => vec![bools(), bools()],
    }
}

/// The symbol carrying `hook` in the prelude, applied to fresh variables (at `SortK` for the
/// sort parameter of `KEQUAL.ite`), as KORE: the left-hand side the written meaning is built at.
fn application(definition: &BackendDefinition, hook: &str, arguments: &[String]) -> String {
    let symbol = definition
        .symbols()
        .values()
        .find(|symbol| symbol.attributes.hook.as_deref() == Some(hook))
        .unwrap_or_else(|| panic!("the prelude declares no symbol hooked {hook}"));
    let sort_arguments = if symbol.sort_variables.is_empty() {
        String::new()
    } else {
        "SortK{}".into()
    };
    format!(
        "{}{{{sort_arguments}}}({})",
        symbol.name,
        arguments.join(", ")
    )
}

/// The prelude's sort of each argument of `hook`, for fresh variables.
fn argument_sorts(hook: &str) -> Vec<&'static str> {
    match hook {
        "BOOL.not" => vec!["SortBool"],
        "KEQUAL.ite" => vec!["SortBool", "SortK", "SortK"],
        "KEQUAL.ne" => vec!["SortK", "SortK"],
        "INT.ne" | "INT.min" | "INT.ediv" => vec!["SortInt", "SortInt"],
        "INT.bitRange" | "INT.signExtendBitRange" => vec!["SortInt", "SortInt", "SortInt"],
        "STRING.replaceAll" => vec!["SortString", "SortString", "SortString"],
        "SET.union" => vec!["SortSet", "SortSet"],
        hook if hook.starts_with("STRING.") => vec!["SortString", "SortString"],
        _ => vec!["SortBool", "SortBool"],
    }
}

/// The written meaning of `hook`, built at the prelude's symbol.
fn written(definition: &BackendDefinition, hook: &str) -> Vec<std::sync::Arc<RewriteRule>> {
    let variables = argument_sorts(hook)
        .iter()
        .enumerate()
        .map(|(index, sort)| format!("Z{index}:{sort}{{}}"))
        .collect::<Vec<_>>();
    let lhs = term(definition, &application(definition, hook, &variables));
    match hooks::meaning(&HookSymbols::of(definition), hook, &lhs) {
        Meaning::Built(rules) => rules,
        Meaning::Unwritten => panic!("{hook} has no written meaning"),
        Meaning::Unbuildable => panic!("{hook}'s written meaning cannot be built in the prelude"),
    }
}

/// The valuation under which `pattern`, a left-hand side whose arguments are variables or domain
/// values, matches `subject`.
fn matched(pattern: &Term, subject: &Term) -> Option<Substitution> {
    let (
        TermKind::Application {
            symbol, arguments, ..
        },
        TermKind::Application {
            symbol: other,
            arguments: values,
            ..
        },
    ) = (pattern.kind(), subject.kind())
    else {
        return None;
    };
    if symbol.name != other.name || arguments.len() != values.len() {
        return None;
    }
    let mut valuation = Substitution::new();
    for (argument, value) in arguments.iter().zip(values) {
        match argument.kind() {
            TermKind::Variable(variable) => {
                if valuation
                    .insert(variable.clone(), value.clone())
                    .is_some_and(|bound| bound != *value)
                {
                    return None;
                }
            }
            _ if argument == value => {}
            _ => return None,
        }
    }
    Some(valuation)
}

/// Whether the `requires` of `rule` holds under `valuation`: `Some(true)` or `Some(false)` when
/// the simplifier decides it, `None` when it does not.
fn holds(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    valuation: &Substitution,
) -> Option<bool> {
    let requires = rule
        .requires
        .instantiate(valuation)
        .with_definedness(definition, &[])
        .ok()?;
    if requires.is_empty() {
        return Some(true);
    }
    match simplify_predicate_with_solver(
        definition,
        &Predicate::And(requires.into()),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    ) {
        Ok(Ok(Predicate::True)) => Some(true),
        Ok(Ok(Predicate::False)) => Some(false),
        _ => None,
    }
}

/// The value `term` evaluates to, `None` for `\bottom`; `Err` when it does not evaluate to one.
fn evaluated(definition: &BackendDefinition, term: &Term) -> Result<Option<Term>, String> {
    match simplify(definition, term, SimplificationOptions::default()) {
        Ok(Ok(result)) => {
            if result.undefined_term.is_some()
                || result
                    .conjoined()
                    .any(|predicate| *predicate == Predicate::False)
            {
                Ok(None)
            } else if result.constraints().is_empty() {
                Ok(Some(result.term))
            } else {
                Err(format!("{term:?} evaluates under constraints"))
            }
        }
        _ => Err(format!("{term:?} does not evaluate")),
    }
}

/// The failures of `hook`'s written meaning on every tuple of its domains, judged by the
/// builtin itself: on a tuple where the builtin takes a step (a value, or `\\bottom`), each entry
/// whose left-hand side matches and whose `requires` holds must evaluate to that result, and some
/// entry must apply; a `requires` the simplifier does not decide on ground arguments is a failure.
/// A tuple where the builtin takes no step (`Unspecified`, a result beyond a size bound) has no
/// peak to cover.
fn failures(definition: &BackendDefinition, hook: &str) -> (usize, Vec<String>) {
    let rules = written(definition, hook);
    let mut tuples = vec![Vec::<Val>::new()];
    for choices in domains(hook) {
        tuples = tuples
            .into_iter()
            .flat_map(|tuple| {
                choices.iter().map(move |choice| {
                    let mut extended = tuple.clone();
                    extended.push(choice.clone());
                    extended
                })
            })
            .collect();
    }
    let (mut checked, mut failures) = (0, Vec::new());
    for tuple in tuples {
        let kore = tuple.iter().map(Val::kore).collect::<Vec<_>>();
        let subject = term(definition, &application(definition, hook, &kore));
        let expected = match evaluate_in_definition(&subject, definition) {
            Ok(Ok(BuiltinResult::Value(value))) => Some(
                evaluated(definition, &value)
                    .expect("a builtin value evaluates")
                    .expect("a builtin value is defined"),
            ),
            Ok(Ok(BuiltinResult::Bottom)) => None,
            Ok(_) => continue,
            Err(stop) => {
                stop.into_cause();
                continue;
            }
        };
        let mut applied = false;
        for rule in &rules {
            let Some(valuation) = matched(&rule.lhs, &subject) else {
                continue;
            };
            match holds(definition, rule, &valuation) {
                Some(true) => {}
                Some(false) => continue,
                None => {
                    failures.push(format!(
                        "{hook} {tuple:?}: the requires of {} is undecided",
                        label(rule)
                    ));
                    continue;
                }
            }
            applied = true;
            checked += 1;
            let RuleRhs::Term(rhs) = &rule.rhs else {
                unreachable!("a written meaning's right-hand side is a term")
            };
            match evaluated(definition, &substitute(rhs, &valuation)) {
                Ok(found) if found == expected => {}
                // A right-hand side the backend leaves with an unevaluated hooked application (a
                // result beyond a size bound: `1 <<Int 2^40`) decides nothing here; such a pair
                // only fails to join.
                Ok(Some(found)) if unevaluated(&found) => {}
                Ok(found) => failures.push(format!(
                    "{hook} {tuple:?}: {} gives {found:?}, the builtin {expected:?}",
                    label(rule)
                )),
                Err(error) => failures.push(format!("{hook} {tuple:?}: {} {error}", label(rule))),
            }
        }
        if !applied {
            failures.push(format!("{hook} {tuple:?}: no entry applies"));
        }
    }
    (checked, failures)
}

/// Whether `term` holds an application of a hooked function the backend left unevaluated.
fn unevaluated(term: &Term) -> bool {
    let mut found = false;
    term.visit_symbols(&mut |symbol| {
        found |= symbol.attributes.hook.is_some() && symbol.attributes.collection.is_none();
    });
    found
}

fn label(rule: &RewriteRule) -> String {
    rule.attributes.label.clone().unwrap_or_default()
}

macro_rules! meaning_test {
    ($test:ident, $hook:literal) => {
        #[test]
        fn $test() {
            let definition = prelude();
            let (checked, failures) = failures(&definition, $hook);
            assert!(checked > 0, "no instance of {} checked", $hook);
            assert!(failures.is_empty(), "{}", failures.join("\n"));
        }
    };
}

meaning_test!(the_meaning_of_bool_not_is_negation, "BOOL.not");
meaning_test!(the_meaning_of_bool_and_is_conjunction, "BOOL.and");
meaning_test!(the_meaning_of_bool_and_then_is_conjunction, "BOOL.andThen");
meaning_test!(the_meaning_of_bool_or_is_disjunction, "BOOL.or");
meaning_test!(the_meaning_of_bool_or_else_is_disjunction, "BOOL.orElse");
meaning_test!(the_meaning_of_bool_xor_is_exclusive_or, "BOOL.xor");
meaning_test!(the_meaning_of_bool_ne_is_exclusive_or, "BOOL.ne");
meaning_test!(the_meaning_of_bool_implies_is_implication, "BOOL.implies");
meaning_test!(the_meaning_of_kequal_ite_is_selection, "KEQUAL.ite");
meaning_test!(
    the_meaning_of_kequal_ne_is_the_complement_of_eq,
    "KEQUAL.ne"
);
meaning_test!(the_meaning_of_int_ne_is_the_complement_of_eq, "INT.ne");
meaning_test!(the_meaning_of_int_min_is_the_minimum, "INT.min");
meaning_test!(
    the_meaning_of_int_ediv_is_the_euclidean_quotient,
    "INT.ediv"
);
meaning_test!(
    the_meaning_of_int_bit_range_is_the_unsigned_bits,
    "INT.bitRange"
);
meaning_test!(
    the_meaning_of_int_sign_extend_bit_range_is_the_signed_bits,
    "INT.signExtendBitRange"
);
meaning_test!(
    the_meaning_of_string_ne_is_the_complement_of_eq,
    "STRING.ne"
);
meaning_test!(the_meaning_of_string_le_is_the_order, "STRING.le");
meaning_test!(the_meaning_of_string_gt_is_the_order, "STRING.gt");
meaning_test!(the_meaning_of_string_ge_is_the_order, "STRING.ge");
meaning_test!(
    the_meaning_of_string_count_all_occurrences_counts_from_the_left,
    "STRING.countAllOccurrences"
);
meaning_test!(
    the_meaning_of_string_replace_all_replaces_each_occurrence,
    "STRING.replaceAll"
);
meaning_test!(the_meaning_of_set_union_is_union, "SET.union");

/// Every hook of the table has a property test above.
#[test]
fn every_written_meaning_has_its_property_test() {
    let source = include_str!("meanings.rs");
    for hook in hooks::WRITTEN {
        assert!(
            source.contains(&format!("\"{hook}\");"))
                || source.contains(&format!("\"{hook}\"\n);")),
            "{hook} has no meaning_test"
        );
    }
}

/// Coverage off the ground: where the builtin takes a step on an application with variables,
/// some entry applies with its `requires` true and gives the builtin's result.
#[test]
fn every_builtin_step_on_variables_is_an_instance_of_a_written_meaning() {
    let definition = prelude();
    let cases: [(&str, [&str; 3]); 12] = [
        (
            "BOOL.and",
            [r#"\dv{SortBool{}}("false")"#, "B:SortBool{}", ""],
        ),
        (
            "BOOL.and",
            ["B:SortBool{}", r#"\dv{SortBool{}}("false")"#, ""],
        ),
        (
            "BOOL.andThen",
            ["B:SortBool{}", r#"\dv{SortBool{}}("false")"#, ""],
        ),
        (
            "BOOL.or",
            [r#"\dv{SortBool{}}("true")"#, "B:SortBool{}", ""],
        ),
        (
            "BOOL.or",
            ["B:SortBool{}", r#"\dv{SortBool{}}("true")"#, ""],
        ),
        (
            "BOOL.orElse",
            ["B:SortBool{}", r#"\dv{SortBool{}}("true")"#, ""],
        ),
        (
            "BOOL.implies",
            [r#"\dv{SortBool{}}("false")"#, "B:SortBool{}", ""],
        ),
        (
            "KEQUAL.ite",
            [r#"\dv{SortBool{}}("true")"#, "X:SortK{}", "Y:SortK{}"],
        ),
        (
            "KEQUAL.ite",
            [r#"\dv{SortBool{}}("false")"#, "X:SortK{}", "Y:SortK{}"],
        ),
        ("INT.ne", ["X:SortInt{}", "X:SortInt{}", ""]),
        ("KEQUAL.ne", ["X:SortK{}", "X:SortK{}", ""]),
        ("STRING.ne", ["X:SortString{}", "X:SortString{}", ""]),
    ];
    let mut failures = Vec::new();
    let mut stepped = 0;
    for (hook, arguments) in cases {
        let arguments = arguments
            .iter()
            .filter(|argument| !argument.is_empty())
            .map(|argument| (*argument).to_owned())
            .collect::<Vec<_>>();
        let subject = term(&definition, &application(&definition, hook, &arguments));
        let Ok(Ok(BuiltinResult::Value(value))) = evaluate_in_definition(&subject, &definition)
        else {
            continue;
        };
        stepped += 1;
        let applies = written(&definition, hook).iter().any(|rule| {
            let Some(valuation) = matched(&rule.lhs, &subject) else {
                return false;
            };
            let RuleRhs::Term(rhs) = &rule.rhs else {
                return false;
            };
            holds(&definition, rule, &valuation) == Some(true)
                && evaluated(&definition, &substitute(rhs, &valuation)) == Ok(Some(value.clone()))
        });
        if !applies {
            failures.push(format!(
                "{hook} {arguments:?}: the builtin gives {value:?}, no entry"
            ));
        }
    }
    assert!(stepped >= 10, "the builtin stepped on {stepped} cases only");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The guarded lemma of `replaceAll`'s meaning (`confluence/hooks.rs`, `replace_all_lemma`):
/// `replaceAll(S, T, R) = replace(S, T, R, countAllOccurrences(S, T))` for a nonempty `T`, with
/// `replace` read by domains.md's two equations. The left side is evaluated by the builtin, the
/// right side through the prelude's `replace` equations (domains.md's rows, priority 50 and
/// `owise`), on the edge values of `replaceAll`'s tests: multibyte strings and self-overlapping
/// patterns (`"aaa"` with `"aa"`).
#[test]
fn the_replace_all_lemma_agrees_with_the_builtin_through_domains_replace() {
    let definition = prelude();
    let named = |hook: &str| {
        definition
            .symbols()
            .values()
            .find(|symbol| symbol.attributes.hook.as_deref() == Some(hook))
            .unwrap_or_else(|| panic!("no symbol hooked {hook}"))
            .name
            .to_string()
    };
    let (replace, count) = (named("STRING.replace"), named("STRING.countAllOccurrences"));
    let priorities = definition
        .function_theory()
        .get(&crate::rule::TermIndex::Symbol(replace.as_str().into()))
        .expect("replace has equations")
        .iter()
        .flat_map(|(priority, rules)| rules.iter().map(move |_| *priority))
        .collect::<Vec<_>>();
    assert_eq!(
        priorities,
        [
            k_rust_kore::names::DEFAULT_RULE_PRIORITY,
            k_rust_kore::names::OWISE_RULE_PRIORITY
        ]
    );
    let domains = domains("STRING.replaceAll");
    let (mut checked, mut failures) = (0, Vec::new());
    for source in &domains[0] {
        for target in &domains[1] {
            if matches!(target, Val::Str(text) if text.is_empty()) {
                continue;
            }
            for replacement in &domains[2] {
                let [s, t, r] = [source, target, replacement].map(Val::kore);
                let subject = term(
                    &definition,
                    &application(
                        &definition,
                        "STRING.replaceAll",
                        &[s.clone(), t.clone(), r.clone()],
                    ),
                );
                let Ok(Ok(BuiltinResult::Value(expected))) =
                    evaluate_in_definition(&subject, &definition)
                else {
                    failures.push(format!("{source:?} {target:?}: the builtin takes no step"));
                    continue;
                };
                let lemma = term(
                    &definition,
                    &format!("{replace}{{}}({s}, {t}, {r}, {count}{{}}({s}, {t}))"),
                );
                checked += 1;
                let found = evaluated(&definition, &lemma);
                if found != Ok(Some(expected.clone())) {
                    failures.push(format!(
                        "{source:?} {target:?} {replacement:?}: the builtin gives {expected:?}, replace {found:?}"
                    ));
                }
            }
        }
    }
    assert!(checked > 100, "{checked} instances checked");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
