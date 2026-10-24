//! The written meanings of the hooks (`confluence/hooks.rs`) against models of the hooks.
//!
//! Each written meaning is a set of equations at a hooked symbol that the critical-pair check
//! reads as true, so each must be an identity of the builtin: on every tuple of argument values
//! where the hook is defined, each entry whose left-hand side matches and whose `requires` holds
//! has a right-hand side that evaluates to the hook's value (`\bottom` where the hook is
//! undefined), and some entry applies (coverage). The models below are written from the hooks'
//! meanings (`crates/k-rust/builtin/domains.md`): Boolean connectives, integer arithmetic, the
//! code-point order and occurrences of strings, and set union. The right-hand sides are evaluated
//! by the backend in FUN's prelude (`tests/fixtures/fun-prelude-hooked-equations.kore`), which
//! declares every hook the table names.
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

/// A value of the models.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Val {
    Bool(bool),
    Int(i64),
    Str(String),
    /// A `K` sequence: one injected integer item, or the empty sequence (`None`).
    K(Option<i64>),
    Set(BTreeSet<i64>),
}

impl Val {
    fn kore(&self) -> String {
        let int = |value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#);
        match self {
            Self::Bool(value) => format!(r#"\dv{{SortBool{{}}}}("{value}")"#),
            Self::Int(value) => int(*value),
            Self::Str(value) => format!(r#"\dv{{SortString{{}}}}("{value}")"#),
            Self::K(None) => "dotk{}()".into(),
            Self::K(Some(value)) => format!(
                "kseq{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({}), dotk{{}}())",
                int(*value)
            ),
            Self::Set(elements) => elements.iter().fold("Lbl'Stop'Set{}()".into(), |set, value| {
                format!(
                    "Lbl'Unds'Set'Unds'{{}}({set}, LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({})))",
                    int(*value)
                )
            }),
        }
    }
}

/// What the hook gives on concrete arguments.
enum Model {
    Value(Val),
    Bottom,
    /// The meaning leaves the value open (`countAllOccurrences(S, "")`): no builtin step, nothing
    /// to compare.
    Open,
}

/// The non-overlapping occurrences of the nonempty `target` in `source`, from the left, as the
/// code-point offsets where each begins.
fn occurrences(source: &[char], target: &[char]) -> Vec<usize> {
    let mut found = Vec::new();
    let mut start = 0;
    while start + target.len() <= source.len() {
        if source[start..start + target.len()] == *target {
            found.push(start);
            start += target.len();
        } else {
            start += 1;
        }
    }
    found
}

/// The models, from the hooks' meanings.
fn model(hook: &str, arguments: &[Val]) -> Model {
    use Val::{Bool, Int, Set, Str};
    let value = Model::Value;
    match (hook, arguments) {
        ("BOOL.not", [Bool(b)]) => value(Bool(!b)),
        ("BOOL.and" | "BOOL.andThen", [Bool(a), Bool(b)]) => value(Bool(*a && *b)),
        ("BOOL.or" | "BOOL.orElse", [Bool(a), Bool(b)]) => value(Bool(*a || *b)),
        ("BOOL.xor" | "BOOL.ne", [Bool(a), Bool(b)]) => value(Bool(a != b)),
        ("BOOL.implies", [Bool(a), Bool(b)]) => value(Bool(!*a || *b)),
        ("KEQUAL.ite", [Bool(c), then, otherwise]) => {
            value(if *c { then.clone() } else { otherwise.clone() })
        }
        ("KEQUAL.ne", [left, right]) | ("INT.ne", [left, right]) | ("STRING.ne", [left, right]) => {
            value(Bool(left != right))
        }
        ("INT.min", [Int(a), Int(b)]) => value(Int(*a.min(b))),
        ("INT.ediv", [Int(a), Int(b)]) => {
            if *b == 0 {
                Model::Bottom
            } else {
                value(Int((a - a.rem_euclid(*b)) / b))
            }
        }
        ("INT.bitRange", [Int(i), Int(index), Int(length)]) => {
            if *index < 0 || *length < 0 {
                Model::Bottom
            } else {
                value(Int((i >> index).rem_euclid(1 << length)))
            }
        }
        ("INT.signExtendBitRange", [Int(i), Int(index), Int(length)]) => {
            if *index < 0 || *length < 1 {
                Model::Bottom
            } else {
                let bits = (i >> index).rem_euclid(1 << length);
                value(Int(if bits >= 1 << (length - 1) {
                    bits - (1 << length)
                } else {
                    bits
                }))
            }
        }
        // The code-point order of strings (here ASCII).
        ("STRING.le", [Str(a), Str(b)]) => value(Bool(a <= b)),
        ("STRING.gt", [Str(a), Str(b)]) => value(Bool(a > b)),
        ("STRING.ge", [Str(a), Str(b)]) => value(Bool(a >= b)),
        ("STRING.countAllOccurrences", [Str(source), Str(target)]) => {
            if target.is_empty() {
                return Model::Open;
            }
            let (source, target) = (
                source.chars().collect::<Vec<_>>(),
                target.chars().collect::<Vec<_>>(),
            );
            value(Int(occurrences(&source, &target).len() as i64))
        }
        ("STRING.replaceAll", [Str(source), Str(target), Str(replacement)]) => {
            if target.is_empty() {
                return Model::Open;
            }
            let (characters, pattern) = (
                source.chars().collect::<Vec<_>>(),
                target.chars().collect::<Vec<_>>(),
            );
            let mut result = String::new();
            let mut position = 0;
            for start in occurrences(&characters, &pattern) {
                result.extend(&characters[position..start]);
                result.push_str(replacement);
                position = start + pattern.len();
            }
            result.extend(&characters[position..]);
            value(Str(result))
        }
        ("SET.union", [Set(a), Set(b)]) => value(Set(a.union(b).cloned().collect())),
        _ => panic!("no model of {hook} on {arguments:?}"),
    }
}

/// The argument values a hook's tests draw from, each a list of choices per argument.
fn domains(hook: &str) -> Vec<Vec<Val>> {
    let bools = || vec![Val::Bool(false), Val::Bool(true)];
    let ints = |range: std::ops::RangeInclusive<i64>| range.map(Val::Int).collect::<Vec<_>>();
    let strings = || {
        ["", "a", "b", "aa", "ab", "ba", "aaa", "aba", "abab", "baa"]
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
        "INT.ne" | "INT.min" => vec![ints(-3..=3), ints(-3..=3)],
        "INT.ediv" => vec![ints(-7..=7), ints(-3..=3)],
        "INT.bitRange" | "INT.signExtendBitRange" => {
            vec![ints(-9..=9), ints(-1..=3), ints(-1..=4)]
        }
        "STRING.ne" | "STRING.le" | "STRING.gt" | "STRING.ge" | "STRING.countAllOccurrences" => {
            vec![strings(), strings()]
        }
        "STRING.replaceAll" => vec![
            strings(),
            strings(),
            vec![
                Val::Str(String::new()),
                Val::Str("c".into()),
                Val::Str("cb".into()),
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

/// The failures of `hook`'s written meaning on every tuple of its domains: an entry that applies
/// and gives another result than the model, a `requires` the simplifier does not decide, or a
/// tuple where the hook is defined and no entry applies.
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
        let expected = match model(hook, &tuple) {
            Model::Open => continue,
            Model::Bottom => None,
            Model::Value(value) => {
                let expected = term(definition, &value.kore());
                Some(
                    evaluated(definition, &expected)
                        .expect("a value evaluates")
                        .expect("a value"),
                )
            }
        };
        let kore = tuple.iter().map(Val::kore).collect::<Vec<_>>();
        let subject = term(definition, &application(definition, hook, &kore));
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
                Ok(found) => failures.push(format!(
                    "{hook} {tuple:?}: {} gives {found:?}, the model {expected:?}",
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
