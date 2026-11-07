//! The short-circuit analysis kink-native's exclusions read, called directly from
//! `k_rust_backend::short_circuit` (where `krs check` reads it too): its rule readings are the
//! rules `DefinitionExclusions` flags, its witness enumerations start with the witnesses the
//! exclusions follow, an inherited witness does not originate, and the prelude depends on no
//! reading.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::{Attributes, Definition, Pattern, Sentence};
use k_rust::names::KoreAttribute;
use k_rust_backend::short_circuit::{
    CausePart, Inlined, ShortCircuitAnalysis, Visit, Witness, equation_parts, is_owise,
    rewrite_sides,
};
use kink_native::exclusion::{CauseLink, DefinitionExclusions, ShortCircuitEffect};
use kink_native::{BACKEND_OPTIONS, NativeValidator};

/// The short-circuit fixtures of `testdata/k/r0c` that `tests/exclusion.rs` judges.
const FIXTURES: [&str; 13] = [
    "scrhs", "screq", "scstr", "scin", "scmlat", "scmloe", "scctl", "scceil", "scfetch", "scpd",
    "scpdc", "scsib", "scthru",
];

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The fixture `testdata/k/r0c/<name>.k`, compiled and loaded as kink-native loads a side, with
/// the exclusions read from that load, and the analysis `check` then runs on it.
fn with_load(
    name: &str,
    check: impl FnOnce(&Definition, &DefinitionExclusions, &ShortCircuitAnalysis<'_>),
) {
    let module = name.to_ascii_uppercase();
    let loaded = support::load_path(
        &Path::new(support::DIR).join(format!("r0c/{name}.k")),
        &module,
    );
    let side = NativeValidator::bind(loaded, CompileOptions::default())
        .compile_baseline()
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    let module = k_rust::kast::identifier::encode(&module);
    let mut load = DefinitionExclusions::load_validated(&side, &module, BACKEND_OPTIONS).unwrap();
    let definition = load.backend.select_definition(None).unwrap();
    let mut analysis = ShortCircuitAnalysis::of(&definition);
    analysis.close_over(&load.kore);
    check(&load.kore, &load.exclusions, &analysis);
}

fn attributes(sentence: &Sentence) -> &Attributes {
    match sentence {
        Sentence::Axiom { attributes, .. } => attributes,
        _ => panic!("not an axiom"),
    }
}

/// The name `DefinitionExclusions` gives a sentence: its `UNIQUE_ID`, else its label.
fn name(attributes: &Attributes) -> String {
    [KoreAttribute::UniqueId, KoreAttribute::Label]
        .into_iter()
        .find_map(|key| attributes.string(key).ok().flatten())
        .expect("a fixture sentence has an id")
        .to_owned()
}

/// The first link a witness gives a cause chain: the operator's hook-free shape (symbol,
/// position, operand, term), or the function and its dependence.
fn first_link(witness: &Witness, link: &CauseLink) -> bool {
    match (witness, link) {
        (
            Witness::Operator {
                operator,
                position,
                operand,
                term,
                ..
            },
            CauseLink::Operator(link),
        ) => {
            link.operator.id == *operator
                && link.position == *position
                && link.operand == *operand
                && link.term == *term
        }
        (
            Witness::Function { symbol, dependence },
            CauseLink::Function {
                function,
                dependence: linked,
                ..
            },
        ) => function.id == *symbol && dependence == linked,
        _ => false,
    }
}

/// B1: on every short-circuit fixture, the rules `rule_readings` names are the rules
/// `DefinitionExclusions` flags, each with the same part and the same first link, and the
/// reading-dependent functions are the exclusions' short-circuit symbols: the exclusions present
/// the shared readings without dropping, adding or changing one, so a reader of the readings
/// (`krs check`) and kink see one analysis. The exclusions are built from the readings, so this
/// does not show that the analysis kept its verdicts when it moved; `tests/exclusion.rs`, whose
/// assertions the move left unchanged, does.
#[test]
fn the_exclusions_present_the_rule_readings() {
    on_a_big_stack(|| {
        for fixture in FIXTURES {
            with_load(fixture, |kore, exclusions, analysis| {
                let readings = analysis.rule_readings(kore);
                let mut conditions = BTreeSet::new();
                let mut results = BTreeSet::new();
                for reading in &readings {
                    let (_, sentence) = reading.rule.resolve(kore).unwrap();
                    let rule = name(attributes(sentence));
                    for (effect, part, witness) in [
                        reading.applicability.as_ref().map(|(part, witness)| {
                            (ShortCircuitEffect::Applicability, part.clone(), witness)
                        }),
                        reading.result.as_ref().map(|witness| {
                            (ShortCircuitEffect::Result, CausePart::RightSide, witness)
                        }),
                    ]
                    .into_iter()
                    .flatten()
                    {
                        match effect {
                            ShortCircuitEffect::Applicability => conditions.insert(rule.clone()),
                            ShortCircuitEffect::Result => results.insert(rule.clone()),
                        };
                        let cause = exclusions
                            .short_circuit_causes
                            .iter()
                            .find(|cause| cause.rule.name == rule && cause.effect == effect)
                            .unwrap_or_else(|| panic!("{fixture}: no cause for {rule} {effect:?}"));
                        assert_eq!(cause.part, part, "{fixture}: {rule}");
                        assert!(
                            first_link(witness, &cause.links[0]),
                            "{fixture}: {rule}: {witness:#?} against {:#?}",
                            cause.links[0]
                        );
                    }
                }
                assert_eq!(
                    conditions,
                    exclusions
                        .short_circuit_conditions
                        .iter()
                        .cloned()
                        .collect(),
                    "{fixture}"
                );
                assert_eq!(
                    results,
                    exclusions.short_circuit_results.iter().cloned().collect(),
                    "{fixture}"
                );
                assert_eq!(
                    exclusions.short_circuit_causes.len(),
                    readings
                        .iter()
                        .map(|reading| {
                            usize::from(reading.applicability.is_some())
                                + usize::from(reading.result.is_some())
                        })
                        .sum::<usize>(),
                    "{fixture}"
                );
                assert_eq!(
                    exclusions.short_circuit_symbols,
                    analysis
                        .undefined()
                        .union(analysis.valued())
                        .cloned()
                        .collect(),
                    "{fixture}"
                );
            });
        }
    });
}

/// Every side of every axiom of `kore` that holds a term or a condition, with whether it holds a
/// condition: a rewrite rule's conditions and left-hand side, and its right-hand side; an
/// equation's antecedent, and its right-hand side.
fn sides(kore: &Definition) -> Vec<(&Pattern, bool)> {
    let mut sides = Vec::new();
    for module in &kore.modules {
        for sentence in &module.sentences {
            let Sentence::Axiom { pattern, .. } = sentence else {
                continue;
            };
            if let Some((conditions, left, right)) = rewrite_sides(pattern) {
                sides.extend(
                    conditions
                        .into_iter()
                        .chain([left])
                        .map(|side| (side, true)),
                );
                sides.push((right, false));
            } else if let Some((_, condition, right)) = equation_parts(pattern) {
                sides.extend(condition.map(|side| (side, true)));
                sides.push((right, false));
            }
        }
    }
    sides
}

/// B2: on every axiom side of the short-circuit fixtures, `operator_witnesses` starts with
/// `direct_witness`, and wherever `condition_side` returns an operator witness,
/// `condition_operator_witnesses` holds it at the same leaf: the enumeration `krs check` reads
/// holds the witness every flagged rule's chain follows.
#[test]
fn operator_witnesses_start_with_direct_witness() {
    on_a_big_stack(|| {
        for fixture in FIXTURES {
            with_load(fixture, |kore, _, analysis| {
                for (side, condition) in sides(kore) {
                    assert_eq!(
                        analysis.operator_witnesses(side).first(),
                        analysis.direct_witness(side).as_ref(),
                        "{fixture}: {side:?}"
                    );
                    if condition
                        && let Some((leaf, witness @ Witness::Operator { .. })) =
                            analysis.condition_side(side)
                    {
                        assert!(
                            analysis
                                .condition_operator_witnesses(side, false)
                                .contains(&(leaf, witness)),
                            "{fixture}: {side:?}"
                        );
                    }
                }
            });
        }
    });
}

/// The witness of the one equation of `head` in `kore`.
/// B2': with nothing inlined, the operator visits of every axiom of the short-circuit fixtures
/// are exactly the witnesses `condition_operator_witnesses` and `operator_witnesses` enumerate
/// over its parts, in order, and each application visit names a reading-dependent function; with
/// every function inlined, an operator visit inside an inlined function is a witness of one of
/// that function's equations. So the walk `krs check` reads enumerates what the analysis does
/// where nothing is inlined, and reads an inlined function's equations, not other places.
#[test]
fn the_axiom_visits_are_the_witness_enumerations() {
    on_a_big_stack(|| {
        for fixture in FIXTURES {
            with_load(fixture, |kore, _, analysis| {
                let mut every = BTreeMap::<String, Vec<Inlined<'_>>>::new();
                for module in &kore.modules {
                    for sentence in &module.sentences {
                        if let Sentence::Axiom {
                            pattern,
                            attributes,
                            ..
                        } = sentence
                            && let Some((head, condition, right)) = equation_parts(pattern)
                        {
                            every.entry(head.to_owned()).or_default().push(Inlined {
                                condition,
                                right,
                                owise: is_owise(attributes),
                            });
                        }
                    }
                }
                for module in &kore.modules {
                    for sentence in &module.sentences {
                        let Sentence::Axiom {
                            pattern,
                            attributes,
                            ..
                        } = sentence
                        else {
                            continue;
                        };
                        let mut expected = Vec::new();
                        if let Some((conditions, left, right)) = rewrite_sides(pattern) {
                            for side in conditions.into_iter().chain([left]) {
                                expected.extend(
                                    analysis
                                        .condition_operator_witnesses(side, false)
                                        .into_iter()
                                        .map(|(_, witness)| (true, witness)),
                                );
                            }
                            expected.extend(
                                analysis
                                    .operator_witnesses(right)
                                    .into_iter()
                                    .map(|witness| (false, witness)),
                            );
                        } else if let Some((_, condition, right)) = equation_parts(pattern) {
                            if let Some(condition) = condition {
                                expected.extend(
                                    analysis
                                        .condition_operator_witnesses(
                                            condition,
                                            is_owise(attributes),
                                        )
                                        .into_iter()
                                        .map(|(_, witness)| (true, witness)),
                                );
                            }
                            expected.extend(
                                analysis
                                    .operator_witnesses(right)
                                    .into_iter()
                                    .map(|witness| (false, witness)),
                            );
                        }
                        let Some(visits) =
                            analysis.axiom_visits(pattern, attributes, &BTreeMap::new())
                        else {
                            assert!(expected.is_empty(), "{fixture}: {pattern:?}");
                            continue;
                        };
                        let mut operators = Vec::new();
                        for visit in visits {
                            match visit {
                                Visit::Operator {
                                    condition,
                                    witness,
                                    within,
                                    ..
                                } => {
                                    assert!(within.is_empty(), "{fixture}");
                                    operators.push((condition, witness));
                                }
                                Visit::Applied { symbol, .. } => {
                                    assert!(analysis.reading_dependent(&symbol), "{fixture}");
                                }
                            }
                        }
                        assert_eq!(operators, expected, "{fixture}: {pattern:?}");
                        for visit in analysis
                            .axiom_visits(pattern, attributes, &every)
                            .unwrap_or_default()
                        {
                            if let Visit::Operator {
                                witness, within, ..
                            } = visit
                                && let Some(function) = within.last()
                            {
                                assert!(
                                    every[function].iter().any(|equation| {
                                        analysis
                                            .operator_witnesses(equation.right)
                                            .contains(&witness)
                                            || equation.condition.is_some_and(|condition| {
                                                analysis
                                                    .condition_operator_witnesses(condition, false)
                                                    .iter()
                                                    .any(|(_, found)| *found == witness)
                                            })
                                    }),
                                    "{fixture}: {function}: {witness:?}"
                                );
                            }
                        }
                    }
                }
            });
        }
    });
}

fn equation_witness(kore: &Definition, analysis: &ShortCircuitAnalysis<'_>, head: &str) -> Witness {
    let readings = analysis.equation_readings(kore);
    let mut found = readings.iter().filter(|reading| reading.head == head);
    let reading = found
        .next()
        .unwrap_or_else(|| panic!("no reading of {head}"));
    assert!(found.next().is_none(), "two readings of {head}");
    reading
        .result
        .clone()
        .unwrap_or_else(|| panic!("{head}: {reading:#?}"))
}

/// B3: `f(N, D) => D =/=Int 0 andThenBool N /Int D >Int 1` originates; `g(B, N, D) => B
/// andThenBool f(N, D)` does not while `f` is declared `total` (its witness is inherited from
/// `f`), and does once `f` is partial.
#[test]
fn an_inherited_witness_does_not_originate() {
    on_a_big_stack(|| {
        with_load("scorig", |kore, _, analysis| {
            assert!(analysis.originates(&equation_witness(kore, analysis, "Lblf")));
            let inherited = equation_witness(kore, analysis, "Lblg");
            assert!(
                matches!(
                    inherited,
                    Witness::Operator {
                        through: Some(_),
                        ..
                    }
                ),
                "{inherited:#?}"
            );
            assert!(!analysis.originates(&inherited), "{inherited:#?}");
        });
        with_load("scorigp", |kore, _, analysis| {
            assert!(analysis.originates(&equation_witness(kore, analysis, "Lblf")));
            assert!(analysis.originates(&equation_witness(kore, analysis, "Lblg")));
        });
    });
}

/// B4: a definition importing the builtin modules (`DOMAINS`, `BYTES`, `FLOAT`, `ARRAY`,
/// `RANGEMAP`, `K-REFLECTION`, `STRING-BUFFER`) with one constructor and no rule of its own has
/// no rewrite rule that depends on the reading, so a lint that reports a rule whose chain no
/// author outside the prelude wrote reports nothing on the pinned prelude; the one equation that
/// does is `isInfinite`'s, whose `orBool` skips a comparison with `maxValueFloat`, a partial
/// function, so a sentence that applies `isInfinite` depends on the reading through it.
#[test]
fn the_prelude_has_no_reading_dependent_rule() {
    on_a_big_stack(|| {
        with_load("scprelude", |kore, _, analysis| {
            assert_eq!(analysis.rule_readings(kore), Vec::new());
            assert_eq!(
                analysis
                    .equation_readings(kore)
                    .iter()
                    .map(|reading| reading.head.as_str())
                    .collect::<Vec<_>>(),
                ["LblisInfinite'LParUndsRParUnds'FLOAT'Unds'Bool'Unds'Float"]
            );
        });
    });
}

/// A conjunctive call at the top of a condition makes no visit, since the readings differ in no
/// rule there, but it holds its place in the order of its function's applications: `go`'s
/// application of `ok` in its right-hand side is the second of the rule's, as a reader of the
/// written rule, who cannot tell which functions are conjunctive, counts them (`krs check` places
/// a finding through the prelude by that count).
#[test]
fn a_conjunctive_call_at_the_top_of_a_condition_holds_its_place() {
    on_a_big_stack(|| {
        with_load("sccnj", |kore, _, analysis| {
            let (pattern, attributes) = kore
                .modules
                .iter()
                .flat_map(|module| &module.sentences)
                .find_map(|sentence| match sentence {
                    Sentence::Axiom {
                        pattern,
                        attributes,
                        ..
                    } if attributes
                        .string(KoreAttribute::Label)
                        .ok()
                        .flatten()
                        .is_some_and(|label| label == "go" || label.ends_with(".go")) =>
                    {
                        Some((pattern, attributes))
                    }
                    _ => None,
                })
                .expect("the fixture has the rule go");
            let applied = analysis
                .axiom_visits(pattern, attributes, &BTreeMap::new())
                .expect("go is a rewrite rule")
                .into_iter()
                .filter_map(|visit| match visit {
                    Visit::Applied {
                        symbol,
                        condition,
                        occurrence,
                        ..
                    } => Some((symbol, condition, occurrence)),
                    Visit::Operator { .. } => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(applied, [("Lblok".to_owned(), false, 1)]);
        });
    });
}
