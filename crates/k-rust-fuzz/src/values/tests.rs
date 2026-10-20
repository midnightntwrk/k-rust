//! Tests of hole values: sort resolution, constraints, generators and printing (FZ-03).
//!
//! The definition these tests resolve sorts against, and whose frontend parses printed values
//! back, is the IMP fixture (`tests/data/imp/imp.k`, FZ-FIX), compiled in-process in the
//! portable build the way `tests/support` compiles it. Its loaded definition carries every
//! module of the embedded prelude, so the syntax modules of `String`, `Bytes` and `MInt`
//! (`STRING-SYNTAX`, `BYTES-SYNTAX`, `MINT-SYNTAX`) parse printed values even though IMP's own
//! program grammar does not import them.

use std::{collections::BTreeMap, process::Command};

use k_rust::{
    inner::ProgramParser,
    k_rust_backend::{externalize, term::Term},
    kast::parser::parse_sort,
    kompile::term_to_kore_from_resolved_with_token_module,
    kore::ast::{Pattern, Sort as KoreSort},
};
use num_bigint::{BigInt, BigUint};

use super::test_definition::imp;
use super::{
    CollectionSymbols, Constraints, DataSorts, ElementSorts, GenerationBounds, IntRange,
    LengthRange, Value, ValueSort, check_constraints,
    generator::{Generator, ValueRng},
    print::{PrintError, parse_k_text, print_k_text, to_kore},
    resolve_value_sort,
};
use crate::error::SortRefusal;

// ------------------------------------------------------------------------------------------
// The IMP fixture (`values/test_definition.rs`).

/// `text` parsed by the frontend at `sort` with the parser of `module`, converted to KORE as a
/// program token is (tokens keep the lexical hooks of the module that parsed them).
fn frontend_kore(module: &str, sort: &str, text: &str) -> Result<Pattern, String> {
    let resolved = imp().grammar.resolved();
    let parser = ProgramParser::from_resolved(resolved, module).map_err(|e| format!("{e:?}"))?;
    let sort = parse_sort(sort).map_err(|e| format!("{e:?}"))?;
    let parsed = parser.parse(&sort, text).map_err(|e| format!("{e:?}"))?;
    term_to_kore_from_resolved_with_token_module(resolved, module, module, parsed.typed_term())
        .map_err(|e| format!("{e:?}"))
}

// ------------------------------------------------------------------------------------------
// Helpers.

fn int(value: i64) -> BigInt {
    BigInt::from(value)
}

fn range(min: Option<i64>, max: Option<i64>) -> Constraints {
    Constraints {
        range: Some(IntRange {
            min: min.map(BigInt::from),
            max: max.map(BigInt::from),
        }),
        ..Constraints::default()
    }
}

fn length(min: Option<u64>, max: Option<u64>) -> Constraints {
    Constraints {
        length: Some(LengthRange { min, max }),
        ..Constraints::default()
    }
}

/// The symbols of the prelude's collection sorts, as the frontend encodes their labels.
fn symbols(sort: &str, unit: &str, element: &str, concat: &str) -> CollectionSymbols {
    let arguments = if sort == "SortMap" { 2 } else { 1 };
    CollectionSymbols {
        kore_sort: sort.into(),
        unit: unit.into(),
        element: element.into(),
        concat: concat.into(),
        element_arguments: vec!["SortKItem".to_owned(); arguments],
    }
}

fn list_symbols() -> CollectionSymbols {
    symbols(
        "SortList",
        "Lbl'Stop'List",
        "LblListItem",
        "Lbl'Unds'List'Unds'",
    )
}

fn set_symbols() -> CollectionSymbols {
    symbols(
        "SortSet",
        "Lbl'Stop'Set",
        "LblSetItem",
        "Lbl'Unds'Set'Unds'",
    )
}

fn map_symbols() -> CollectionSymbols {
    symbols(
        "SortMap",
        "Lbl'Stop'Map",
        "Lbl'UndsPipe'-'-GT-Unds'",
        "Lbl'Unds'Map'Unds'",
    )
}

fn seed(byte: u8) -> [u8; 32] {
    [byte; 32]
}

/// The (sort, constraints) pairs every generator test draws from.
fn generator_cases() -> Vec<(ValueSort, Constraints)> {
    let huge = BigInt::from(1u8) << 200u32;
    vec![
        (ValueSort::Int, Constraints::default()),
        (ValueSort::Int, range(Some(0), Some(1_000_000))),
        (ValueSort::Int, range(Some(-50), Some(-10))),
        (ValueSort::Int, range(Some(7), Some(7))),
        (ValueSort::Int, range(Some(-3), None)),
        (ValueSort::Int, range(None, Some(-1_000))),
        (
            ValueSort::Int,
            Constraints {
                range: Some(IntRange {
                    min: Some(huge.clone()),
                    max: Some(&huge * 3),
                }),
                ..Constraints::default()
            },
        ),
        (ValueSort::Bool, Constraints::default()),
        (ValueSort::String, Constraints::default()),
        (ValueSort::String, length(Some(2), Some(5))),
        (ValueSort::String, length(Some(20), None)),
        (ValueSort::Bytes, Constraints::default()),
        (ValueSort::Bytes, length(None, Some(3))),
        (ValueSort::MInt { width: 8 }, Constraints::default()),
        (ValueSort::MInt { width: 8 }, range(Some(-5), Some(9))),
        (ValueSort::MInt { width: 1 }, Constraints::default()),
        (ValueSort::MInt { width: 256 }, Constraints::default()),
        (
            ValueSort::Int,
            Constraints {
                choices: Some(vec![
                    Value::Int(int(3)),
                    Value::Int(int(-8)),
                    Value::Int(int(42)),
                ]),
                ..Constraints::default()
            },
        ),
        (
            ValueSort::Token { sort: "Id".into() },
            Constraints {
                choices: Some(vec![
                    Value::Token {
                        sort: "Id".into(),
                        text: "x".into(),
                    },
                    Value::Token {
                        sort: "Id".into(),
                        text: "y".into(),
                    },
                ]),
                ..Constraints::default()
            },
        ),
    ]
}

/// Draw `count` values of each generator case, each followed by up to `shrinks` alternating
/// simplify and complicate steps, and return every value seen.
fn draw_all(seed: [u8; 32], count: usize, shrinks: usize) -> Vec<Value> {
    let bounds = GenerationBounds::default();
    let mut rng = ValueRng::from_seed(seed);
    let mut drawn = Vec::new();
    for (sort, constraints) in generator_cases() {
        let generator = Generator::new(&sort, &constraints, &bounds)
            .unwrap_or_else(|error| panic!("{sort:?} {constraints:?}: {error}"));
        for _ in 0..count {
            let mut tree = generator.generate(&mut rng);
            drawn.push(tree.current());
            for step in 0..shrinks {
                let moved = if step % 3 == 2 {
                    tree.complicate()
                } else {
                    tree.simplify()
                };
                if !moved {
                    break;
                }
                drawn.push(tree.current());
            }
        }
    }
    drawn
}

// ------------------------------------------------------------------------------------------
// Generators stay inside their sort and constraints.

#[test]
fn a_generator_never_leaves_its_range() {
    let bounds = GenerationBounds::default();
    for byte in 0..4u8 {
        let mut rng = ValueRng::from_seed(seed(byte));
        for (sort, constraints) in generator_cases() {
            let generator = Generator::new(&sort, &constraints, &bounds).unwrap();
            for _ in 0..200 {
                let mut tree = generator.generate(&mut rng);
                let mut steps = 0;
                loop {
                    let value = tree.current();
                    check_constraints(&value, &sort, &constraints).unwrap_or_else(|error| {
                        panic!("{sort:?} {constraints:?} produced {value:?}: {error}")
                    });
                    steps += 1;
                    let moved = if steps % 4 == 0 {
                        tree.complicate()
                    } else {
                        tree.simplify()
                    };
                    if !moved || steps > 400 {
                        break;
                    }
                }
            }
        }
    }
}

#[test]
fn unranged_values_respect_the_default_bounds() {
    let bounds = GenerationBounds {
        int_bits: 10,
        length: 4,
        depth: 1,
    };
    let mut rng = ValueRng::from_seed(seed(9));
    let limit = BigInt::from(1u32 << 10);
    let ints = Generator::new(&ValueSort::Int, &Constraints::default(), &bounds).unwrap();
    let strings = Generator::new(&ValueSort::String, &Constraints::default(), &bounds).unwrap();
    let bytes = Generator::new(&ValueSort::Bytes, &Constraints::default(), &bounds).unwrap();
    let mut saw_negative = false;
    let mut saw_large = false;
    for _ in 0..500 {
        let Value::Int(value) = ints.generate(&mut rng).current() else {
            panic!("an Int generator produced another sort");
        };
        assert!(-&limit < value && value < limit, "{value} exceeds 10 bits");
        saw_negative |= value < int(0);
        saw_large |= value.bits() >= 9;
        let Value::String(text) = strings.generate(&mut rng).current() else {
            panic!("a String generator produced another sort");
        };
        assert!(text.chars().count() <= 4, "{text:?} is longer than 4");
        let Value::Bytes(data) = bytes.generate(&mut rng).current() else {
            panic!("a Bytes generator produced another sort");
        };
        assert!(data.len() <= 4, "{data:?} is longer than 4");
    }
    assert!(
        saw_negative && saw_large,
        "the Int generator covers signs and magnitudes"
    );
}

#[test]
fn ranges_reach_their_ends() {
    // Boundary values are where guards change their answer; the generator proposes them.
    let bounds = GenerationBounds::default();
    let constraints = range(Some(-1_000_000), Some(1_000_000));
    let generator = Generator::new(&ValueSort::Int, &constraints, &bounds).unwrap();
    let mut rng = ValueRng::from_seed(seed(3));
    let values: Vec<Value> = (0..400)
        .map(|_| generator.generate(&mut rng).current())
        .collect();
    for end in [-1_000_000, 0, 1_000_000] {
        assert!(values.contains(&Value::Int(int(end))), "{end} never drawn");
    }
}

#[test]
fn int_values_shrink_towards_the_range_value_nearest_zero() {
    let bounds = GenerationBounds::default();
    for (constraints, target) in [
        (Constraints::default(), 0),
        (range(Some(10), Some(1_000)), 10),
        (range(Some(-1_000), Some(-10)), -10),
    ] {
        let generator = Generator::new(&ValueSort::Int, &constraints, &bounds).unwrap();
        let mut rng = ValueRng::from_seed(seed(5));
        for _ in 0..50 {
            let mut tree = generator.generate(&mut rng);
            let mut steps = 0;
            while tree.simplify() {
                steps += 1;
                assert!(steps < 1_000, "simplification does not terminate");
            }
            assert_eq!(tree.current(), Value::Int(int(target)));
        }
    }
}

#[test]
fn a_choice_set_draws_only_its_members() {
    let bounds = GenerationBounds::default();
    let choices = vec![Value::Int(int(1)), Value::Int(int(99)), Value::Int(int(-4))];
    let constraints = Constraints {
        choices: Some(choices.clone()),
        ..Constraints::default()
    };
    let generator = Generator::new(&ValueSort::Int, &constraints, &bounds).unwrap();
    let mut rng = ValueRng::from_seed(seed(1));
    let mut seen = Vec::new();
    for _ in 0..200 {
        let value = generator.generate(&mut rng).current();
        assert!(choices.contains(&value), "{value:?} is not a choice");
        if !seen.contains(&value) {
            seen.push(value);
        }
    }
    assert_eq!(seen.len(), 3, "every choice is drawn");
}

#[test]
fn inconsistent_constraints_are_refused() {
    let bounds = GenerationBounds::default();
    let refused = [
        (ValueSort::Int, range(Some(5), Some(4))),
        (ValueSort::String, range(Some(0), Some(4))),
        (ValueSort::Int, length(Some(0), Some(4))),
        (ValueSort::Bytes, length(Some(5), Some(4))),
        (ValueSort::MInt { width: 8 }, range(Some(256), Some(300))),
        (ValueSort::MInt { width: 8 }, range(None, Some(-1))),
        (
            ValueSort::Int,
            Constraints {
                choices: Some(Vec::new()),
                ..Constraints::default()
            },
        ),
        (
            ValueSort::Int,
            Constraints {
                range: Some(IntRange {
                    min: Some(int(0)),
                    max: Some(int(10)),
                }),
                choices: Some(vec![Value::Int(int(11))]),
                ..Constraints::default()
            },
        ),
        (
            ValueSort::Bool,
            Constraints {
                choices: Some(vec![Value::Int(int(1))]),
                ..Constraints::default()
            },
        ),
        (
            ValueSort::Int,
            Constraints {
                elements: Some(ElementSorts::Elements {
                    element: "Int".into(),
                }),
                ..Constraints::default()
            },
        ),
        // No generator for these in this milestone, and no choice set (FZ-09, FZ-G6).
        (
            ValueSort::Token { sort: "Id".into() },
            Constraints::default(),
        ),
        (
            // A data sort resolved without its constructor table.
            ValueSort::Data {
                sort: "Tx".into(),
                table: DataSorts::default(),
                text: None,
            },
            Constraints::default(),
        ),
    ];
    for (sort, constraints) in refused {
        assert!(
            Generator::new(&sort, &constraints, &bounds).is_err(),
            "{sort:?} {constraints:?} is accepted"
        );
    }
}

// ------------------------------------------------------------------------------------------
// Determinism.

#[test]
fn the_same_seed_gives_the_same_values() {
    assert_eq!(draw_all(seed(7), 30, 12), draw_all(seed(7), 30, 12));
    assert_ne!(draw_all(seed(7), 30, 0), draw_all(seed(8), 30, 0));
}

/// The environment variable that makes [`environment_probe`] print its draws.
const PROBE: &str = "K_RUST_FUZZ_VALUES_PROBE";

/// Markers around the probe's output on standard output.
const PROBE_BEGIN: &str = "<<<values-probe>>>";
const PROBE_END: &str = "<<<end-values-probe>>>";

/// Run in a child process by [`the_same_seed_gives_the_same_values_whatever_the_environment`]:
/// print the draws of a fixed seed and the `cases` of proptest's own default `Config`, which is
/// read from `PROPTEST_*` variables exactly when proptest's `std` feature is on. Without the
/// probe variable it does nothing.
#[test]
fn environment_probe() {
    if std::env::var_os(PROBE).is_none() {
        return;
    }
    let draws = serde_json::to_string(&draw_all(seed(11), 20, 8)).unwrap();
    let cases = proptest::test_runner::Config::default().cases;
    let config = serde_json::to_string(&explicit_config()).unwrap();
    println!(
        "{PROBE_BEGIN}{{\"proptest-default-cases\":{cases},\"config\":{config},\"draws\":{draws}}}{PROBE_END}"
    );
}

/// Every field of the engine's `Config` that is not feature-gated, as text (FZ-03 review
/// note 1): a field the engine stops setting explicitly would then follow the environment, and
/// the children of the environment test would disagree on it even when no strategy reads it.
fn explicit_config() -> String {
    let config = super::generator::engine_config(&seed(11));
    format!(
        "cases={} local_rejects={} global_rejects={} flat_map_regens={} persistence={} \
         source_file={:?} test_name={:?} shrink_iters={} default_size_range={} rng={:?} seed={:?}",
        config.cases,
        config.max_local_rejects,
        config.max_global_rejects,
        config.max_flat_map_regens,
        config.failure_persistence.is_some(),
        config.source_file,
        config.test_name,
        config.max_shrink_iters,
        config.max_default_size_range,
        config.rng_algorithm,
        config.rng_seed,
    )
}

/// The probe's output in a child process whose environment has every `PROPTEST_*` variable of
/// this process removed and then `variables` set.
fn probe_in_child(variables: &[(&str, &str)]) -> serde_json::Value {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args([
        "--exact",
        "values::tests::environment_probe",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (name, _) in std::env::vars_os() {
        if name.to_string_lossy().starts_with("PROPTEST_") {
            command.env_remove(name);
        }
    }
    command.env(PROBE, "1");
    for (name, value) in variables {
        command.env(name, value);
    }
    let output = command.output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "probe failed: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let begin = stdout.find(PROBE_BEGIN).expect("probe printed nothing") + PROBE_BEGIN.len();
    let end = stdout
        .find(PROBE_END)
        .expect("probe output is unterminated");
    serde_json::from_str(&stdout[begin..end]).unwrap()
}

/// ARCHITECTURE 3, 5.4 and T-2: proptest's configuration from the environment is excluded by
/// construction. Two child processes of this test binary, one without any `PROPTEST_*` variable
/// and one with every variable proptest reads set to a non-default value, draw the same values
/// from the same seed, and the same as this process.
///
/// Whether proptest reads the environment at all depends on its `std` feature, which a
/// `cargo test --workspace` build turns on through the other crates' dev-dependencies, and a
/// `cargo test -p k-rust-fuzz` build leaves off. The probe reports proptest's default `cases`, so
/// with `std` on the test also checks that the second child's environment did reach proptest.
#[test]
fn the_same_seed_gives_the_same_values_whatever_the_environment() {
    let plain = probe_in_child(&[]);
    let varied = probe_in_child(&[
        ("PROPTEST_CASES", "3"),
        ("PROPTEST_RNG_ALGORITHM", "xs"),
        ("PROPTEST_RNG_SEED", "12345"),
        ("PROPTEST_MAX_LOCAL_REJECTS", "1"),
        ("PROPTEST_MAX_GLOBAL_REJECTS", "1"),
        ("PROPTEST_MAX_FLAT_MAP_REGENS", "1"),
        ("PROPTEST_MAX_SHRINK_TIME", "1"),
        ("PROPTEST_MAX_SHRINK_ITERS", "1"),
        ("PROPTEST_MAX_DEFAULT_SIZE_RANGE", "1"),
        ("PROPTEST_VERBOSE", "2"),
        ("PROPTEST_FORK", "true"),
        ("PROPTEST_TIMEOUT", "1"),
    ]);
    assert_eq!(plain["draws"], varied["draws"]);
    assert_eq!(plain["config"], varied["config"]);
    assert_eq!(
        plain["config"],
        serde_json::Value::String(explicit_config())
    );
    let here = serde_json::to_value(draw_all(seed(11), 20, 8)).unwrap();
    assert_eq!(plain["draws"], here);
    let proptest_reads_environment = cfg!(not(target_arch = "wasm32"))
        && varied["proptest-default-cases"] != plain["proptest-default-cases"];
    if proptest_reads_environment {
        assert_eq!(varied["proptest-default-cases"], 3);
    }
    eprintln!(
        "proptest read the varied environment: {proptest_reads_environment} \
         (true exactly when its `std` feature is on in this build)"
    );
}

// ------------------------------------------------------------------------------------------
// Printing.

#[test]
fn builtin_values_print_as_k_literals() {
    let cases = [
        (Value::Int(int(-5)), ValueSort::Int, "-5"),
        (Value::Int(int(0)), ValueSort::Int, "0"),
        (Value::Bool(true), ValueSort::Bool, "true"),
        (
            Value::String("a\"b\\\n\t\u{e9}\u{2603}\u{1f600}\u{7f}".into()),
            ValueSort::String,
            r#""a\"b\\\n\t\xe9\u2603\U0001f600\x7f""#,
        ),
        (
            Value::Bytes(vec![0, b'a', b'"', b'\\', 0x0c, 0xff]),
            ValueSort::Bytes,
            r#"b"\x00a\"\\\f\xff""#,
        ),
        (
            Value::MInt {
                width: 8,
                value: BigUint::from(255u32),
            },
            ValueSort::MInt { width: 8 },
            "255p8",
        ),
        (
            Value::Token {
                sort: "Id".into(),
                text: "x1".into(),
            },
            ValueSort::Token { sort: "Id".into() },
            "x1",
        ),
    ];
    for (value, sort, text) in cases {
        assert_eq!(print_k_text(&value, &sort).unwrap(), text);
    }
}

#[test]
fn printing_refuses_mismatched_and_unsupported_values() {
    assert_eq!(
        print_k_text(&Value::Bool(true), &ValueSort::Int),
        Err(PrintError::SortMismatch)
    );
    assert_eq!(
        to_kore(&Value::Int(int(1)), &ValueSort::String),
        Err(PrintError::SortMismatch)
    );
    let data = Value::Apply {
        symbol: "Lbltransfer".into(),
        arguments: vec![Value::Int(int(1)), Value::Int(int(2))],
    };
    let sort = ValueSort::Data {
        sort: "Tx".into(),
        table: DataSorts::default(),
        text: None,
    };
    assert!(matches!(
        print_k_text(&data, &sort),
        Err(PrintError::Unsupported(_))
    ));
    assert!(to_kore(&data, &sort).is_err());
}

/// The sort's syntax module and K name for the frontend parse of a printed value.
///
/// `None` for `MInt{W}`: the frontend parses a literal of a parametric instance only when the
/// definition declares that instance (`syntax MInt{8}`), which no prelude module and no fixture
/// does, so its printed literals are checked by the crate's reader and the KORE payload alone.
fn syntax_of(sort: &ValueSort) -> Option<(&'static str, &'static str)> {
    match sort {
        ValueSort::Int => Some(("INT-SYNTAX", "Int")),
        ValueSort::Bool => Some(("BOOL-SYNTAX", "Bool")),
        ValueSort::String => Some(("STRING-SYNTAX", "String")),
        ValueSort::Bytes => Some(("BYTES-SYNTAX", "Bytes")),
        // `Id` tokens lex in a program grammar that imports `ID` (`ID-SYNTAX-PROGRAM-PARSING`).
        ValueSort::Token { .. } => Some(("IMP-SYNTAX", "Id")),
        ValueSort::MInt { .. } => None,
        other => panic!("no syntax module for {other:?}"),
    }
}

#[test]
fn printed_values_parse_back() {
    let bounds = GenerationBounds::default();
    let mut rng = ValueRng::from_seed(seed(21));
    let mut checked = 0;
    for (sort, constraints) in generator_cases() {
        let generator = Generator::new(&sort, &constraints, &bounds).unwrap();
        let syntax = syntax_of(&sort);
        for _ in 0..60 {
            let value = generator.generate(&mut rng).current();
            let text = print_k_text(&value, &sort).unwrap();
            // The crate's own reader of the literal syntax gives the value back.
            assert_eq!(parse_k_text(&text, &sort), Ok(value.clone()), "{text}");
            // The frontend's lexer and token conversion give the KORE `to_kore` states.
            let expected = to_kore(&value, &sort).unwrap();
            checked += 1;
            let Some((module, k_sort)) = syntax else {
                // The KORE payload of an MInt value is its printed literal, which is the
                // canonical residue the backend keeps.
                let Pattern::DomainValue { value: payload, .. } = &expected else {
                    panic!("an MInt value is a domain value");
                };
                assert_eq!(payload.as_utf8(), Ok(text.as_str()));
                continue;
            };
            let parsed = frontend_kore(module, k_sort, &text)
                .unwrap_or_else(|error| panic!("{text} does not parse at {k_sort}: {error}"));
            assert_eq!(parsed, expected, "{text}");
        }
    }
    assert!(checked > 1_000);
}

#[test]
fn kore_agrees_with_the_backend_constructors() {
    let values: [(Value, ValueSort, Term); 5] = [
        (Value::Int(int(-12)), ValueSort::Int, Term::int(-12)),
        (Value::Bool(false), ValueSort::Bool, Term::bool(false)),
        (
            Value::String("x\u{e9}\u{1f600}".into()),
            ValueSort::String,
            Term::string("x\u{e9}\u{1f600}"),
        ),
        (
            Value::Bytes(vec![0, 0x80, 0xff]),
            ValueSort::Bytes,
            Term::bytes(vec![0u8, 0x80, 0xff]),
        ),
        (
            Value::Int(int(1) << 100u32),
            ValueSort::Int,
            Term::int(int(1) << 100u32),
        ),
    ];
    for (value, sort, term) in values {
        assert_eq!(to_kore(&value, &sort).unwrap(), externalize::term(&term));
    }
    // A machine integer's domain value is its unsigned residue, `p` and the width, at
    // `SortMInt{Sort<width>{}}`.
    let expected = Pattern::DomainValue {
        sort: KoreSort::Application {
            name: "SortMInt".into(),
            arguments: vec![KoreSort::Application {
                name: "Sort8".into(),
                arguments: Vec::new(),
            }],
        },
        value: "200p8".into(),
    };
    let mint = Value::MInt {
        width: 8,
        value: BigUint::from(200u32),
    };
    assert_eq!(to_kore(&mint, &ValueSort::MInt { width: 8 }), Ok(expected));
}

// ------------------------------------------------------------------------------------------
// Sort resolution and constraint checks.

fn elements(element: &str) -> Constraints {
    Constraints {
        elements: Some(ElementSorts::Elements {
            element: element.into(),
        }),
        ..Constraints::default()
    }
}

#[test]
fn builtin_sorts_resolve_and_hooked_sorts_without_a_generator_are_refused() {
    let definition = &imp().backend;
    let none = Constraints::default();
    assert_eq!(
        resolve_value_sort("Int", &none, definition),
        Ok(ValueSort::Int)
    );
    assert_eq!(
        resolve_value_sort("Bool", &none, definition),
        Ok(ValueSort::Bool)
    );
    assert_eq!(
        resolve_value_sort("Id", &none, definition),
        Ok(ValueSort::Token { sort: "Id".into() })
    );
    assert_eq!(
        resolve_value_sort("NoSuchSort", &none, definition),
        Err(SortRefusal::Unknown)
    );
    // Without a K-text syntax nothing but `K` and `KItem` is excluded, so a program sort
    // resolves to a data sort; the hole-sort rule refuses it first (FZ-02), and
    // `TextSyntax::resolve` leaves it out.
    assert!(matches!(
        resolve_value_sort("Pgm", &none, definition),
        Ok(ValueSort::Data { sort, table, .. }) if sort == "Pgm" && !table.sorts.is_empty()
    ));
    // IMP imports MAP and SET: collections need element sorts, which must resolve.
    assert_eq!(
        resolve_value_sort("Set", &none, definition),
        Err(SortRefusal::Collection)
    );
    assert_eq!(
        resolve_value_sort("Set", &elements("Int"), definition),
        Ok(ValueSort::Set {
            sort: "Set".into(),
            symbols: set_symbols(),
            element: Box::new(ValueSort::Int),
            text: None,
        })
    );
    assert_eq!(
        resolve_value_sort("Set", &elements("NoSuchSort"), definition),
        Err(SortRefusal::Collection)
    );
    let entries = Constraints {
        elements: Some(ElementSorts::Entries {
            key: "Id".into(),
            value: "Int".into(),
        }),
        ..Constraints::default()
    };
    assert_eq!(
        resolve_value_sort("Map", &entries, definition),
        Ok(ValueSort::Map {
            sort: "Map".into(),
            symbols: map_symbols(),
            key: Box::new(ValueSort::Token { sort: "Id".into() }),
            value: Box::new(ValueSort::Int),
            text: None,
        })
    );
    assert_eq!(
        resolve_value_sort("Map", &elements("Int"), definition),
        Err(SortRefusal::Collection)
    );
    assert_eq!(
        resolve_value_sort("Set", &entries, definition),
        Err(SortRefusal::Collection)
    );
}

/// Every sort of the IMP definition whose head carries a hook resolves to a sort with a
/// generator or is refused with `NoGenerator` (or `Collection`, for a collection without
/// element sorts); none resolves to a data sort.
#[test]
fn every_hooked_sort_has_a_generator_or_is_refused() {
    let definition = &imp().backend;
    let mut seen = BTreeMap::new();
    for (name, info) in definition.sorts() {
        let Some(hook) = info.hook.clone() else {
            continue;
        };
        if !info.parameters.is_empty() {
            continue;
        }
        let Some(k_name) = name.strip_prefix("Sort") else {
            continue;
        };
        let result = resolve_value_sort(k_name, &Constraints::default(), definition);
        assert!(
            matches!(
                result,
                Ok(ValueSort::Int | ValueSort::Bool | ValueSort::String | ValueSort::Bytes)
                    | Err(SortRefusal::NoGenerator | SortRefusal::Collection)
            ),
            "{name} (hook {hook}) resolves to {result:?}"
        );
        seen.insert(hook, result);
    }
    assert!(
        seen.contains_key("INT.Int") && seen.contains_key("MAP.Map"),
        "{seen:?}"
    );
}

#[test]
fn check_constraints_refuses_violations() {
    let ok = |value: Value, sort: ValueSort, constraints: Constraints| {
        check_constraints(&value, &sort, &constraints)
    };
    assert!(ok(Value::Int(int(3)), ValueSort::Int, range(Some(0), Some(3))).is_ok());
    assert!(ok(Value::Int(int(4)), ValueSort::Int, range(Some(0), Some(3))).is_err());
    assert!(ok(Value::Int(int(-1)), ValueSort::Int, range(Some(0), None)).is_err());
    assert!(ok(Value::Bool(true), ValueSort::Int, Constraints::default()).is_err());
    let mint = |value: u32, width: u32| Value::MInt {
        width,
        value: BigUint::from(value),
    };
    assert!(
        ok(
            mint(255, 8),
            ValueSort::MInt { width: 8 },
            Constraints::default()
        )
        .is_ok()
    );
    assert!(
        ok(
            mint(256, 8),
            ValueSort::MInt { width: 8 },
            Constraints::default()
        )
        .is_err()
    );
    assert!(
        ok(
            mint(1, 16),
            ValueSort::MInt { width: 8 },
            Constraints::default()
        )
        .is_err()
    );
    assert!(
        ok(
            mint(9, 8),
            ValueSort::MInt { width: 8 },
            range(Some(0), Some(8))
        )
        .is_err()
    );
    assert!(
        ok(
            Value::String("abc".into()),
            ValueSort::String,
            length(None, Some(3))
        )
        .is_ok()
    );
    assert!(
        ok(
            Value::String("\u{e9}\u{e9}".into()),
            ValueSort::String,
            length(Some(2), Some(2))
        )
        .is_ok(),
        "a String's length counts code points"
    );
    assert!(
        ok(
            Value::Bytes(vec![1, 2, 3, 4]),
            ValueSort::Bytes,
            length(None, Some(3))
        )
        .is_err()
    );
    let choices = Constraints {
        choices: Some(vec![Value::Int(int(1))]),
        ..Constraints::default()
    };
    assert!(ok(Value::Int(int(1)), ValueSort::Int, choices.clone()).is_ok());
    assert!(ok(Value::Int(int(2)), ValueSort::Int, choices).is_err());
}

#[test]
fn check_constraints_refuses_ill_formed_collections() {
    let ok = |value: Value, sort: ValueSort, constraints: Constraints| {
        check_constraints(&value, &sort, &constraints)
    };
    let list = ValueSort::List {
        sort: "List".into(),
        symbols: list_symbols(),
        element: Box::new(ValueSort::Int),
        text: None,
    };
    assert!(
        ok(
            Value::List(vec![Value::Int(int(1)), Value::Int(int(1))]),
            list.clone(),
            length(None, Some(2))
        )
        .is_ok()
    );
    assert!(
        ok(
            Value::List(vec![Value::Bool(true)]),
            list,
            Constraints::default()
        )
        .is_err()
    );
    let set = ValueSort::Set {
        sort: "Set".into(),
        symbols: set_symbols(),
        element: Box::new(ValueSort::Int),
        text: None,
    };
    assert!(
        ok(
            Value::Set(vec![Value::Int(int(2)), Value::Int(int(1))]),
            set.clone(),
            Constraints::default()
        )
        .is_err(),
        "a Set's elements are sorted and distinct"
    );
    assert!(
        ok(
            Value::Set(vec![Value::Int(int(1)), Value::Int(int(2))]),
            set,
            Constraints::default()
        )
        .is_ok()
    );
    let map = ValueSort::Map {
        sort: "Map".into(),
        symbols: map_symbols(),
        key: Box::new(ValueSort::Int),
        value: Box::new(ValueSort::Bool),
        text: None,
    };
    assert!(
        ok(
            Value::Map(vec![
                (Value::Int(int(1)), Value::Bool(true)),
                (Value::Int(int(1)), Value::Bool(false))
            ]),
            map,
            Constraints::default()
        )
        .is_err(),
        "a Map's keys are distinct"
    );
}
