//! Tests of collection and data-sort values (FZ-09), their K text (FZ-G6), renamed builtins, and
//! the FZ-03 review items folded into the values module.
//!
//! Definitions: IMP, LEDGER and VALUES (`values/test_definition.rs`). "Parses back" means: the
//! printed text, read by the frontend as the configuration assembler reads a value of the sort,
//! is the value's KORE ([`to_kore`]), and [`parse_k_text`] gives the value back; the assembler
//! tests also find that KORE in a configuration assembled by the frontend's public
//! `ConfigurationAssembler` from the printed text.

use k_rust::{
    k_rust_backend::{externalize, term::Sort as BackendSort},
    kore::{ast::Pattern, walk},
};
use num_bigint::{BigInt, BigUint};

use super::{
    ArgumentSort, Constraints, ElementSorts, GenerationBounds, LengthRange, MAX_GENERATED_LENGTH,
    Value, ValueSort, check_constraints,
    generator::{Generator, ValueRng},
    print::{parse_k_text, print_k_text, to_kore},
    resolve_value_sort,
    term::second_value,
    test_definition::{TestDefinition, imp, ledger, values},
    text::TextSyntax,
};
use crate::error::SortRefusal;

// ------------------------------------------------------------------------------------------
// Helpers.

fn none() -> Constraints {
    Constraints::default()
}

fn elements(element: &str) -> Constraints {
    Constraints {
        elements: Some(ElementSorts::Elements {
            element: element.into(),
        }),
        ..Constraints::default()
    }
}

fn entries(key: &str, value: &str) -> Constraints {
    Constraints {
        elements: Some(ElementSorts::Entries {
            key: key.into(),
            value: value.into(),
        }),
        ..Constraints::default()
    }
}

fn int(value: i64) -> Value {
    Value::Int(BigInt::from(value))
}

/// VALUES's syntax with its program sorts excluded, as the hole-sort rule excludes them.
fn values_syntax() -> TextSyntax {
    values().text_syntax(&["Pgm", "Stmt"])
}

fn resolve(
    definition: &TestDefinition,
    syntax: &TextSyntax,
    sort: &str,
    c: &Constraints,
) -> ValueSort {
    syntax
        .resolve(sort, c, &definition.backend)
        .unwrap_or_else(|refusal| panic!("{sort}: {refusal:?}"))
}

/// `count` draws of each of four seeds, each followed by up to `shrinks` alternating simplify
/// and complicate steps; every value seen.
fn draws(
    sort: &ValueSort,
    constraints: &Constraints,
    bounds: &GenerationBounds,
    count: usize,
    shrinks: usize,
) -> Vec<Value> {
    let generator = Generator::new(sort, constraints, bounds)
        .unwrap_or_else(|error| panic!("{sort:?}: {error}"));
    let mut seen = Vec::new();
    for byte in [1u8, 2, 3, 4] {
        let mut rng = ValueRng::from_seed([byte; 32]);
        for _ in 0..count {
            let mut tree = generator.generate(&mut rng);
            seen.push(tree.current());
            for step in 0..shrinks {
                let moved = if step % 3 == 2 {
                    tree.complicate()
                } else {
                    tree.simplify()
                };
                if !moved {
                    break;
                }
                seen.push(tree.current());
            }
        }
    }
    seen
}

/// The number of constructor applications on the longest path of `value`.
fn height(value: &Value) -> u32 {
    match value {
        Value::Apply { arguments, .. } => 1 + arguments.iter().map(height).max().unwrap_or(0),
        Value::List(items) | Value::Set(items) => items.iter().map(height).max().unwrap_or(0),
        Value::Map(entries) => entries
            .iter()
            .map(|(key, value)| height(key).max(height(value)))
            .max()
            .unwrap_or(0),
        _ => 0,
    }
}

fn contains(haystack: &Pattern, needle: &Pattern) -> bool {
    haystack == needle
        || walk::children(haystack)
            .into_iter()
            .any(|child| contains(child, needle))
}

/// The K name of a resolved sort (the name the frontend reads it at).
fn k_name(sort: &ValueSort) -> &str {
    match sort {
        ValueSort::List { sort, .. }
        | ValueSort::Set { sort, .. }
        | ValueSort::Map { sort, .. }
        | ValueSort::Data { sort, .. }
        | ValueSort::Renamed { sort, .. } => sort,
        _ => unreachable!("only collection, data and renamed sorts are read here"),
    }
}

/// Print `value`, read the text back as the assembler reads a value of the sort, and require
/// the value's KORE and the value itself back.
fn assert_parses_back(syntax: &TextSyntax, value: &Value, sort: &ValueSort) -> String {
    let text = print_k_text(value, sort).unwrap_or_else(|error| panic!("{value:?}: {error:?}"));
    let kore = to_kore(value, sort).unwrap();
    let read = syntax
        .parse(&text, k_name(sort))
        .unwrap_or_else(|error| panic!("{value:?} printed as `{text}`: {error}"));
    assert_eq!(read, kore, "`{text}` reads back as other KORE");
    assert_eq!(
        parse_k_text(&text, sort).as_ref(),
        Ok(value),
        "`{text}` reads back as another value"
    );
    text
}

fn constructor_symbols(sort: &ValueSort) -> Vec<String> {
    let ValueSort::Data { table, .. } = sort else {
        panic!("{sort:?} is not a data sort");
    };
    table.sorts[0]
        .constructors
        .iter()
        .map(|constructor| constructor.symbol.clone())
        .collect()
}

// ------------------------------------------------------------------------------------------
// FZ-09: constructor enumeration, exclusions and inhabitation.

#[test]
fn data_tables_follow_the_exclusions_and_inhabitation() {
    let definition = values();
    let syntax = values_syntax();
    // `hold(Stmt)` enters a program sort, `named(Id, Int)` a token sort, `mk` is a function and
    // `loop(Loop)` is never inhabited: only `anon(Int)` is a choice.
    let holder = resolve(definition, &syntax, "Holder", &none());
    assert_eq!(constructor_symbols(&holder), ["Lblanon"]);
    // Without the program sorts excluded, `Stmt` is a data sort (`skip`) and `hold` a choice.
    let unexcluded = resolve_value_sort("Holder", &none(), &definition.backend).unwrap();
    assert_eq!(constructor_symbols(&unexcluded), ["Lblanon", "Lblhold"]);

    assert_eq!(
        syntax.resolve("Loop", &none(), &definition.backend),
        Err(SortRefusal::NoGenerator)
    );
    assert_eq!(
        syntax.resolve("Stmt", &none(), &definition.backend),
        Err(SortRefusal::ProgramSyntax)
    );
    assert_eq!(
        syntax.resolve("Pgm", &none(), &definition.backend),
        Err(SortRefusal::ProgramSyntax)
    );

    // Subsorts with constructors: each is injected from its own result sort.
    let shape = resolve(definition, &syntax, "Shape", &none());
    let ValueSort::Data { table, .. } = &shape else {
        unreachable!()
    };
    let results = table.sorts[0]
        .constructors
        .iter()
        .map(|constructor| {
            (
                constructor.symbol.as_str(),
                constructor.result_kore_sort.as_str(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        results,
        [
            ("Lblcircle", "SortCircle"),
            ("Lblsquare", "SortSquare"),
            ("LblunitSquare", "SortSquare")
        ]
    );
    assert_eq!(table.sorts[0].height, Some(1));

    // Builtin subsorts and no constructor.
    let val = resolve(definition, &syntax, "Val", &none());
    let ValueSort::Data { table, .. } = &val else {
        unreachable!()
    };
    assert_eq!(table.sorts[0].height, Some(0));
    assert!(table.sorts[0].constructors.is_empty());
    assert_eq!(
        table.sorts[0].subsorts,
        [
            ArgumentSort::Value(ValueSort::Bool),
            ArgumentSort::Value(ValueSort::Int),
            ArgumentSort::Value(ValueSort::String)
        ]
    );

    // A collection argument without element sorts: only its empty collection.
    let account = resolve(definition, &syntax, "Account", &none());
    let ValueSort::Data { table, .. } = &account else {
        unreachable!()
    };
    let arguments = &table.sorts[0].constructors[0].arguments;
    assert_eq!(arguments[0], ArgumentSort::Value(ValueSort::Int));
    assert!(
        matches!(&arguments[1], ArgumentSort::Empty(empty) if empty.symbols.kore_sort == "SortMap")
    );

    // Recursion: `leaf` has height 1, `node` height 2, and the sort height 1.
    let tree = resolve(definition, &syntax, "Tree", &none());
    let ValueSort::Data { table, .. } = &tree else {
        unreachable!()
    };
    let heights = table.sorts[0]
        .constructors
        .iter()
        .map(|constructor| (constructor.symbol.as_str(), constructor.height))
        .collect::<Vec<_>>();
    assert_eq!(heights, [("Lblleaf", Some(1)), ("Lblnode", Some(2))]);
}

#[test]
fn a_hole_at_a_program_sort_is_refused() {
    // The hole-sort rule's exclusions reach `TextSyntax::resolve`: a program sort, `K` and
    // `KItem` are refused, and a data sort never draws a program term as an argument.
    let ledger = ledger();
    let syntax = ledger.text_syntax(&["Pgm"]);
    assert_eq!(
        syntax.resolve("Pgm", &none(), &ledger.backend),
        Err(SortRefusal::ProgramSyntax)
    );
    assert_eq!(
        syntax.resolve("KItem", &none(), &ledger.backend),
        Err(SortRefusal::Computation)
    );
    assert!(syntax.resolve("Tx", &none(), &ledger.backend).is_ok());
    let definition = values();
    let holder = resolve(definition, &values_syntax(), "Holder", &none());
    for value in draws(&holder, &none(), &GenerationBounds::default(), 50, 4) {
        assert!(
            matches!(&value, Value::Apply { symbol, .. } if symbol == "Lblanon"),
            "{value:?}"
        );
    }
}

#[test]
fn generated_data_values_are_well_sorted_and_inhabited() {
    let definition = values();
    let syntax = values_syntax();
    let bounds = GenerationBounds::default();
    for name in [
        "Shape", "Rec", "Pair", "Wrapper", "Account", "Tree", "Val", "Holder",
    ] {
        let sort = resolve(definition, &syntax, name, &none());
        let drawn = draws(&sort, &none(), &bounds, 40, 6);
        for value in &drawn {
            check_constraints(value, &sort, &none())
                .unwrap_or_else(|error| panic!("{name}: {value:?}: {error}"));
            assert!(height(value) <= bounds.depth, "{name}: {value:?}");
            assert_parses_back(&syntax, value, &sort);
        }
        let distinct = drawn
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        assert!(distinct > 1, "{name} draws a single value");
    }
}

#[test]
fn recursion_terminates_under_the_depth_bound() {
    let definition = values();
    let syntax = values_syntax();
    let tree = resolve(definition, &syntax, "Tree", &none());
    let rec = resolve(definition, &syntax, "Rec", &none());
    for depth in 0..=6 {
        let bounds = GenerationBounds {
            depth,
            ..GenerationBounds::default()
        };
        if depth == 0 {
            assert!(Generator::new(&tree, &none(), &bounds).is_err());
            continue;
        }
        let drawn = draws(&tree, &none(), &bounds, 50, 6);
        assert!(drawn.iter().all(|value| height(value) <= depth));
        assert_eq!(
            drawn.iter().map(height).max(),
            Some(depth),
            "depth {depth} is reached"
        );
        // `rec` needs a tree below it.
        assert_eq!(Generator::new(&rec, &none(), &bounds).is_ok(), depth >= 2);
    }
    // Shrinking a tree to the end gives the least value: the first constructor at height 1
    // applied to the least integer.
    let generator = Generator::new(&tree, &none(), &GenerationBounds::default()).unwrap();
    let mut rng = ValueRng::from_seed([9; 32]);
    for _ in 0..20 {
        let mut shrinkable = generator.generate(&mut rng);
        while shrinkable.simplify() {}
        assert_eq!(
            shrinkable.current(),
            Value::Apply {
                symbol: "Lblleaf".into(),
                arguments: vec![int(0)]
            }
        );
    }
}

#[test]
fn collections_draw_distinct_elements_without_failing() {
    let definition = values();
    let syntax = values_syntax();
    let bounds = GenerationBounds::default();
    let set_of = |element: &str, length: Option<LengthRange>| {
        let constraints = Constraints {
            length,
            ..elements(element)
        };
        (
            resolve(definition, &syntax, "Set", &constraints),
            constraints,
        )
    };
    // Bool has two values: at least three distinct ones is refused, and lengths are clamped.
    let (set, constraints) = set_of(
        "Bool",
        Some(LengthRange {
            min: Some(3),
            max: None,
        }),
    );
    assert!(Generator::new(&set, &constraints, &bounds).is_err());
    let (set, constraints) = set_of("Bool", None);
    for value in draws(&set, &constraints, &bounds, 50, 6) {
        let Value::Set(items) = &value else { panic!() };
        assert!(items.len() <= 2);
        check_constraints(&value, &set, &constraints).unwrap();
    }
    // MInt{8} has 256 values: a set of at least 200 is a subsequence of them.
    let wide = Some(LengthRange {
        min: Some(200),
        max: Some(256),
    });
    let (set, constraints) = set_of("MInt{8}", wide);
    for value in draws(&set, &constraints, &bounds, 10, 6) {
        check_constraints(&value, &set, &constraints).unwrap();
    }
    // Int has more values than matter: proptest's btree_set.
    let (set, constraints) = set_of(
        "Int",
        Some(LengthRange {
            min: Some(5),
            max: Some(8),
        }),
    );
    for value in draws(&set, &constraints, &bounds, 20, 6) {
        check_constraints(&value, &set, &constraints).unwrap();
        assert_parses_back(&syntax, &value, &set);
    }
    // Map keys are distinct, and data elements print and parse back inside collections.
    let map = resolve(definition, &syntax, "Map", &entries("Bool", "Shape"));
    for value in draws(&map, &none(), &bounds, 30, 6) {
        let Value::Map(entries) = &value else {
            panic!()
        };
        assert!(entries.len() <= 2);
        assert_parses_back(&syntax, &value, &map);
    }
    let list = resolve(definition, &syntax, "List", &elements("Tree"));
    for value in draws(&list, &none(), &bounds, 30, 6) {
        assert_parses_back(&syntax, &value, &list);
    }
}

// ------------------------------------------------------------------------------------------
// FZ-G6: printed values parse back, and appear in assembled configurations.

#[test]
fn values_print_through_their_productions_on_one_line() {
    let definition = values();
    let syntax = values_syntax();
    let cases = [
        (
            "Shape",
            none(),
            Value::Apply {
                symbol: "Lblcircle".into(),
                arguments: vec![int(-5)],
            },
            "circle ( -5 )",
        ),
        (
            "Pair",
            none(),
            Value::Apply {
                symbol: "Lblpair".into(),
                arguments: vec![int(1), Value::String("x".into())],
            },
            "1 & \"x\"",
        ),
        (
            "Account",
            none(),
            Value::Apply {
                symbol: "Lblaccount".into(),
                arguments: vec![int(3), Value::Map(Vec::new())],
            },
            "account ( 3 , .Map )",
        ),
        (
            "List",
            elements("Int"),
            Value::List(vec![int(1), int(2), int(3)]),
            "ListItem ( 1 ) ListItem ( 2 ) ListItem ( 3 )",
        ),
        (
            "Map",
            entries("Int", "String"),
            Value::Map(vec![
                (int(1), Value::String("a".into())),
                (int(2), Value::String("b".into())),
            ]),
            "1 |-> \"a\" 2 |-> \"b\"",
        ),
    ];
    for (name, constraints, value, expected) in cases {
        let sort = resolve(definition, &syntax, name, &constraints);
        assert_eq!(assert_parses_back(&syntax, &value, &sort), expected);
    }
}

#[test]
fn ledger_values_round_trip_through_the_assembler() {
    let ledger = ledger();
    let syntax = ledger.text_syntax(&["Pgm"]);
    let bounds = GenerationBounds::default();
    let tx = resolve(ledger, &syntax, "Tx", &none());
    let account = resolve(ledger, &syntax, "Account", &none());
    assert_eq!(constructor_symbols(&tx), ["Lblnoop", "Lbltransfer"]);
    for value in draws(&tx, &none(), &bounds, 30, 4) {
        let text = assert_parses_back(&syntax, &value, &tx);
        let configuration = ledger
            .assemble("settle", &[("TX", &text)])
            .unwrap_or_else(|error| panic!("`{text}`: {error}"));
        assert!(
            contains(&configuration, &to_kore(&value, &tx).unwrap()),
            "`{text}` is not in the configuration"
        );
    }
    for value in draws(&account, &none(), &bounds, 30, 4) {
        assert_parses_back(&syntax, &value, &account);
    }
}

#[test]
fn values_round_trip_through_the_assembler() {
    let definition = values();
    let syntax = values_syntax();
    let bounds = GenerationBounds::default();
    let holes = [
        ("SHAPE", "Shape", none()),
        ("REC", "Rec", none()),
        ("PAIR", "Pair", none()),
        ("WRAPPER", "Wrapper", none()),
        ("ACCOUNT", "Account", none()),
        ("LIST", "List", elements("Shape")),
        ("SET", "Set", elements("Int")),
        ("MAP", "Map", entries("Int", "Val")),
    ];
    let sorts = holes
        .iter()
        .map(|(_, name, constraints)| resolve(definition, &syntax, name, constraints))
        .collect::<Vec<_>>();
    let generators = sorts
        .iter()
        .map(|sort| Generator::new(sort, &none(), &bounds).unwrap())
        .collect::<Vec<_>>();
    let mut rng = ValueRng::from_seed([5; 32]);
    for _ in 0..25 {
        let drawn = generators
            .iter()
            .map(|generator| generator.generate(&mut rng).current())
            .collect::<Vec<_>>();
        let texts = drawn
            .iter()
            .zip(&sorts)
            .map(|(value, sort)| print_k_text(value, sort).unwrap())
            .collect::<Vec<_>>();
        let bindings = holes
            .iter()
            .zip(&texts)
            .map(|((variable, _, _), text)| (*variable, text.as_str()))
            .collect::<Vec<_>>();
        let configuration = definition
            .assemble("run", &bindings)
            .unwrap_or_else(|error| panic!("{bindings:?}: {error}"));
        for ((value, sort), text) in drawn.iter().zip(&sorts).zip(&texts) {
            assert!(
                contains(&configuration, &to_kore(value, sort).unwrap()),
                "`{text}` ({value:?}) is not in the configuration"
            );
        }
    }
}

#[test]
fn imp_values_print_and_parse_back() {
    let imp = imp();
    let syntax = imp.text_syntax(&["Pgm", "Stmt", "AExp", "BExp", "Block", "Ids"]);
    let bounds = GenerationBounds::default();
    for (name, constraints) in [
        ("KResult", none()),
        ("Map", entries("Int", "Int")),
        ("Map", entries("Int", "Bool")),
        ("Set", elements("Int")),
        ("Set", elements("KResult")),
    ] {
        let sort = resolve(imp, &syntax, name, &constraints);
        for value in draws(&sort, &none(), &bounds, 30, 4) {
            assert_parses_back(&syntax, &value, &sort);
        }
    }
}

#[test]
fn anchors_of_collection_and_data_sorts_are_read() {
    let ledger = ledger();
    let syntax = ledger.text_syntax(&["Pgm"]);
    let tx = resolve(ledger, &syntax, "Tx", &none());
    let anchor = parse_k_text("transfer(30, 1)", &tx).unwrap();
    assert_eq!(
        anchor,
        Value::Apply {
            symbol: "Lbltransfer".into(),
            arguments: vec![int(30), int(1)],
        }
    );
    let second = second_value(&anchor, &tx).unwrap();
    assert_ne!(second, anchor);
    check_constraints(&second, &tx, &none()).unwrap();
    assert!(parse_k_text("transfer(30)", &tx).is_err());
    let noop = parse_k_text("noop", &tx).unwrap();
    assert!(second_value(&noop, &tx).is_some_and(|other| other != noop));

    let definition = values();
    let syntax = values_syntax();
    let set = resolve(definition, &syntax, "Set", &elements("Int"));
    // The value's order, whatever order the text lists the elements in.
    assert_eq!(
        parse_k_text("SetItem(2) SetItem(1)", &set),
        Ok(Value::Set(vec![int(1), int(2)]))
    );
    let map = resolve(definition, &syntax, "Map", &entries("Int", "Val"));
    let empty = parse_k_text(".Map", &map).unwrap();
    assert_eq!(empty, Value::Map(Vec::new()));
    let one = second_value(&empty, &map).unwrap();
    assert_eq!(one, Value::Map(vec![(int(0), Value::Bool(false))]));
    let shape = resolve(definition, &syntax, "Shape", &none());
    let square = parse_k_text("square(3, true)", &shape).unwrap();
    assert_eq!(
        to_kore(&square, &shape).unwrap(),
        syntax.parse("square(3, true)", "Shape").unwrap()
    );
}

// ------------------------------------------------------------------------------------------
// Renamed builtins and MInt (FZ-03 review should-fix 2), against k-rust's own domain values.

#[test]
fn renamed_hooked_sorts_resolve_with_their_kore_sort() {
    let definition = values();
    let syntax = values_syntax();
    let my_int = resolve_value_sort("MyInt", &none(), &definition.backend).unwrap();
    assert_eq!(
        my_int,
        ValueSort::Renamed {
            sort: "MyInt".into(),
            kore_sort: "SortMyInt".into(),
            base: Box::new(ValueSort::Int),
        }
    );
    for value in draws(&my_int, &none(), &GenerationBounds::default(), 30, 4) {
        let Value::Int(number) = &value else { panic!() };
        let expected = externalize::term(
            &definition
                .backend
                .domain_value(
                    BackendSort::application("SortMyInt", Vec::new()),
                    number.to_string(),
                )
                .unwrap(),
        );
        assert_eq!(to_kore(&value, &my_int).unwrap(), expected);
        let text = print_k_text(&value, &my_int).unwrap();
        assert_eq!(syntax.parse(&text, "MyInt").unwrap(), expected);
        assert_eq!(parse_k_text(&text, &my_int), Ok(value));
    }
}

#[test]
fn mint_resolves_and_matches_the_backend() {
    let definition = values();
    let syntax = values_syntax();
    let mint = resolve_value_sort("MInt{8}", &none(), &definition.backend).unwrap();
    assert_eq!(mint, ValueSort::MInt { width: 8 });
    let sort = BackendSort::application(
        "SortMInt",
        vec![BackendSort::application("Sort8", Vec::new())],
    );
    let value = Value::MInt {
        width: 8,
        value: BigUint::from(200u32),
    };
    let kore = to_kore(&value, &mint).unwrap();
    for spelling in ["200p8", "-56p8"] {
        let backend = externalize::term(
            &definition
                .backend
                .domain_value(sort.clone(), spelling)
                .unwrap(),
        );
        assert_eq!(kore, backend, "{spelling}");
        assert_eq!(parse_k_text(spelling, &mint).as_ref(), Ok(&value));
        if let Some(read) = frontend_with_inference(&syntax, spelling, "MInt{8}") {
            assert_eq!(read, kore, "{spelling}");
        }
    }
    assert_eq!(print_k_text(&value, &mint).unwrap(), "200p8");
    // An MInt inside a data value: printed through `w8`'s production.
    let word = resolve(definition, &syntax, "Word", &none());
    for drawn in draws(&mint, &none(), &GenerationBounds::default(), 30, 4)
        .into_iter()
        .chain(draws(&word, &none(), &GenerationBounds::default(), 10, 2))
    {
        let sort = if matches!(drawn, Value::Apply { .. }) {
            &word
        } else {
            &mint
        };
        let text = print_k_text(&drawn, sort).unwrap();
        if let Some(read) = frontend_with_inference(&syntax, &text, k_name_or_mint(sort)) {
            assert_eq!(read, to_kore(&drawn, sort).unwrap(), "`{text}`");
            assert_eq!(parse_k_text(&text, sort).as_ref(), Ok(&drawn));
        }
    }
}

fn k_name_or_mint(sort: &ValueSort) -> &str {
    match sort {
        ValueSort::MInt { .. } => "MInt{8}",
        other => k_name(other),
    }
}

/// The frontend's reading of `text` at `sort`, or `None` when the frontend needs Z3 to infer the
/// parametric sort `MInt{8}`, which only a build with `z3-inference` has.
fn frontend_with_inference(syntax: &TextSyntax, text: &str, sort: &str) -> Option<Pattern> {
    match syntax.parse(text, sort) {
        Ok(pattern) => Some(pattern),
        Err(error) if error.contains("Z3InferenceRequired") && !cfg!(feature = "z3") => {
            eprintln!("`{text}` at {sort} needs Z3 inference; checked in the z3 build");
            None
        }
        Err(error) => panic!("`{text}` at {sort}: {error}"),
    }
}

// ------------------------------------------------------------------------------------------
// FZ-03 review: caps, complicate, canonical hex.

#[test]
fn huge_constraints_and_bounds_are_capped() {
    let bounds = GenerationBounds::default();
    let huge = Constraints {
        length: Some(LengthRange {
            min: None,
            max: Some(1_000_000_000_000),
        }),
        ..Constraints::default()
    };
    let generator = Generator::new(&ValueSort::Bytes, &huge, &bounds).unwrap();
    let mut rng = ValueRng::from_seed([1; 32]);
    for _ in 0..3 {
        let Value::Bytes(bytes) = generator.generate(&mut rng).current() else {
            panic!()
        };
        assert!(bytes.len() as u64 <= MAX_GENERATED_LENGTH);
    }
    let too_long = Constraints {
        length: Some(LengthRange {
            min: Some(MAX_GENERATED_LENGTH + 1),
            max: None,
        }),
        ..Constraints::default()
    };
    assert!(Generator::new(&ValueSort::String, &too_long, &bounds).is_err());
    for bad in [
        GenerationBounds {
            int_bits: u32::MAX,
            ..bounds
        },
        GenerationBounds {
            length: 1_000_000_000_000,
            ..bounds
        },
        GenerationBounds {
            depth: 1_000,
            ..bounds
        },
    ] {
        assert!(
            Generator::new(&ValueSort::Int, &none(), &bad).is_err(),
            "{bad:?}"
        );
    }
}

#[test]
fn complicate_before_simplify_returns_false() {
    let generator = Generator::new(&ValueSort::Int, &none(), &GenerationBounds::default()).unwrap();
    let mut rng = ValueRng::from_seed([3; 32]);
    for _ in 0..50 {
        let mut tree = generator.generate(&mut rng);
        let before = tree.current();
        assert!(!tree.complicate());
        assert_eq!(tree.current(), before);
    }
}

#[test]
fn text_syntax_is_shared_across_threads() {
    fn shared<T: Send + Sync>() {}
    shared::<TextSyntax>();
    shared::<ValueSort>();
}

#[test]
fn hex_bytes_require_two_hex_digits() {
    assert!(serde_json::from_str::<Value>(r#"{"bytes":"+f+f"}"#).is_err());
    assert_eq!(
        serde_json::from_str::<Value>(r#"{"bytes":"0f0f"}"#).unwrap(),
        Value::Bytes(vec![15, 15])
    );
}
