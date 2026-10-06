use k_rust::kast::parser;

#[test]
fn rejects_leading_zero_numeral_sorts_in_kast_text() {
    for source in ["08", "MInt{08}", "MInt{MInt{08}}"] {
        let error = parser::parse_sort(source).unwrap_err();
        assert_eq!(
            error.message, "numeral sort 08 is written with a leading zero; a width is spelled 8",
            "{source}"
        );
    }
    for source in ["MInt{8}", "0", "MInt{0}"] {
        assert_eq!(parser::parse_sort(source).unwrap().to_string(), source);
    }
}

#[test]
fn frontend_textual_kast_fixture_round_trips() {
    let source = include_str!("fixtures/kast/kast-data.kast");
    let term = parser::parse_term(source).unwrap();
    let printed = term.to_string();
    assert_eq!(parser::parse_term(&printed).unwrap(), term);
}

#[test]
fn accepts_legacy_spellings_and_double_commas() {
    let modern = parser::parse_term("foo(.KList) ~> .K").unwrap();
    let legacy = parser::parse_term("foo(.::KList) ~> .::K").unwrap();
    assert_eq!(modern, legacy);

    let term = parser::parse_term("foo(X,,Y)").unwrap();
    assert_eq!(term.to_string(), "foo(X,Y)");
}

/// The reader descends once per level of the term or sort it reads, and accepts any depth: a
/// chain of 100,000 applications, a chain of 100,000 rewrites (right-nested, as `=>` reads), and
/// a sort with 100,000 nested parameters are read on a thread of 256 KiB of stack.
#[test]
fn terms_and_sorts_of_any_depth_are_read_on_a_small_stack() {
    const DEPTH: usize = 100_000;
    let applications = format!("{}z(.KList){}", "s(".repeat(DEPTH), ")".repeat(DEPTH));
    let rewrites = format!("{}z(.KList)", "z(.KList) => ".repeat(DEPTH));
    let sort = format!("{}Nat{}", "Box{".repeat(DEPTH), "}".repeat(DEPTH));
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(move || {
            let mut term = &parser::parse_term(&applications).unwrap();
            let mut depth = 0;
            while let k_rust::kast::Term::Apply { arguments, .. } = term
                && let [argument] = arguments.as_slice()
            {
                depth += 1;
                term = argument;
            }
            assert_eq!(depth, DEPTH);
            let mut term = &parser::parse_term(&rewrites).unwrap();
            let mut depth = 0;
            while let k_rust::kast::Term::Rewrite { right, .. } = term {
                depth += 1;
                term = right;
            }
            assert_eq!(depth, DEPTH);
            let mut sort = &parser::parse_sort(&sort).unwrap();
            let mut depth = 0;
            while let [parameter] = sort.parameters.as_slice() {
                depth += 1;
                sort = parameter;
            }
            assert_eq!(depth, DEPTH);
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish");
}
