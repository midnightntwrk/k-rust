use k_rust::kast::parser;

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
