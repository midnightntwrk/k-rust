//! The condition of an implication names the request's variables as the request spells them,
//! and the check's local names apart from them.

use k_rust::backend::{Backend, BackendOptions, implication::cli_output};
use k_rust_backend::definition::Admission;
use k_rust_kore::kore::parser::parse_pattern;

const DEFINITION: &str = r#"[]
module TEST
  sort SortK{} []
  symbol value{}() : SortK{} [constructor{}()]
endmodule []"#;

fn implication_output(antecedent: &str, consequent: &str) -> serde_json::Value {
    let mut backend = Backend::new(DEFINITION, "TEST", BackendOptions::default()).unwrap();
    let antecedent = parse_pattern(antecedent).unwrap();
    let consequent = parse_pattern(consequent).unwrap();
    let (verdict, sort) = backend
        .implies_kore(None, &antecedent, &consequent, Admission::Verified)
        .unwrap();
    serde_json::from_str(&cli_output(&antecedent, &consequent, &sort, verdict).unwrap()).unwrap()
}

/// A request variable keeps its name, even when it is spelled like a local name of the check
/// (`X-bexists0`, the printed `X!exists0`); a local name of the check prints as the consequent
/// binder it renames.
#[test]
fn implies_keeps_request_names_and_restores_only_local_names() {
    let cases = [
        (
            "X-bexists0:SortK{}",
            r#"\exists{SortK{}}(X:SortK{}, X:SortK{})"#,
            ["X-bexists0", "X"],
        ),
        (
            "value{}()",
            r#"\exists{SortK{}}(X-bexists0:SortK{}, X-bexists0:SortK{})"#,
            ["X-bexists0", "value"],
        ),
        (
            "value{}()",
            r#"\exists{SortK{}}(X:SortK{}, X:SortK{})"#,
            ["X", "value"],
        ),
    ];
    for (antecedent, consequent, expected) in cases {
        let output = implication_output(antecedent, consequent);
        assert_eq!(output["status"], "valid", "{output:#}");
        let substitution = &output["condition"]["substitution"]["term"];
        assert_eq!(substitution["tag"], "Equals", "{output:#}");
        let actual = [
            substitution["first"]["name"].as_str().unwrap(),
            substitution["second"]["name"].as_str().unwrap(),
        ];
        for name in expected {
            assert!(actual.contains(&name), "{output:#}");
        }
    }
}

const TWO_VALUES: &str = r#"[]
module TEST
  sort SortK{} []
  symbol a{}() : SortK{} [constructor{}(), functional{}()]
  symbol b{}() : SortK{} [constructor{}(), functional{}()]
  axiom{} \or{SortK{}}(a{}(), b{}()) [constructor{}()]
endmodule []"#;

fn two_values_implication(antecedent: &str, consequent: &str) -> (String, serde_json::Value) {
    let mut backend = Backend::new(TWO_VALUES, "TEST", BackendOptions::default()).unwrap();
    let antecedent = parse_pattern(antecedent).unwrap();
    let consequent = parse_pattern(consequent).unwrap();
    let (verdict, sort) = backend
        .implies_kore(None, &antecedent, &consequent, Admission::Verified)
        .unwrap();
    let output = cli_output(&antecedent, &consequent, &sort, verdict).unwrap();
    let output: serde_json::Value = serde_json::from_str(&output).unwrap();
    (output["status"].as_str().unwrap().to_owned(), output)
}

/// `\exists X. X /\ \not(\exists W. W = a /\ \not(W = X))` is `\exists X. X /\ X = a`, which
/// `b` does not imply. The inner binder is a request variable, so its spelling cannot matter,
/// even when it is the printed spelling of the check's first local name for `X` (`X!exists0`).
#[test]
fn implies_does_not_let_a_bound_request_name_capture_a_consequent_existential() {
    let consequent = |binder: &str| {
        format!(
            r#"\exists{{SortK{{}}}}(X:SortK{{}}, \and{{SortK{{}}}}(X:SortK{{}},
                \not{{SortK{{}}}}(\exists{{SortK{{}}}}({binder}:SortK{{}},
                    \and{{SortK{{}}}}(\equals{{SortK{{}}, SortK{{}}}}({binder}:SortK{{}}, a{{}}()),
                        \not{{SortK{{}}}}(\equals{{SortK{{}}, SortK{{}}}}({binder}:SortK{{}}, X:SortK{{}})))))))"#
        )
    };
    let (control, _) = two_values_implication("b{}()", &consequent("W"));
    let (spelled, output) = two_values_implication("b{}()", &consequent("X-bexists0"));
    assert_ne!(control, "valid");
    assert_eq!(spelled, control, "{output:#}");
    let (holds, output) = two_values_implication("a{}()", &consequent("X-bexists0"));
    assert_eq!(holds, "valid", "{output:#}");
}

/// A request binder spelled like a local name does not change how the consequent existential
/// prints: the binding of `X` prints as `X`, wherever `X-bexists0` is bound.
#[test]
fn implies_prints_a_consequent_existential_apart_from_bound_request_names() {
    for antecedent in [
        r#"\and{SortK{}}(b{}(), \exists{SortK{}}(X-bexists0:SortK{},
            \equals{SortK{}, SortK{}}(X-bexists0:SortK{}, a{}())))"#,
        r#"\exists{SortK{}}(X-bexists0:SortK{}, b{}())"#,
        r#"\and{SortK{}}(b{}(), \exists{SortK{}}(X-bexists0:SortK{}, \top{SortK{}}()))"#,
    ] {
        let (status, output) =
            two_values_implication(antecedent, r#"\exists{SortK{}}(X:SortK{}, X:SortK{})"#);
        assert_eq!(status, "valid", "{output:#}");
        let substitution = &output["condition"]["substitution"]["term"];
        assert_eq!(substitution["tag"], "Equals", "{output:#}");
        assert_eq!(substitution["first"]["name"], "X", "{output:#}");
        assert_eq!(substitution["second"]["name"], "b", "{output:#}");
    }
}

/// A consequent existential bound to the antecedent variable prints as `antecedent = binder`,
/// whatever the antecedent's spelling.
#[test]
fn implies_orients_an_escaped_antecedent_variable_like_a_plain_one() {
    for antecedent in ["V", "V-b0", "V--1"] {
        for spelled in [
            format!("{antecedent}:SortK{{}}"),
            format!(r#"\exists{{SortK{{}}}}({antecedent}:SortK{{}}, {antecedent}:SortK{{}})"#),
        ] {
            let (status, output) =
                two_values_implication(&spelled, r#"\exists{SortK{}}(Y:SortK{}, Y:SortK{})"#);
            assert_eq!(status, "valid", "{output:#}");
            let substitution = &output["condition"]["substitution"]["term"];
            assert_eq!(substitution["tag"], "Equals", "{output:#}");
            assert_eq!(substitution["first"]["name"], antecedent, "{output:#}");
            assert_eq!(substitution["second"]["name"], "Y", "{output:#}");
        }
    }
}
