//! An equation whose map pattern matches one subject in several ways is applied when one of its
//! instances applies (`simplify::scan::scan_instances`): its `requires` is decided on each
//! matching, not on the first one only, and a lower-priority equation fires only when every
//! instance is refuted. A search target that matches one subject in several ways matches it once
//! per way.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    rewrite::Pattern,
    rule::Predicate,
    search::{PatternMatchError, match_disjunction},
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    term::{Sort, Term, Variable},
};

const PRELUDE: &str = r#"
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
    hooked-sort SortC{} [hook{}("MAP.Map"), unit{}(cUnit{}()), element{}(cItem{}()), concat{}(cConcat{}())]
    hooked-symbol cUnit{}() : SortC{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol cItem{}(SortInt{}, SortInt{}) : SortC{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol cConcat{}(SortC{}, SortC{}) : SortC{}
        [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}(), unit{}(cUnit{}())]
    sort SortS{} []
    symbol mk{}(SortInt{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
    symbol f{}(SortC{}) : SortS{} [function{}()]
    symbol g{}(SortC{}) : SortS{} [anywhere{}()]
"#;

const ENTRY: &str = r"cConcat{}(cItem{}(VarK:SortInt{}, VarV:SortInt{}), VarM:SortC{})";

fn int(value: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// P6 of the value-contract review 3, `f(K |-> V M) = mk(1) requires K ==Int key` beside
/// `f(M) = mk(2) [owise]`, and the ceil equation `\ceil(g(K |-> V M)) = \top requires
/// K ==Int key` of the partial equation head `g`.
fn load(key: i64) -> BackendDefinition {
    let requires = format!(
        r#"\equals{{SortBool{{}}, R}}(eqInt{{}}(VarK:SortInt{{}}, {}), \dv{{SortBool{{}}}}("true"))"#,
        int(key)
    );
    let function = |requires: &str, pattern: &str, result: i64, attributes: &str| {
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, \and{{R}}(\in{{SortC{{}}, R}}(X0:SortC{{}}, {pattern}), \top{{R}}())), \equals{{SortS{{}}, R}}(f{{}}(X0:SortC{{}}), \and{{SortS{{}}}}(mk{{}}({}), \top{{SortS{{}}}}()))) [{attributes}]",
            int(result)
        )
    };
    let axioms = [
        function(&requires, ENTRY, 1, ""),
        function(r"\top{R}()", "VarM:SortC{}", 2, "owise{}()"),
        format!(
            r"axiom{{R}} \implies{{R}}({requires}, \equals{{R, R}}(\ceil{{SortS{{}}, R}}(g{{}}({ENTRY})), \and{{R}}(\top{{R}}(), \top{{R}}()))) []"
        ),
    ];
    let source = format!(
        "[] module MAIN {PRELUDE} {} endmodule []",
        axioms.join("\n")
    );
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).unwrap(), &[])
        .expect("the term internalizes")
}

/// The map `{k |-> 0, ...}` over the given keys, each written as a pattern.
fn map(keys: &[&str]) -> String {
    keys.iter()
        .map(|key| format!(r"cItem{{}}({key}, {})", int(0)))
        .reduce(|left, right| format!(r"cConcat{{}}({left}, {right})"))
        .expect("at least one entry")
}

fn evaluate(definition: &BackendDefinition, subject: &str) -> Term {
    simplify(
        definition,
        &term(definition, subject),
        SimplificationOptions::default(),
    )
    .expect("no stop is armed")
    .expect("the simplification succeeds")
    .term
}

fn decide(definition: &BackendDefinition, predicate: &Predicate) -> Predicate {
    simplify_predicate_with_solver(
        definition,
        predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop is armed")
    .expect("the simplification succeeds")
}

/// On `{1 |-> 0, 2 |-> 0}` the instance `K = key` applies for either key, so every model has
/// `f(m) = mk(1)`; for one of the two keys the matcher's first matching refutes the `requires`,
/// which used to pass the equation over and give the `owise` result `mk(2)`. The ceil equation
/// likewise decides `\ceil(g(m))` for either key, where it used to leave it open for one.
#[test]
fn an_equation_applies_when_any_matching_satisfies_its_requires() {
    let one = int(1);
    let two = int(2);
    let subject = map(&[&one, &two]);
    for key in [1, 2] {
        let definition = load(key);
        let applied = format!("f{{}}({subject})");
        assert_eq!(
            evaluate(&definition, &applied),
            term(&definition, &format!("mk{{}}({one})")),
            "key {key}"
        );
        let mk = |value: &str| term(&definition, &format!("mk{{}}({value})"));
        let application = term(&definition, &applied);
        assert_eq!(
            decide(
                &definition,
                &Predicate::Equals(application.clone(), mk(&one))
            ),
            Predicate::True,
            "key {key}"
        );
        assert_eq!(
            decide(&definition, &Predicate::Equals(application, mk(&two))),
            Predicate::False,
            "key {key}"
        );
        let ceil = Predicate::Ceil(term(&definition, &format!("g{{}}({subject})")));
        assert_eq!(decide(&definition, &ceil), Predicate::True, "key {key}");
    }
}

/// When every matching refutes the `requires`, the lower-priority equation applies; when one is
/// undecided and none holds, the application is kept, as for an equation with one matching.
#[test]
fn a_lower_priority_equation_applies_only_when_every_matching_is_refuted() {
    let definition = load(3);
    let subject = map(&[&int(1), &int(2)]);
    assert_eq!(
        evaluate(&definition, &format!("f{{}}({subject})")),
        term(&definition, &format!("mk{{}}({})", int(2)))
    );
    let ceil = Predicate::Ceil(term(&definition, &format!("g{{}}({subject})")));
    assert_eq!(decide(&definition, &ceil), ceil);

    // `{Y |-> 0, 2 |-> 0}` under `requires K ==Int 1`: the matching `K = 2` is refuted, the
    // matching `K = Y` is undecided, so neither equation applies.
    let definition = load(1);
    let applied = format!("f{{}}({})", map(&["VarY:SortInt{}", &int(2)]));
    assert_eq!(evaluate(&definition, &applied), term(&definition, &applied));
    // `{Y |-> 0, 1 |-> 0}`: the matching `K = 1` applies, whatever the other one gives.
    let applied = format!("f{{}}({})", map(&["VarY:SortInt{}", &int(1)]));
    assert_eq!(
        evaluate(&definition, &applied),
        term(&definition, &format!("mk{{}}({})", int(1)))
    );
}

/// A target `K |-> V M` matches the subject `{1 |-> 10, 2 |-> 20, 3 |-> 30}` in three ways, one
/// per entry, each binding `M` to the other two; the subject is an instance of the target under
/// any one of them, so each is a match. Fixing the value leaves one way, a pattern of one entry
/// and no rest none (a refutation, not an undecided match). A subject with a frame of unknown
/// entries is left undecided: the target's entry may lie in the frame on some instances, and a
/// match states every way, so it is not narrowed to the ways the known entries give.
#[test]
fn a_target_that_matches_a_subject_in_several_ways_matches_it_once_per_way() {
    let definition = load(1);
    let subject = |source: &str| Pattern {
        term: term(&definition, source),
        constraints: Vec::new(),
    };
    let entry = |key: i64, value: i64| format!(r"cItem{{}}({}, {})", int(key), int(value));
    let three = format!(
        r"cConcat{{}}({}, cConcat{{}}({}, {}))",
        entry(1, 10),
        entry(2, 20),
        entry(3, 30)
    );
    let int_variable = |name: &str| Variable::new(format!("Var{name}"), Sort::simple("SortInt"));
    let matches = |target: &str, subject: &Pattern| {
        match_disjunction(
            &definition,
            &target_pattern(target, &definition),
            std::slice::from_ref(subject),
        )
        .expect("no stop is armed")
    };
    let found = matches(ENTRY, &subject(&three)).expect("every way is decided");
    let mut ways = found
        .iter()
        .map(|found| {
            assert!(found.constraints.is_empty(), "{found:?}");
            (
                found.substitution[&int_variable("K")].clone(),
                found.substitution[&int_variable("V")].clone(),
            )
        })
        .collect::<Vec<_>>();
    ways.sort();
    let expected = [(1, 10), (2, 20), (3, 30)]
        .map(|(key, value)| (term(&definition, &int(key)), term(&definition, &int(value))));
    assert_eq!(ways, expected);

    let valued = format!(
        r"cConcat{{}}(cItem{{}}(VarK:SortInt{{}}, {}), VarM:SortC{{}})",
        int(20)
    );
    let found = matches(&valued, &subject(&three)).expect("every way is decided");
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(
        found[0].substitution[&int_variable("K")],
        term(&definition, &int(2))
    );

    let closed = r"cItem{}(VarK:SortInt{}, VarV:SortInt{})";
    assert_eq!(matches(closed, &subject(&three)), Ok(Vec::new()));

    let framed = subject(&format!(r"cConcat{{}}({}, VarN:SortC{{}})", entry(1, 10)));
    assert!(
        matches!(
            matches(ENTRY, &framed),
            Err(PatternMatchError::Indeterminate { .. })
        ),
        "{:?}",
        matches(ENTRY, &framed)
    );
}

fn target_pattern(target: &str, definition: &BackendDefinition) -> Pattern {
    Pattern {
        term: term(definition, target),
        constraints: Vec::new(),
    }
}
