//! KINK-FINDING-NAMES: a finding of the full critical-pair check is named by its kind, its
//! sentences and a digest of the compiled sentences it is about (`data_term::names`), so that a
//! premise naming it survives every edit that leaves those sentences alone and names nothing
//! once they change.
//!
//! The fixture extends `overloaded-list-owise.kore` with `h : E -> State` over a sort `E` with no
//! element and two equations with different results: the check cannot join them and the ground
//! search finds no input, so the root pair is undecided, a finding a premise can assume.

use k_rust_backend::{
    data_term::{
        DataHeads, Finding,
        names::{
            self, Candidate, FindingName, Given, Refusal, Spelling, canonical, classify, parse,
            respell,
        },
    },
    definition::BackendDefinition,
};
use k_rust_kore::kore::parser::parse_definition;

const FIXTURE: &str = include_str!("../fixtures/overloaded-list-owise.kore");

fn symbol(name: &str) -> String {
    name.to_owned()
}

/// One equation `h(X) = rhs` with the axiom attributes `attributes`; `variable` names `X`.
fn equation(variable: &str, rhs: &str, attributes: &str) -> String {
    format!(
        r#"
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\top{{R}}(), \and{{R}}(\in{{SortE{{}}, R}}(X0:SortE{{}}, {variable}:SortE{{}}), \top{{R}}())),
        \equals{{SortState{{}}, R}}(h{{}}(X0:SortE{{}}), \and{{SortState{{}}}}({rhs}, \top{{SortState{{}}}}())))
        [{attributes}]
"#
    )
}

fn labelled(label: &str, line: u32) -> String {
    format!(
        r#"label{{}}("{label}"), org'Stop'kframework'Stop'attributes'Stop'Location{{}}("Location({line},3,{line},30)"), org'Stop'kframework'Stop'attributes'Stop'Source{{}}("Source(/work/spec.k)")"#
    )
}

/// The fixture with `h`'s declaration (`declaration` its attributes) and `equations`.
fn definition_with(declaration: &str, equations: &[String]) -> BackendDefinition {
    let (head, tail) = FIXTURE.rsplit_once("endmodule").expect("one module");
    let source = format!(
        "{head}
    sort SortE{{}} []
    symbol h{{}}(SortE{{}}) : SortState{{}} [{declaration}]
{}
endmodule{tail}",
        equations.concat()
    );
    BackendDefinition::internalize(
        &parse_definition(&source).expect("parses"),
        "OVERLOADED-LIST-OWISE",
    )
    .expect("loads")
}

fn definition(equations: &[String]) -> BackendDefinition {
    definition_with("function{}(), total{}()", equations)
}

/// The two labelled equations `h-failed` and `h-bound`, the first written at `first_line`.
fn pair(first_line: u32) -> Vec<String> {
    vec![
        equation("V", "failed{}()", &labelled("h-failed", first_line)),
        equation(
            "V",
            "bound{}(one{}())",
            &labelled("h-bound", first_line + 1),
        ),
    ]
}

fn k_name(name: &FindingName) -> String {
    Spelling::k(&symbol).text(name)
}

/// The one finding of `heads` with its name.
fn only(heads: &DataHeads) -> (&Finding, Option<&FindingName>) {
    let named = heads
        .named()
        .map(|(finding, name, _)| (finding, name))
        .collect::<Vec<_>>();
    let [only] = named.as_slice() else {
        panic!("one finding: {:?}", heads.findings());
    };
    *only
}

fn refusal(given: &str, definition: &BackendDefinition) -> Refusal {
    let heads = definition.data_heads();
    let candidates = heads
        .named()
        .map(|(finding, name, _)| Candidate { finding, name })
        .collect::<Vec<_>>();
    classify(given, &candidates, definition, &Spelling::k(&symbol)).expect_err("refused")
}

fn accepted(given: &str, definition: &BackendDefinition) -> usize {
    let heads = definition.data_heads();
    let candidates = heads
        .named()
        .map(|(finding, name, _)| Candidate { finding, name })
        .collect::<Vec<_>>();
    classify(given, &candidates, definition, &Spelling::k(&symbol))
        .unwrap_or_else(|refusal| panic!("{}: {}", refusal.reason(), refusal.detail(given)))
        .len()
}

/// The undecided root pair's name, as a real check prints it.
fn pair_name(definition: &BackendDefinition) -> String {
    let heads = definition.data_heads();
    let (finding, name) = only(&heads);
    assert!(!finding.is_genuine() && !finding.is_decided(), "{finding}");
    k_name(name.expect("named"))
}

/// Test 1 and 2 (backend level): moving the sentences (their `Location`) and renaming their
/// variables leave the name as it is, and the premise still applies.
#[test]
fn moving_or_renaming_a_sentence_leaves_its_name() {
    let before = definition(&pair(7));
    let name = pair_name(&before);
    eprintln!("root pair: {name}");
    assert!(name.starts_with("root:h-bound,h-failed#"), "{name}");
    let moved = definition(&pair(40));
    assert_eq!(pair_name(&moved), name);
    let renamed = definition(&[
        equation("Other", "failed{}()", &labelled("h-failed", 9)),
        equation("Z", "bound{}(one{}())", &labelled("h-bound", 3)),
    ]);
    assert_eq!(pair_name(&renamed), name);
    assert_eq!(accepted(&name, &renamed), 1);
}

/// Test 8: a root pair is read in either order and printed sorted; quotes that are not needed
/// are dropped; every kind round-trips from print to parse.
#[test]
fn a_root_pair_reads_in_either_order_and_every_kind_round_trips() {
    let definition = definition(&pair(7));
    let name = pair_name(&definition);
    let digest = name.rsplit_once('#').expect("a digest").1;
    let reversed = format!("root:h-failed,\"h-bound\"#{digest}");
    assert_eq!(canonical(&reversed).as_deref(), Some(name.as_str()));
    assert_eq!(accepted(&reversed, &definition), 1);
    let hex = "0123456789abcdef0123456789abcdef";
    for text in [
        format!("root:a,b#{hex}"),
        format!("self:a~1#{hex}"),
        format!("inner:a,\"b c\"@1.0#{hex}"),
        format!("hook:id:abc#{hex}"),
        format!("equation:witness:\"f(X) => X\"#{hex}"),
        format!("precondition:MODULE.rule#{hex}"),
        format!("precondition:no-least-common-overload:a:\"b:c\"#{hex}"),
        format!("root:crate::x,overload:\"g,h\":l#{hex}"),
    ] {
        assert!(
            matches!(
                parse(&text),
                Ok(Given::Name {
                    digest: Some(_),
                    ..
                })
            ),
            "{text}"
        );
        assert_eq!(respell(&text, &|_| None).as_deref(), Some(text.as_str()));
        assert_eq!(canonical(&text).as_deref(), Some(text.as_str()));
    }
    // A front end's spelling maps a label both ways.
    let spelled = respell(&name, &|label| {
        (label == "h-bound").then(|| "crate::h_bound".to_owned())
    })
    .expect("a name");
    assert!(
        spelled.starts_with("root:crate::h_bound,h-failed#"),
        "{spelled}"
    );
}

/// Test 3: changing a sentence's right-hand side, its condition, its priority or the declaration
/// of a symbol it applies changes the digest, and the premise is refused as `changed` with the
/// new name; a new subsort of a mentioned sort does not (the digest leaves the sort relations
/// out, so an unrelated sort under `KItem` refuses nothing).
#[test]
fn a_changed_sentence_or_declaration_refuses_the_premise_with_the_new_name() {
    let name = pair_name(&definition(&pair(7)));
    let changed = |definition: &BackendDefinition| {
        let new = pair_name(definition);
        assert_ne!(new, name);
        match refusal(&name, definition) {
            Refusal::Changed { current } => {
                assert_eq!(current.len(), 1);
                assert_eq!(current[0].0, new);
            }
            other => panic!("{other:?}"),
        }
    };
    changed(&definition(&[
        equation("V", "failed{}()", &labelled("h-failed", 7)),
        equation("V", "state{}(matchFailure{}())", &labelled("h-bound", 8)),
    ]));
    let condition = |rhs: &str, attributes: &str| {
        format!(
            r#"
    axiom{{R}} \implies{{R}}(
        \and{{R}}(\equals{{SortBool{{}}, R}}(\dv{{SortBool{{}}}}("true"), \dv{{SortBool{{}}}}("true")), \and{{R}}(\in{{SortE{{}}, R}}(X0:SortE{{}}, V:SortE{{}}), \top{{R}}())),
        \equals{{SortState{{}}, R}}(h{{}}(X0:SortE{{}}), \and{{SortState{{}}}}({rhs}, \top{{SortState{{}}}}())))
        [{attributes}]
"#
        )
    };
    changed(&definition(&[
        equation("V", "failed{}()", &labelled("h-failed", 7)),
        condition("bound{}(one{}())", &labelled("h-bound", 8)),
    ]));
    let priority =
        |label: &str, line: u32| format!("{}, priority{{}}(\"60\")", labelled(label, line));
    changed(&definition(&[
        equation("V", "failed{}()", &priority("h-failed", 7)),
        equation("V", "bound{}(one{}())", &priority("h-bound", 8)),
    ]));
    changed(&definition_with("function{}()", &pair(7)));
    // A subsort of a sort the sentences mention, which they do not read.
    let (head, tail) = FIXTURE.rsplit_once("endmodule").expect("one module");
    let source = format!(
        "{head}
    sort SortE{{}} []
    sort SortF{{}} []
    symbol h{{}}(SortE{{}}) : SortState{{}} [function{{}}(), total{{}}()]
    axiom{{R}} \\exists{{R}}(V:SortState{{}}, \\equals{{SortState{{}}, R}}(V:SortState{{}}, inj{{SortF{{}}, SortState{{}}}}(F:SortF{{}})))
        [subsort{{SortF{{}}, SortState{{}}}}()]
{}
endmodule{tail}",
        pair(7).concat()
    );
    let subsorted = BackendDefinition::internalize(
        &parse_definition(&source).expect("parses"),
        "OVERLOADED-LIST-OWISE",
    )
    .expect("loads");
    assert_eq!(pair_name(&subsorted), name);
}

/// Test 4 and 5 (backend level): swapping two equations' labels, or giving a label to another
/// equation (KRS names a function's branch by its position, so inserting a branch renames the
/// branches after it), refuses the premise as `changed`: never a re-match of another pair.
#[test]
fn a_label_that_moves_to_another_sentence_refuses_the_premise() {
    let name = pair_name(&definition(&pair(7)));
    let swapped = definition(&[
        equation("V", "failed{}()", &labelled("h-bound", 7)),
        equation("V", "bound{}(one{}())", &labelled("h-failed", 8)),
    ]);
    assert!(matches!(refusal(&name, &swapped), Refusal::Changed { .. }));
    // Branches named by position: a new first branch takes `h-1`'s name.
    let branches = |equations: &[(&str, &str)]| {
        definition(
            &equations
                .iter()
                .enumerate()
                .map(|(i, (rhs, label))| equation("V", rhs, &labelled(label, 7 + i as u32)))
                .collect::<Vec<_>>(),
        )
    };
    let before = branches(&[("failed{}()", "h-1"), ("bound{}(one{}())", "h-2")]);
    let old = pair_name(&before);
    let after = branches(&[
        ("state{}(matchFailure{}())", "h-1"),
        ("failed{}()", "h-2"),
        ("bound{}(one{}())", "h-3"),
    ]);
    let refused = refusal(&old, &after);
    assert!(
        matches!(refused, Refusal::Changed { .. } | Refusal::NoFinding),
        "{refused:?}"
    );
}

/// Test 6 (backend level): every refusal reason a name of a premise can have.
#[test]
fn every_refusal_reason() {
    let definition = definition(&pair(7));
    let name = pair_name(&definition);
    let readable = name.rsplit_once('#').expect("a digest").0;
    for (given, reason) in [
        ("nonsense", "malformed"),
        ("root:a,b,c#0123456789abcdef0123456789abcdef", "malformed"),
        ("root:a,b#0123", "malformed"),
        (
            "root:a,b#0123456789abcdef0123456789abcdef#0123456789abcdef0123456789abcdef",
            "malformed",
        ),
        ("root:a b,c#0123456789abcdef0123456789abcdef", "malformed"),
        ("spec.k:7:3,spec.k:8:3@root", "position-name"),
        (readable, "no-digest"),
        ("root:x,y#0123456789abcdef0123456789abcdef", "no-finding"),
    ] {
        let refused = refusal(given, &definition);
        assert_eq!(
            refused.reason(),
            reason,
            "{given}: {}",
            refused.detail(given)
        );
    }
    // A former position name lists the finding at that position now.
    match refusal("spec.k:7:3,spec.k:8:3@root", &definition) {
        Refusal::PositionName { located } => assert_eq!(located, std::slice::from_ref(&name)),
        other => panic!("{other:?}"),
    }
    match refusal(readable, &definition) {
        Refusal::NoDigest { candidates } => assert_eq!(candidates, std::slice::from_ref(&name)),
        other => panic!("{other:?}"),
    }
    // An unlabelled sentence with no UNIQUE_ID has no name: a former position name at it is
    // refused as `unnamed-sentence`.
    let at = |line: u32| {
        format!(
            r#"org'Stop'kframework'Stop'attributes'Stop'Location{{}}("Location({line},3,{line},30)"), org'Stop'kframework'Stop'attributes'Stop'Source{{}}("Source(/work/spec.k)")"#
        )
    };
    let unnamed = self::definition(&[
        equation("V", "failed{}()", &at(7)),
        equation("V", "bound{}(one{}())", &at(8)),
    ]);
    let heads = unnamed.data_heads();
    let (_, none) = only(&heads);
    assert!(none.is_none());
    let refused = refusal("spec.k:7:3,spec.k:8:3@root", &unnamed);
    assert_eq!(refused.reason(), "unnamed-sentence", "{refused:?}");
    // An unlabelled sentence with a UNIQUE_ID is `id:`, and every refusal involving one suggests
    // a label.
    let ids = self::definition(&[
        equation(
            "V",
            "failed{}()",
            &format!("{}, UNIQUE'Unds'ID{{}}(\"aa11\")", at(7)),
        ),
        equation(
            "V",
            "bound{}(one{}())",
            &format!("{}, UNIQUE'Unds'ID{{}}(\"bb22\")", at(8)),
        ),
    ]);
    let id_name = pair_name(&ids);
    assert!(id_name.starts_with("root:id:aa11,id:bb22#"), "{id_name}");
    let refused = refusal(id_name.rsplit_once('#').expect("a digest").0, &ids);
    assert_eq!(refused.reason(), "no-digest");
    assert!(
        refused.detail(&id_name).contains("give it a label"),
        "{}",
        refused.detail(&id_name)
    );
}

/// The decided refusal of a premise whose pair the check now joins: its sentences are those the
/// premise was written for (the digest is reproduced from the definition's equations), and no
/// finding has its name.
#[test]
fn a_premise_whose_pair_now_joins_is_refused_as_decided() {
    // `h-bound` gives `failed` too: one definition, two writings of the same premise.
    let joined = definition(&[
        equation("V", "failed{}()", &labelled("h-failed", 7)),
        equation("V", "failed{}()", &labelled("h-bound", 8)),
    ]);
    assert!(joined.data_heads().confluent());
    // The premise an author wrote when the pair did not join, under an old check: rebuild its
    // digest from this definition's own equations by naming the pair as a finding would.
    let rules = joined
        .function_theory()
        .values()
        .flat_map(|groups| groups.values().flatten())
        .filter(|rule| {
            rule.attributes
                .label
                .as_deref()
                .is_some_and(|label| label.starts_with("h-"))
        })
        .cloned()
        .collect::<Vec<_>>();
    let [first, second] = rules.as_slice() else {
        panic!("two equations");
    };
    let pair = k_rust_backend::confluence::UnjoinedPair {
        first: first.clone(),
        second: second.clone(),
        position: Vec::new(),
        overlap: None,
        sides: None,
        reached: None,
        refused: None,
        conditions: None,
        reason: k_rust_backend::confluence::UnjoinedReason::DifferentResults,
        withdrawn: Vec::new(),
        rewrites_argument: false,
        hook: None,
    };
    let finding = Finding::Pair {
        pair,
        instance: None,
    };
    let premise = k_name(&names::finding_name(&joined, &finding).expect("named"));
    let refused = refusal(&premise, &joined);
    assert_eq!(refused, Refusal::Resolved);
    assert_eq!(refused.reason(), "decided");
}

/// Test 7 (the injected duplicate): two findings with one name and different sentences are
/// `ambiguous`; the hook pairs of one equation, which share a name, are one finding.
#[test]
fn one_name_for_two_propositions_is_ambiguous() {
    let definition = definition(&pair(7));
    let heads = definition.data_heads();
    let (finding, name) = only(&heads);
    let name = name.expect("named").clone();
    let mut other = name.clone();
    other.sentences[0].unique_id = Some("another".to_owned());
    let given = k_name(&name);
    let candidates = [
        Candidate {
            finding,
            name: Some(&name),
        },
        Candidate {
            finding,
            name: Some(&other),
        },
    ];
    let refused =
        classify(&given, &candidates, &definition, &Spelling::k(&symbol)).expect_err("ambiguous");
    assert_eq!(refused.reason(), "ambiguous");
    let same = [
        Candidate {
            finding,
            name: Some(&name),
        },
        Candidate {
            finding,
            name: Some(&name),
        },
    ];
    assert_eq!(
        classify(&given, &same, &definition, &Spelling::k(&symbol)).expect("one finding"),
        [0, 1]
    );
}
