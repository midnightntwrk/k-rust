use std::collections::BTreeSet;

use super::*;

/// Every position the walker can reach: each form's slots, under every nesting.
fn positions() -> Vec<Position> {
    let mut positions = Vec::new();
    for form in Form::ALL {
        let slots: &[Slot] = match form {
            Form::Initializer => &[Slot::InitializerValue],
            Form::Constant => &[Slot::ConstantValue],
            _ => &[Slot::Subject, Slot::Result, Slot::Requires, Slot::Ensures],
        };
        for &slot in slots {
            for bits in 0_u8..32 {
                positions.push(Position {
                    form,
                    slot,
                    nesting: Nesting {
                        below_root: bits & 1 != 0,
                        in_matches_pattern: bits & 2 != 0,
                        in_let_pattern: bits & 4 != 0,
                        in_rewrite: bits & 8 != 0,
                        in_collection_entry: bits & 16 != 0,
                    },
                });
            }
        }
    }
    positions
}

#[test]
fn every_class_and_rule_answers_some_row() {
    let mut classes = BTreeSet::new();
    let mut rules = BTreeSet::new();
    for position in positions() {
        for construct in Construct::ALL {
            match admits(position, construct) {
                Admission::Admit => {}
                Admission::Refuse(class) => {
                    classes.insert(class);
                }
                Admission::After(rule) => {
                    rules.insert(rule);
                }
            }
        }
    }
    assert_eq!(classes, Class::ALL.into_iter().collect());
    assert_eq!(rules, Rule::ALL.into_iter().collect());
}

#[test]
fn every_class_code_is_a_registered_author_code() {
    for class in Class::ALL {
        let info = codes::info(class.code().as_str())
            .unwrap_or_else(|| panic!("{} names an unregistered code", class.name()));
        assert_eq!(
            info.code.kind(),
            codes::CodeKind::Author,
            "{}",
            class.name()
        );
    }
}

#[test]
fn a_pattern_admits_what_matches_and_refuses_what_computes() {
    let subject = Position {
        nesting: Nesting {
            below_root: true,
            ..Nesting::default()
        },
        ..Position::root(Form::RuleFn, Slot::Subject)
    };
    for construct in [Construct::Wildcard, Construct::As, Construct::Or] {
        assert_eq!(
            admits(subject, construct),
            Admission::Admit,
            "{construct:?}"
        );
    }
    assert_eq!(
        admits(subject, Construct::Matches),
        Admission::Refuse(Class::MatchesOutsideCondition)
    );
    assert_eq!(
        admits(subject, Construct::Let),
        Admission::Refuse(Class::LetOutsideTerm)
    );
    assert_eq!(
        admits(subject, Construct::SortTest),
        Admission::Refuse(Class::SortTestInPattern)
    );
    assert_eq!(
        admits(subject, Construct::MlPredicate),
        Admission::Refuse(Class::MlPredicateAsTerm)
    );
    assert_eq!(
        admits(subject, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
    let entry = Position {
        nesting: Nesting {
            in_collection_entry: true,
            ..subject.nesting
        },
        ..subject
    };
    assert_eq!(
        admits(entry, Construct::FunctionApplication),
        Admission::Admit
    );
}

#[test]
fn a_built_term_refuses_what_only_matches() {
    let result = Position::root(Form::RuleFn, Slot::Result);
    assert_eq!(
        admits(result, Construct::Wildcard),
        Admission::Refuse(Class::WildcardOutsidePattern)
    );
    assert_eq!(
        admits(result, Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(result, Construct::Or),
        Admission::After(Rule::AlternativesOutsidePattern)
    );
    for construct in [Construct::Matches, Construct::Let, Construct::SortTest] {
        assert_eq!(admits(result, construct), Admission::Admit, "{construct:?}");
    }
    // A desugar clause's `_` is K's anonymous variable of the rewritten program.
    assert_eq!(
        admits(
            Position::root(Form::Desugar, Slot::Result),
            Construct::Wildcard
        ),
        Admission::Admit
    );
}

#[test]
fn a_matches_pattern_binds_an_alias_in_a_condition_only() {
    let in_matches = |slot| Position {
        nesting: Nesting {
            in_matches_pattern: true,
            ..Nesting::default()
        },
        ..Position::root(Form::RuleFn, slot)
    };
    assert_eq!(
        admits(in_matches(Slot::Requires), Construct::As),
        Admission::Admit
    );
    assert_eq!(
        admits(in_matches(Slot::Result), Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(in_matches(Slot::Result), Construct::Wildcard),
        Admission::Admit
    );
}

#[test]
fn a_single_body_rule_rewrites_only_inside_its_subject_and_once() {
    let subject = Position::root(Form::LocalRule, Slot::Subject);
    assert_eq!(admits(subject, Construct::Rewrite), Admission::Admit);
    assert_eq!(
        admits(subject, Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(subject, Construct::Or),
        Admission::Refuse(Class::AlternativesInOneTermRewrite)
    );
    let inside = Position {
        nesting: Nesting {
            in_rewrite: true,
            ..Nesting::default()
        },
        ..subject
    };
    assert_eq!(
        admits(inside, Construct::Rewrite),
        Admission::Refuse(Class::RewriteOutsideLocalRule)
    );
    assert_eq!(admits(inside, Construct::As), Admission::Admit);
    for form in [Form::RuleFn, Form::EquationFn, Form::ReadableRule] {
        assert_eq!(
            admits(Position::root(form, Slot::Subject), Construct::Rewrite),
            Admission::Refuse(Class::RewriteOutsideLocalRule),
            "{form:?}"
        );
    }
    assert_eq!(
        admits(
            Position::root(Form::Context, Slot::Subject),
            Construct::Rewrite
        ),
        Admission::Admit
    );
}

#[test]
fn claims_hold_the_symbolic_islands() {
    for form in [Form::ReadableClaim, Form::CellsClaim] {
        let subject = Position::root(form, Slot::Subject);
        let result = Position::root(form, Slot::Result);
        assert_eq!(admits(subject, Construct::Anonymous), Admission::Admit);
        assert_eq!(
            admits(result, Construct::Anonymous),
            Admission::Refuse(Class::ClaimSubjectOnlyTerm)
        );
        assert_eq!(admits(subject, Construct::OrBool), Admission::Admit);
        assert_eq!(admits(result, Construct::OrBool), Admission::Admit);
        assert_eq!(admits(result, Construct::SortTest), Admission::Admit);
        assert_eq!(
            admits(result, Construct::Matches),
            Admission::Refuse(Class::MatchesOutsideCondition)
        );
        assert_eq!(
            admits(result, Construct::Let),
            Admission::Refuse(Class::LetOutsideTerm)
        );
    }
    let rule = Position::root(Form::RuleFn, Slot::Result);
    assert_eq!(
        admits(rule, Construct::OrBool),
        Admission::Refuse(Class::ClaimOnlyTerm)
    );
}

#[test]
fn an_initializer_builds_concrete_values() {
    let value = Position::root(Form::Initializer, Slot::InitializerValue);
    assert_eq!(
        admits(value, Construct::Anonymous),
        Admission::Refuse(Class::ClaimSubjectOnlyTerm)
    );
    assert_eq!(
        admits(value, Construct::Turbofish),
        Admission::Refuse(Class::TurbofishInInitializer)
    );
    for construct in [Construct::RecordUpdate, Construct::OpenRecord] {
        assert_eq!(
            admits(value, construct),
            Admission::Refuse(Class::RecordRemainderInInitializer)
        );
    }
    for construct in [Construct::Literal, Construct::IdToken, Construct::Lexeme] {
        assert_eq!(admits(value, construct), Admission::Admit, "{construct:?}");
    }
}

#[test]
fn a_cells_value_names_every_field_and_holds_no_let_or_test() {
    for form in [Form::CellsRule, Form::CellsLocalRule, Form::CellsClaim] {
        for slot in [Slot::Subject, Slot::Result] {
            let position = Position::root(form, slot);
            for construct in [Construct::RecordUpdate, Construct::OpenRecord] {
                assert_eq!(
                    admits(position, construct),
                    Admission::Refuse(Class::RecordRemainderInCellsTerm)
                );
            }
            assert_eq!(
                admits(position, Construct::Let),
                Admission::Refuse(Class::LetOutsideTerm)
            );
            assert_eq!(
                admits(position, Construct::Matches),
                Admission::Refuse(Class::MatchesOutsideCondition)
            );
        }
    }
    // Its conditions are a rule's conditions.
    let requires = Position::root(Form::CellsRule, Slot::Requires);
    assert_eq!(admits(requires, Construct::Let), Admission::Admit);
    assert_eq!(admits(requires, Construct::Matches), Admission::Admit);
}

#[test]
fn a_constant_is_a_ground_constructor_term() {
    let value = Position::root(Form::Constant, Slot::ConstantValue);
    for construct in [
        Construct::Literal,
        Construct::IdToken,
        Construct::BytesToken,
        Construct::Lexeme,
    ] {
        assert_eq!(admits(value, construct), Admission::Admit, "{construct:?}");
    }
    assert_eq!(
        admits(value, Construct::FunctionApplication),
        Admission::After(Rule::ConstantAppliesFunction)
    );
    for construct in [
        Construct::Wildcard,
        Construct::Anonymous,
        Construct::Fragment,
    ] {
        assert_eq!(
            admits(value, construct),
            Admission::Refuse(Class::ConstantNotGround),
            "{construct:?}"
        );
    }
}

#[test]
fn a_refusal_names_the_position() {
    let position = Position {
        nesting: Nesting {
            in_matches_pattern: true,
            ..Nesting::default()
        },
        ..Position::root(Form::ReadableRule, Slot::Result)
    };
    assert_eq!(
        position.to_string(),
        "a `k::matches!` pattern in the result of a readable rule"
    );
    assert!(
        Class::AliasOutsidePattern.message(position).ends_with(
            "; here it stands in a `k::matches!` pattern in the result of a readable rule"
        )
    );
}
