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
            for bits in 0_u8..128 {
                positions.push(Position {
                    form,
                    slot,
                    nesting: Nesting {
                        in_matches_pattern: bits & 1 != 0,
                        in_let_pattern: bits & 2 != 0,
                        in_rewrite: bits & 4 != 0,
                        in_map_key: bits & 8 != 0,
                        in_computed_key: bits & 16 != 0,
                        in_selected_key: bits & 32 != 0,
                        in_braced_instance: bits & 64 != 0,
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
    let subject = Position::root(Form::RuleFn, Slot::Subject);
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
    let key = Position {
        nesting: Nesting {
            in_map_key: true,
            ..subject.nesting
        },
        ..subject
    };
    assert_eq!(
        admits(key, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
}

#[test]
fn a_key_reads_by_its_construct_and_is_built_below_a_computed_one() {
    let key = Position {
        nesting: Nesting {
            in_map_key: true,
            ..Position::root(Form::ReadableRule, Slot::Subject).nesting
        },
        ..Position::root(Form::ReadableRule, Slot::Subject)
    };
    // A name or a pattern-only construct selects an entry by matching the map's keys; a
    // computed construct computes the key looked up, when the whole key is computed, which
    // takes its names: the compiler decides.
    for construct in [
        Construct::Wildcard,
        Construct::As,
        Construct::Or,
        Construct::RecordUpdate,
    ] {
        assert_eq!(admits(key, construct), Admission::Admit, "{construct:?}");
    }
    assert_eq!(
        admits(key, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
    assert_eq!(
        admits(key, Construct::SortTest),
        Admission::After(Rule::SortTestInPattern)
    );
    let computed = Position {
        nesting: Nesting {
            in_computed_key: true,
            ..key.nesting
        },
        ..key
    };
    assert_eq!(
        admits(computed, Construct::Wildcard),
        Admission::Refuse(Class::WildcardOutsidePattern)
    );
    assert_eq!(
        admits(computed, Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(computed, Construct::Or),
        Admission::After(Rule::AlternativesOutsidePattern)
    );
    assert_eq!(
        admits(computed, Construct::OpenRecord),
        Admission::Refuse(Class::OpenRecordOutsidePattern)
    );
    assert_eq!(admits(key, Construct::OpenRecord), Admission::Admit);
    assert_eq!(
        admits(computed, Construct::SortTest),
        Admission::After(Rule::SortTestInPattern)
    );
    // K's `#let` and `:=K` stand in built terms and conditions only: no key holds them, at any
    // depth (NT-3-2).
    for position in [key, computed] {
        assert_eq!(
            admits(position, Construct::Let),
            Admission::Refuse(Class::LetOutsideTerm)
        );
        assert_eq!(
            admits(position, Construct::Matches),
            Admission::Refuse(Class::MatchesOutsideCondition)
        );
    }
    // Below `@` or `|`, a key selects an entry by matching: what computes is refused.
    let selected = Position {
        nesting: Nesting {
            in_selected_key: true,
            ..key.nesting
        },
        ..key
    };
    assert_eq!(admits(selected, Construct::Wildcard), Admission::Admit);
    // Below `@` or `|` a key is matched: a function there never matches.
    assert_eq!(
        admits(selected, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
    assert_eq!(
        admits(selected, Construct::SortTest),
        Admission::Refuse(Class::SortTestInPattern)
    );
    assert_eq!(
        admits(selected, Construct::Let),
        Admission::Refuse(Class::LetOutsideTerm)
    );
    // A `cells!` key is a cell's content, which holds no `let` (S0-17's boundary).
    let cells_key = Position {
        form: Form::CellsRule,
        ..key
    };
    assert_eq!(
        admits(cells_key, Construct::Let),
        Admission::Refuse(Class::LetOutsideTerm)
    );
    assert_eq!(
        admits(cells_key, Construct::SortTest),
        Admission::After(Rule::SortTestInPattern)
    );
}

#[test]
fn a_map_value_a_list_element_and_a_local_pattern_match_evaluated_terms() {
    let subject = Position::root(Form::CellsRule, Slot::Subject);
    // A map's value and a list's element are matched as a constructor's field is.
    assert_eq!(
        admits(subject, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
    // A local pattern matches a value a rule computed, in a result or a condition too.
    for slot in [Slot::Result, Slot::Requires] {
        for local in [
            Nesting {
                in_let_pattern: true,
                ..subject.nesting
            },
            Nesting {
                in_matches_pattern: true,
                ..subject.nesting
            },
        ] {
            let position = Position {
                form: Form::SortRule,
                slot,
                nesting: local,
            };
            assert_eq!(
                admits(position, Construct::FunctionApplication),
                Admission::After(Rule::FunctionInPattern),
                "{position:?}"
            );
        }
    }
}

#[test]
fn a_function_application_where_a_rule_or_an_equation_matches_is_left_to_the_compiler() {
    // At a slot's root as below it: the compiler tells an equation's subject root, the function
    // it defines, from the root of its function-context cells.
    for form in [
        Form::ReadableRule,
        Form::SortRule,
        Form::RuleFn,
        Form::LocalRule,
        Form::CellsRule,
        Form::CellsLocalRule,
        Form::EquationFn,
        Form::EquationTable,
        Form::Context,
        Form::ContextAlias,
        Form::Alias,
        Form::Desugar,
    ] {
        let subject = Position::root(form, Slot::Subject);
        assert_eq!(
            admits(subject, Construct::FunctionApplication),
            Admission::After(Rule::FunctionInPattern),
            "{form:?}"
        );
        assert_eq!(
            admits(subject.rewrite_right(), Construct::FunctionApplication),
            Admission::Admit,
            "{form:?}"
        );
    }
    for form in [Form::Simplification, Form::ReadableClaim, Form::CellsClaim] {
        assert_eq!(
            admits(
                Position::root(form, Slot::Subject),
                Construct::FunctionApplication
            ),
            Admission::Admit,
            "{form:?}"
        );
        // A sort test is an application, which these subjects hold.
        assert_eq!(
            admits(Position::root(form, Slot::Subject), Construct::SortTest),
            Admission::Admit,
            "{form:?}"
        );
    }
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
fn an_alias_subject_is_built_backwards_and_refuses_what_only_matches() {
    let subject = Position::root(Form::Alias, Slot::Subject);
    assert!(subject.is_built_backwards());
    for (construct, class) in [
        (Construct::Wildcard, Class::WildcardInAliasSubject),
        (Construct::As, Class::AliasInAliasSubject),
        (Construct::Or, Class::AlternativesInAliasSubject),
        (Construct::OpenRecord, Class::OpenRecordInAliasSubject),
        (Construct::Rest, Class::RestInAliasSubject),
    ] {
        assert_eq!(
            admits(subject, construct),
            Admission::Refuse(class),
            "{construct:?}"
        );
    }
    // A static clause's subject matches a program as written, where a function's application
    // or a sort test would stand for its spelling (decision NT-11-5): the compiler tells a
    // function, and a set's concatenation, which matches only disjoint parts, by its head.
    assert!(subject.matches_terms_as_written());
    assert_eq!(
        admits(subject, Construct::FunctionApplication),
        Admission::After(Rule::FunctionInPattern)
    );
    assert_eq!(
        admits(subject, Construct::SortTest),
        Admission::Refuse(Class::SortTestInPattern)
    );
    // A desugar clause runs one way, and its result is built only once.
    let desugar = Position::root(Form::Desugar, Slot::Subject);
    assert!(!desugar.is_built_backwards());
    for construct in [
        Construct::Wildcard,
        Construct::As,
        Construct::Or,
        Construct::OpenRecord,
        Construct::Rest,
    ] {
        assert_eq!(
            admits(desugar, construct),
            Admission::Admit,
            "{construct:?}"
        );
    }
    let result = Position::root(Form::Alias, Slot::Result);
    assert!(!result.is_built_backwards());
    for construct in [Construct::Let, Construct::Matches, Construct::SortTest] {
        assert_eq!(admits(result, construct), Admission::Admit, "{construct:?}");
    }
    assert_eq!(
        admits(Position::root(Form::RuleFn, Slot::Subject), Construct::Rest),
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
fn a_let_pattern_is_one_shape_without_an_alias() {
    for form in [Form::RuleFn, Form::EquationFn, Form::ReadableRule] {
        for slot in [Slot::Result, Slot::Requires] {
            let in_let = Position {
                nesting: Nesting {
                    in_let_pattern: true,
                    ..Nesting::default()
                },
                ..Position::root(form, slot)
            };
            assert_eq!(
                admits(in_let, Construct::As),
                Admission::Refuse(Class::AliasInLetPattern),
                "{form:?} {slot:?}"
            );
            assert_eq!(
                admits(in_let, Construct::Or),
                Admission::Refuse(Class::AlternativesInLetPattern),
                "{form:?} {slot:?}"
            );
            assert_eq!(
                admits(in_let, Construct::Wildcard),
                Admission::Admit,
                "{form:?} {slot:?}"
            );
        }
    }
}

#[test]
fn a_record_update_is_built_and_an_open_record_matched() {
    let subject = Position::root(Form::RuleFn, Slot::Subject);
    let in_let = Position {
        nesting: Nesting {
            in_let_pattern: true,
            ..Nesting::default()
        },
        ..Position::root(Form::RuleFn, Slot::Result)
    };
    let local_left = Position::root(Form::LocalRule, Slot::Subject).rewrite_left();
    for pattern in [subject, in_let, local_left] {
        assert_eq!(
            admits(pattern, Construct::RecordUpdate),
            Admission::Refuse(Class::RecordUpdateInPattern),
            "{pattern}"
        );
        assert_eq!(
            admits(pattern, Construct::OpenRecord),
            Admission::Admit,
            "{pattern}"
        );
    }
    for built in [
        Position::root(Form::RuleFn, Slot::Result),
        Position::root(Form::ReadableRule, Slot::Requires),
        Position::root(Form::LocalRule, Slot::Subject).rewrite_right(),
    ] {
        assert_eq!(
            admits(built, Construct::RecordUpdate),
            Admission::Admit,
            "{built}"
        );
    }
    // A `cells!` value names every field, whether it matches or builds.
    assert_eq!(
        admits(
            Position::root(Form::CellsRule, Slot::Subject),
            Construct::RecordUpdate
        ),
        Admission::Refuse(Class::RecordRemainderInCellsTerm)
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
fn a_rewrite_changes_a_map_value_and_never_a_key() {
    let subject = Position::root(Form::CellsLocalRule, Slot::Subject);
    let entry = |in_map_key| Position {
        nesting: Nesting {
            in_map_key,
            ..Nesting::default()
        },
        ..subject
    };
    assert_eq!(admits(entry(false), Construct::Rewrite), Admission::Admit);
    assert_eq!(
        admits(entry(true), Construct::Rewrite),
        Admission::Refuse(Class::RewriteInMapKey)
    );
    // Where no rewrite stands at all, that is the answer, key or not.
    let readable_key = Position {
        form: Form::ReadableRule,
        ..entry(true)
    };
    assert_eq!(
        admits(readable_key, Construct::Rewrite),
        Admission::Refuse(Class::RewriteOutsideLocalRule)
    );
}

#[test]
fn a_rewrite_matches_on_its_left_and_builds_on_its_right() {
    let subject = Position::root(Form::LocalRule, Slot::Subject);
    let (left, right) = (subject.rewrite_left(), subject.rewrite_right());
    assert_eq!(admits(left, Construct::As), Admission::Admit);
    assert_eq!(admits(left, Construct::Wildcard), Admission::Admit);
    assert_eq!(
        admits(right, Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(right, Construct::Wildcard),
        Admission::Refuse(Class::WildcardOutsidePattern)
    );
    for construct in [Construct::Let, Construct::Matches, Construct::SortTest] {
        assert!(
            matches!(admits(left, construct), Admission::Refuse(_)),
            "{construct:?}"
        );
        assert_eq!(admits(right, construct), Admission::Admit, "{construct:?}");
    }
    assert_eq!(
        admits(right, Construct::Rewrite),
        Admission::Refuse(Class::RewriteOutsideLocalRule)
    );
    assert!(
        right
            .to_string()
            .starts_with("the right side of a `k::rewrite!`")
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
    }
    // A readable claim's states and conditions could hold `let` and `k::matches!`, but no prover
    // takes them there (finding NT-7-1); a `cells!` claim's cell values are `cells!` values.
    for slot in [Slot::Subject, Slot::Result, Slot::Requires, Slot::Ensures] {
        let position = Position::root(Form::ReadableClaim, slot);
        assert_eq!(
            admits(position, Construct::Matches),
            Admission::Refuse(Class::MatchesInClaim),
            "{slot:?}"
        );
        assert_eq!(
            admits(position, Construct::Let),
            Admission::Refuse(Class::LetInClaim),
            "{slot:?}"
        );
    }
    let requires = Position::root(Form::CellsClaim, Slot::Requires);
    assert_eq!(
        admits(requires, Construct::Let),
        Admission::Refuse(Class::LetInClaim)
    );
    let result = Position::root(Form::CellsClaim, Slot::Result);
    assert_eq!(
        admits(result, Construct::Let),
        Admission::Refuse(Class::LetOutsideTerm)
    );
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
        admits(value, Construct::OpenRecord),
        Admission::Refuse(Class::RecordRemainderInInitializer)
    );
    assert_eq!(
        admits(value, Construct::MlPredicate),
        Admission::Refuse(Class::MlInInitializer)
    );
    assert_eq!(
        admits(value, Construct::Fragment),
        Admission::Refuse(Class::FragmentInInitializer)
    );
    // It is built as a result is: a `let` block, `k::matches!`, a sort test, a turbofish and a
    // record update mean there what they mean in a result.
    for construct in [
        Construct::Literal,
        Construct::IdToken,
        Construct::Lexeme,
        Construct::FunctionApplication,
        Construct::Let,
        Construct::Matches,
        Construct::SortTest,
        Construct::Turbofish,
        Construct::RecordUpdate,
    ] {
        assert_eq!(admits(value, construct), Admission::Admit, "{construct:?}");
    }
    // A local pattern in it reads as one: `_` and an open record match, a predicate is no
    // pattern, and `@`, which K's right-hand side refuses, is refused in a `k::matches!` there.
    let matches = Position {
        nesting: Nesting {
            in_matches_pattern: true,
            ..Nesting::default()
        },
        ..value
    };
    for construct in [Construct::Wildcard, Construct::Or, Construct::OpenRecord] {
        assert_eq!(
            admits(matches, construct),
            Admission::Admit,
            "{construct:?}"
        );
    }
    assert_eq!(
        admits(matches, Construct::As),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    assert_eq!(
        admits(matches, Construct::MlPredicate),
        Admission::Refuse(Class::MlPredicateAsTerm)
    );
    assert_eq!(
        admits(matches, Construct::Let),
        Admission::Refuse(Class::LetOutsideTerm)
    );
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

#[test]
fn a_subject_root_is_the_matched_head_and_a_value_root_a_term() {
    for construct in [
        RootConstruct::As,
        RootConstruct::Wildcard,
        RootConstruct::Island,
    ] {
        assert!(!PatternRoot::Subject.admits(construct), "{construct:?}");
        assert!(PatternRoot::Value.admits(construct), "{construct:?}");
    }
    assert!(PatternRoot::Subject.names_constructor());
    assert!(!PatternRoot::Value.names_constructor());
    // A clause's root binds a bare name and holds `_`, an alias or an island as a value does, and
    // is otherwise a subject's.
    assert_eq!(PatternRoot::Clause.at(true), PatternRoot::Value);
    assert_eq!(PatternRoot::Clause.at(false), PatternRoot::Subject);
    assert_eq!(PatternRoot::Subject.at(true), PatternRoot::Subject);
}
