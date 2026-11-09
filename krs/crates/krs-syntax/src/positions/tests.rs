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
            for bits in 0_u16..256 {
                positions.push(Position {
                    form,
                    slot,
                    nesting: Nesting {
                        in_matches_pattern: bits & 1 != 0,
                        in_let_pattern: bits & 2 != 0,
                        in_rewrite: bits & 4 != 0,
                        in_map_key: bits & 8 != 0,
                        // The walker marks a set's element as a key too.
                        in_set_element: bits & 128 != 0 && bits & 8 != 0,
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
    // A key a `cells!` subject computes denotes what the same key of a readable rule does, so it
    // holds a `let` as that key does; a `cells!` result's key is built, as any result term is,
    // so it computes (S0-17).
    let cells_key = Position {
        form: Form::CellsRule,
        ..key
    };
    assert_eq!(
        admits(cells_key, Construct::Let),
        Admission::After(Rule::LetOutsideTerm)
    );
    assert_eq!(
        admits(
            Position {
                slot: Slot::Result,
                ..cells_key
            },
            Construct::Let
        ),
        Admission::Admit
    );
    assert_eq!(
        admits(cells_key, Construct::SortTest),
        Admission::After(Rule::SortTestInPattern)
    );
}

#[test]
fn a_computed_key_holds_a_local_function_where_its_pattern_meets_evaluated_terms() {
    let key = Position {
        nesting: Nesting {
            in_map_key: true,
            ..Position::root(Form::ReadableRule, Slot::Subject).nesting
        },
        ..Position::root(Form::ReadableRule, Slot::Subject)
    };
    let computed = Position {
        nesting: Nesting {
            in_computed_key: true,
            ..key.nesting
        },
        ..key
    };
    // A `let` block and `k::matches!` are functions of the names they read: a key a pattern over
    // evaluated terms computes holds them as it holds an application (NT-3-2), and the compiler
    // refuses one where the key selects by a name nothing else binds.
    for position in [key, computed] {
        assert_eq!(
            admits(position, Construct::Let),
            Admission::After(Rule::LetOutsideTerm)
        );
        assert_eq!(
            admits(position, Construct::Matches),
            Admission::After(Rule::MatchesOutsideCondition)
        );
    }
    // A test in a key is a function of the names the key reads, whose equations state the test
    // in their conditions, where `@` in its pattern means what it means in any condition.
    let key_test = Position {
        nesting: Nesting {
            in_matches_pattern: true,
            ..computed.nesting
        },
        ..computed
    };
    assert_eq!(admits(key_test, Construct::As), Admission::Admit);
    // In a result a test's pattern tests a built term, which `@` names no part of.
    assert_eq!(
        admits(
            Position {
                slot: Slot::Result,
                ..key_test
            },
            Construct::As
        ),
        Admission::Refuse(Class::AliasOutsidePattern)
    );
    // A simplification's and a static clause's patterns meet unevaluated terms, where the
    // generated function's application never stands.
    for form in [Form::Simplification, Form::Desugar] {
        let unevaluated = Position { form, ..key };
        assert_eq!(
            admits(unevaluated, Construct::Let),
            Admission::Refuse(Class::LetOutsideTerm)
        );
    }
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
    // function, and a collection of two or more parts, one of its spellings, by its head.
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
    // A `cells!` pattern holds no update of any record; where a `cells!` value is built, only
    // the record's head tells a constructor's record, written whole, from a group record, a
    // cell's entry.
    assert_eq!(
        admits(
            Position::root(Form::CellsRule, Slot::Subject),
            Construct::RecordUpdate
        ),
        Admission::Refuse(Class::RecordRemainderInCellsTerm)
    );
    assert_eq!(
        admits(
            Position::root(Form::CellsRule, Slot::Result),
            Construct::RecordUpdate
        ),
        Admission::After(Rule::RecordRemainderInCellsTerm)
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
    // A readable claim's states and conditions hold `let` and `k::matches!` as a rule's do: KRS
    // lifts them into functions the claim's spec module declares (NT-15); a `cells!` claim's
    // result values are built, as a readable claim's are, and its start state's are `cells!`
    // subject values (S0-17).
    for slot in [Slot::Subject, Slot::Result, Slot::Requires, Slot::Ensures] {
        let position = Position::root(Form::ReadableClaim, slot);
        assert_eq!(
            admits(position, Construct::Matches),
            Admission::Admit,
            "{slot:?}"
        );
        assert_eq!(
            admits(position, Construct::Let),
            Admission::Admit,
            "{slot:?}"
        );
    }
    let requires = Position::root(Form::CellsClaim, Slot::Requires);
    assert_eq!(admits(requires, Construct::Let), Admission::Admit);
    let result = Position::root(Form::CellsClaim, Slot::Result);
    assert_eq!(admits(result, Construct::Let), Admission::Admit);
    assert_eq!(admits(result, Construct::Matches), Admission::Admit);
    // A `cells!` claim's start state is a term, as a readable claim's is (S0-17).
    let subject = Position::root(Form::CellsClaim, Slot::Subject);
    assert_eq!(admits(subject, Construct::Let), Admission::Admit);
    assert_eq!(admits(subject, Construct::Matches), Admission::Admit);
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
fn a_cells_value_names_every_field_and_computes_only_where_built() {
    // A constructor's record is written whole; a record whose head is a group's struct is a
    // cell's entry, which the entry's admission judges: only resolution tells them apart.
    for form in [
        Form::CellsRule,
        Form::CellsLocalRule,
        Form::CellsClaim,
        Form::ContextAlias,
    ] {
        for slot in [Slot::Subject, Slot::Result] {
            let position = Position::root(form, slot);
            assert_eq!(
                admits(position, Construct::OpenRecord),
                Admission::After(Rule::RecordRemainderInCellsTerm)
            );
            assert_eq!(
                admits(position, Construct::RecordUpdate),
                if matches!(slot, Slot::Result) {
                    Admission::After(Rule::RecordRemainderInCellsTerm)
                } else {
                    Admission::Refuse(Class::RecordRemainderInCellsTerm)
                }
            );
        }
    }
    // A result value is built, so a `let` or a test computes it, as in a readable result; a
    // rule's subject value is a pattern, which holds neither outside a key or a Set collection's
    // instance the subject computes; a claim's start state is a term (S0-17).
    for form in [Form::CellsRule, Form::CellsLocalRule, Form::CellsClaim] {
        let result = Position::root(form, Slot::Result);
        assert_eq!(admits(result, Construct::Let), Admission::Admit);
        assert_eq!(admits(result, Construct::Matches), Admission::Admit);
    }
    for form in [Form::CellsRule, Form::CellsLocalRule] {
        let subject = Position::root(form, Slot::Subject);
        assert_eq!(
            admits(subject, Construct::Let),
            Admission::Refuse(Class::LetOutsideTerm)
        );
        assert_eq!(
            admits(subject, Construct::Matches),
            Admission::Refuse(Class::MatchesOutsideCondition)
        );
    }
    let mut instance = Position::root(Form::CellsRule, Slot::Subject);
    instance.nesting.in_braced_instance = true;
    assert_eq!(
        admits(instance, Construct::Let),
        Admission::After(Rule::LetOutsideTerm)
    );
    assert_eq!(
        admits(instance, Construct::Matches),
        Admission::After(Rule::MatchesOutsideCondition)
    );
    // A pattern's group record leaves the group's other children unconstrained (S5-F2); a
    // result's `..` after every child is the exact record, and the entry's admission refuses one
    // that leaves a child out, as it does the bare twin's (RDRA item 1).
    for form in [Form::CellsRule, Form::CellsLocalRule, Form::CellsClaim] {
        for slot in [Slot::Subject, Slot::Result] {
            assert_eq!(
                admits(Position::root(form, slot), Construct::OpenFragment),
                Admission::Admit
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

#[test]
fn a_set_s_element_in_a_pattern_reads_as_a_key() {
    let element = Position {
        nesting: Nesting {
            in_map_key: true,
            in_set_element: true,
            ..Position::root(Form::RuleFn, Slot::Subject).nesting
        },
        ..Position::root(Form::RuleFn, Slot::Subject)
    };
    assert_eq!(
        element.to_string(),
        "a set's element in the subject of a `#[k::rule]` fn"
    );
    // A set's element is computed from names bound elsewhere, as a key is.
    assert_eq!(
        admits(element, Construct::Let),
        Admission::After(Rule::LetOutsideTerm)
    );
    assert_eq!(
        admits(element, Construct::SortTest),
        Admission::After(Rule::SortTestInPattern)
    );
    // Replacing an element in place may meet one the set already holds, as re-keying an entry
    // may meet a key the map holds.
    for form in [Form::LocalRule, Form::CellsLocalRule] {
        assert_eq!(
            admits(Position { form, ..element }, Construct::Rewrite),
            Admission::Refuse(Class::RewriteInMapKey)
        );
        // Outside the element, inside the single-body rule's subject, the rewrite is admitted.
        assert_eq!(
            admits(Position::root(form, Slot::Subject), Construct::Rewrite),
            Admission::Admit
        );
    }
    // In a `cells!` subject too.
    let cells = Position {
        form: Form::CellsRule,
        ..element
    };
    assert_eq!(
        admits(cells, Construct::Matches),
        Admission::After(Rule::MatchesOutsideCondition)
    );
}
