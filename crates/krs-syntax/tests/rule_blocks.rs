//! Readable term-rule family parser coverage.

use krs_syntax::KrsSyntax;
use krs_syntax::{ProvenanceRole, RuleExtra, RuleHeadResult};

#[test]
fn nonlinear_subject_bindings_are_one_catalog_entry_with_repeated_occurrences() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Expr;
        use Op::*;

        same: Eq(value, value) => true;
        ",
    )
    .unwrap();

    let pattern = &block.clauses()[0].rule().parameter().pattern;
    assert_eq!(pattern.bindings(), ["value"]);
    assert_eq!(pattern.spelling(), "Eq (value , value)");
}

#[test]
fn imp_expression_table_reuses_the_structured_rule_grammar() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Expr;
        use Op::*;

        eval_neg:     Neg { value }          => int::sub(0, value);
        eval_not:     Not { value }          => bool::not(value);
        eval_add:     Add { lhs, rhs }       => int::add(lhs, rhs);
        eval_sub:     Sub { lhs, rhs }       => int::sub(lhs, rhs);
        eval_mul:     Mul { lhs, rhs }       => int::mul(lhs, rhs);
        eval_div:     Div { lhs, rhs }       => int::div(lhs, rhs);
        eval_ge:      Ge { lhs, rhs }        => int::ge(lhs, rhs);
        eval_gt:      Gt { lhs, rhs }        => int::gt(lhs, rhs);
        eval_le:      Le { lhs, rhs }        => int::le(lhs, rhs);
        eval_lt:      Lt { lhs, rhs }        => int::lt(lhs, rhs);
        eval_bool_eq: Eq { lhs, rhs }        => bool::eq(lhs, rhs) where lhs: Bool, rhs: Bool;
        eval_int_eq:  Eq { lhs, rhs }        => int::eq(lhs, rhs)  where lhs: Int, rhs: Int;
        eval_bool_ne: Ne { lhs, rhs }        => bool::ne(lhs, rhs) where lhs: Bool, rhs: Bool;
        eval_int_ne:  Ne { lhs, rhs }        => int::ne(lhs, rhs)  where lhs: Int, rhs: Int;
        and_true:     And { lhs: true, rhs } => rhs;
        and_false:    And { lhs: false, .. } => false;
        or_true:      Or { lhs: true, .. }   => true;
        or_false:     Or { lhs: false, rhs } => rhs;
        ",
    )
    .unwrap();

    assert_eq!(block.sort().sort_token_text(), "Expr");
    assert_eq!(block.imports().len(), 1);
    assert_eq!(block.imports()[0].owner().segments[0].ident, "Op");
    assert_eq!(block.clauses().len(), 18);
    assert_eq!(block.clauses()[10].narrowings().len(), 2);
    assert_eq!(block.clauses()[10].narrowings()[0].binding(), "lhs");
    assert_eq!(
        block.clauses()[10].narrowings()[0].sort().segments[0].ident,
        "Bool"
    );
    assert_eq!(
        block.clauses()[15]
            .rule()
            .parameter()
            .pattern
            .bindings()
            .len(),
        0
    );
    assert_eq!(
        block.clauses()[17]
            .rule()
            .parameter()
            .pattern
            .bindings()
            .len(),
        1
    );

    let anchors = block.clauses()[0].rule().full_provenance().unwrap();
    assert!(
        anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleDeclaration)
    );
    assert!(
        anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleType)
    );
    assert!(
        anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleLeftRecordFieldName)
    );
    assert!(
        anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::RuleRightLiteral)
    );
}

#[test]
fn positional_docs_labels_and_raw_identities_are_retained() {
    let block = krs_syntax::RuleBlock::parse_source(
        r#"
        for Stmt;
        use StmtSyntax::*;

        /// Unfold the loop.
        #[k::rule(owise, label = "while-step")]
        r#while: While(c, s) => IfThen(c, s) where c: Bool;
        "#,
    )
    .unwrap();
    let clause = &block.clauses()[0];
    assert_eq!(clause.rule().item().sig.ident.to_string(), "r#while");
    assert_eq!(clause.attribute().label().unwrap().value(), "while-step");
    assert!(clause.attribute().is_owise());
    assert!(
        clause
            .rule()
            .item()
            .attrs
            .iter()
            .any(|attribute| attribute.path().is_ident("doc"))
    );
    assert_eq!(clause.rule().parameter().pattern.bindings().len(), 2);
}

#[test]
fn control_flow_results_and_gradual_map_extras_are_structured() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Stmt;
        use StmtSyntax::*;

        step: Sequence(s1, s2) => k![s1, s2];
        done: EmptyBlock() => ();
        assign: Assign(name, value) => ()
            where value: Value,
                  update env = map::update(env, name, value);
        ",
    )
    .unwrap();
    assert!(matches!(
        block.clauses()[0].head_result(),
        Some(RuleHeadResult::Splice { items, .. }) if items.len() == 2
    ));
    assert!(matches!(
        block.clauses()[1].head_result(),
        Some(RuleHeadResult::Erase(_))
    ));
    assert!(matches!(
        block.clauses()[2].extras(),
        [RuleExtra::UpdateMap { cell, .. }] if cell == "env"
    ));
    let roles = block.clauses()[2]
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::RuleBindingType));
    assert!(roles.contains(&ProvenanceRole::RuleRightCellsField));
    assert!(roles.contains(&ProvenanceRole::RuleRightMapUpdateBase));
    assert!(roles.contains(&ProvenanceRole::RuleRightMapKey));
    assert!(roles.contains(&ProvenanceRole::RuleRightMapValue));

    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Expr;
        var: name => value
            where name: Id,
                  value: Value,
                  have env[Lookup(name, name) -> let value];
        ",
    )
    .unwrap();
    let clause = &block.clauses()[0];
    assert_eq!(
        clause
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["name", "value"]
    );
    assert!(matches!(
        clause.extras(),
        [RuleExtra::HaveMap { cell, value, .. }]
            if cell == "env" && value == "value"
    ));
    let roles = clause
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::RuleLeftCellsField));
    assert!(roles.contains(&ProvenanceRole::RuleLeftMapKey));
    assert!(roles.contains(&ProvenanceRole::RuleLeftMapValue));
}

#[test]
fn final_machine_records_preserve_cells_bindings_and_configuration_ownership() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use StmtSyntax::Assign;

        var: {
            computation: [name, ..],
            env: { name -> value, .. },
        } => {
            computation: [value, ..],
        }
        where name: Id;

        assign: {
            computation: [Assign(name, value), ..],
            env: e,
        } => {
            computation: [..],
            env: map::update(e, name, value),
        }
        where value: Value;
        ",
    )
    .unwrap();

    assert!(block.is_configuration());
    assert_eq!(block.sort().sort_token_text(), "Machine");
    assert_eq!(block.imports()[0].owner().segments[0].ident, "StmtSyntax");
    assert_eq!(block.imports()[0].variant().unwrap(), "Assign");
    assert_eq!(
        block.clauses()[0].computation_cell().unwrap(),
        "computation"
    );
    assert_eq!(
        block.clauses()[0]
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["name", "value"]
    );
    assert!(matches!(
        block.clauses()[0].extras(),
        [RuleExtra::HaveMap { cell, value, .. }]
            if cell == "env" && value == "value"
    ));
    assert!(matches!(
        block.clauses()[1].extras(),
        [RuleExtra::UpdateMap { cell, base, .. }]
            if cell == "env" && base == "e"
    ));
    let update_roles = block.clauses()[1]
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert_eq!(
        update_roles
            .iter()
            .filter(|role| **role == ProvenanceRole::RuleRightApplicationHead)
            .count(),
        1
    );
    assert_eq!(
        update_roles
            .iter()
            .filter(|role| **role == ProvenanceRole::RuleRightReference)
            .count(),
        3
    );
}

#[test]
fn machine_records_support_ordinary_fixed_cell_term_rewrites() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Instr::Binary;

        binary: {
            instrs: [Binary(op), ..],
            valstack: Stack::Cons(rhs, Stack::Cons(lhs, rest)),
        } => {
            instrs: [Eval(op, lhs, rhs), ..],
            valstack: rest,
        }
        where op: BinOp, lhs: Value, rhs: Value, rest: ValStack;
        ",
    )
    .unwrap();

    let clause = &block.clauses()[0];
    assert_eq!(clause.computation_cell().unwrap(), "instrs");
    assert_eq!(
        clause
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["op", "rhs", "lhs", "rest"]
    );
    assert!(matches!(
        clause.extras(),
        [RuleExtra::RewriteCell { cell, before, after, .. }]
            if cell == "valstack"
                && before.spelling() == "Stack :: Cons (rhs , Stack :: Cons (lhs , rest))"
                && after.spelling() == "rest"
    ));
    let roles = clause
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| anchor.role())
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::RuleLeftCellsField));
    assert!(roles.contains(&ProvenanceRole::RuleRightCellsField));
    assert!(roles.contains(&ProvenanceRole::RuleLeftApplicationHead));
    assert!(roles.contains(&ProvenanceRole::RuleRightReference));
}

#[test]
fn malformed_blocks_fail_at_the_local_construct() {
    for (source, expected) in [
        ("for Expr;", "requires at least one clause"),
        ("for Expr in k; x: X => X;", "not implemented yet"),
        (
            "for Expr; use Op::Add; x: Add(a, b) => a;",
            "only `use Enum::*;`",
        ),
        (
            "for Expr; x: Add(a, b) => a where absent: Int;",
            "unbound subject binding",
        ),
        (
            "for Expr; x: Add(a, b) => a; x: Add(a, b) => b;",
            "duplicate readable rule",
        ),
        (
            "for Expr; x: Wrap(a) => a where have env[a -> let v], have env[a -> let w];",
            "duplicate extra-cell mention",
        ),
        (
            "for Expr; x: Wrap(a) => a where have env[a -> v];",
            "expected `let`",
        ),
        (
            "for Expr; x: Wrap(a) => a where have env[a => let v];",
            "`=>` is reserved for rewrites; map entries use `->`",
        ),
        (
            "for Machine; x: { computation: [a, ..], env: { a => v, .. } } => { computation: [a, ..] };",
            "`=>` is reserved for rewrites; map entries use `->`",
        ),
        (
            "for Machine; x: { computation: [a, ..], stack: Cons(v, rest) } => { computation: [a, ..] };",
            "ordinary fixed-cell pattern requires a corresponding result",
        ),
        (
            "for Expr; x: Wrap(a) => a where update env = map::lookup(env, a);",
            "requires exactly three arguments",
        ),
        (
            "for Expr; x: Wrap(a) => a where update env = map::update(other, a, a);",
            "update base must be the cell `env`",
        ),
        (
            "for Expr; x: Wrap(a) => k![a, ..tail];",
            "implicit preserved tail",
        ),
    ] {
        let error = krs_syntax::RuleBlock::parse_source(source).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "expected {expected:?} in {error}"
        );
    }
}

#[test]
fn map_update_head_identity_is_deferred_to_rust_resolution() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Expr; x: Wrap(a) => a where update env = aliased(env, a, a);",
    )
    .unwrap();
    let [RuleExtra::UpdateMap { update, .. }] = block.clauses()[0].extras() else {
        panic!("expected one map update")
    };
    assert_eq!(update.term().spelling(), "aliased (env , a , a)");
}

#[test]
fn reserved_binder_diagnostics_survive_readable_rule_parsing() {
    use krs_diagnostic::{ToDiagnostic, codes};

    for spelling in ["__krs_wildcard_1", "_x__krs_3", "a__krs_b"] {
        for source in [
            format!("for Expr; x: Wrap({spelling}) => true;"),
            format!("for Expr; x: term!(Wrap({spelling})) => true;"),
            format!("for Expr; x: Wrap(a) => true where have env[a -> let {spelling}];"),
            format!(
                "for Expr; x: Wrap(a) => true where update {spelling} = map::update({spelling}, a, a);"
            ),
            format!(
                "for Machine; x: {{ computation: [Wrap(a), ..], env: {{ a -> {spelling}, .. }} }} => {{ computation: [a, ..] }};"
            ),
            format!(
                "for Machine; x: {{ computation: [Wrap(a), ..], env: {spelling} }} => {{ computation: [a, ..], env: map::update({spelling}, a, a) }};"
            ),
        ] {
            let error = krs_syntax::RuleBlock::parse_source(&source).unwrap_err();
            assert_eq!(
                error.to_diagnostic().code,
                codes::syntax::RESERVED_BINDER,
                "{source}"
            );
            assert_eq!(
                error.span().start().column,
                source.find(spelling).unwrap(),
                "{source}"
            );
            assert!(error.to_string().contains("__krs_"));
            assert!(
                error
                    .to_string()
                    .contains("reserved for generated identifiers")
            );
        }
    }
}

#[test]
fn reserved_anonymous_spelling_diagnostics_survive_readable_rule_parsing() {
    use krs_diagnostic::{ToDiagnostic, codes};

    for spelling in ["__krs_wildcard_1", "_x__krs_3"] {
        for source in [
            format!("for Expr; x: Wrap(a) => k::anonymous!(Expr, \"{spelling}\");"),
            format!(
                "for Expr; x: Wrap(a) => true where have env[k::anonymous!(Expr, \"{spelling}\") -> let value];"
            ),
            format!(
                "for Machine; x: {{ computation: [Wrap(a), ..] }} => {{ computation: [k::anonymous!(Expr, \"{spelling}\"), ..] }};"
            ),
        ] {
            let error = krs_syntax::RuleBlock::parse_source(&source).unwrap_err();
            assert_eq!(
                error.to_diagnostic().code,
                codes::syntax::RESERVED_BINDER,
                "{source}"
            );
            assert_eq!(
                error.span().start().column,
                source.find('"').unwrap(),
                "{source}"
            );
        }
    }
}

#[test]
fn reserved_marker_remains_allowed_in_readable_item_and_constructor_names() {
    let block = krs_syntax::RuleBlock::parse_source(
        "for Expr; __krs_rule: __krs_constructor(a) => a; __krs_unit_rule: model::__krs_unit => true;",
    )
    .unwrap();
    assert_eq!(block.clauses().len(), 2);
    assert_eq!(block.clauses()[0].bindings(), ["a"]);
    assert!(block.clauses()[1].bindings().is_empty());
}

#[test]
fn readable_patterns_and_results_accept_negative_int_literals() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Expr;
        use Op::*;

        div_by_minus_one: Div { lhs, rhs: -1 } => int::sub(0, lhs);
        sign:             Sgn(-12)              => -1;
        ",
    )
    .unwrap();
    let pattern = &block.clauses()[0].rule().parameter().pattern;
    assert_eq!(pattern.bindings(), ["lhs"]);
    let anchors = block.clauses()[1].rule().full_provenance().unwrap();
    let literal = |role| {
        anchors
            .iter()
            .find(|anchor| anchor.role() == role)
            .map(|anchor| (anchor.range().start().column, anchor.range().end().column))
            .unwrap()
    };
    // `-12` and `-1` are each one literal anchor that starts at the sign.
    let left = literal(ProvenanceRole::RuleLeftLiteral);
    assert_eq!(left.1 - left.0, 3);
    let right = literal(ProvenanceRole::RuleRightLiteral);
    assert_eq!(right.1 - right.0, 2);
}

#[test]
fn readable_patterns_reject_negative_zero() {
    let error = krs_syntax::RuleBlock::parse_source(
        r"
        for Expr;
        use Op::*;

        zero: Sgn(-0) => 0;
        ",
    )
    .unwrap_err();
    assert!(error.to_string().contains("write 0"), "{error}");
}

#[test]
fn readable_patterns_match_string_literals() {
    let block = krs_syntax::RuleBlock::parse_source(
        r#"
        for Exp;
        use Greeting::*;

        greet_world: Greet("world") => "hello, world";
        greet_raw:   Greet(r"a\b")  => "raw";
        "#,
    )
    .unwrap();
    assert_eq!(block.clauses().len(), 2);
    assert!(
        block.clauses()[0]
            .rule()
            .parameter()
            .pattern
            .bindings()
            .is_empty()
    );
    let error = krs_syntax::RuleBlock::parse_source(
        r#"
        for Exp;
        use Greeting::*;

        wide: Greet("\u{100}") => "no";
        "#,
    )
    .unwrap_err();
    assert!(error.to_string().contains("U+00FF"), "{error}");
}
