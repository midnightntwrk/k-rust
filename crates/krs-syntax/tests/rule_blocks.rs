//! Readable term-rule family parser coverage.

use krs_syntax::{ProvenanceRole, RuleExtra, RuleHeadResult, parse_rule_block_source};

#[test]
fn nonlinear_subject_bindings_are_one_catalog_entry_with_repeated_occurrences() {
    let block = parse_rule_block_source(
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
    let block = parse_rule_block_source(
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

    assert_eq!(block.sort().sort_spelling(), "Expr");
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

    let anchors = block.clauses()[0].rule().m3a_provenance().unwrap();
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
    let block = parse_rule_block_source(
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
    let block = parse_rule_block_source(
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
        RuleHeadResult::Splice { items, .. } if items.len() == 2
    ));
    assert!(matches!(
        block.clauses()[1].head_result(),
        RuleHeadResult::Erase(_)
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

    let block = parse_rule_block_source(
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
    let block = parse_rule_block_source(
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
    assert_eq!(block.sort().sort_spelling(), "Machine");
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
    let block = parse_rule_block_source(
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
        let error = parse_rule_block_source(source).unwrap_err();
        assert!(
            error.to_string().contains(expected),
            "expected {expected:?} in {error}"
        );
    }
}

#[test]
fn map_update_head_identity_is_deferred_to_rust_resolution() {
    let block =
        parse_rule_block_source("for Expr; x: Wrap(a) => a where update env = aliased(env, a, a);")
            .unwrap();
    let [RuleExtra::UpdateMap { update, .. }] = block.clauses()[0].extras() else {
        panic!("expected one map update")
    };
    assert_eq!(update.spelling(), "aliased (env , a , a)");
}
