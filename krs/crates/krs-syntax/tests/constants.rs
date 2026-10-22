//! `#[k::constant]` items and the constant-name rule in patterns.

use krs_syntax::{ConstantItem, KrsSyntax, ProvenanceRole, SyntaxErrorKind};

fn invalid_constant(source: &str) -> String {
    let error = ConstantItem::parse_source(source).unwrap_err();
    let SyntaxErrorKind::InvalidConstant { reason } = error.kind() else {
        panic!("{source}: {error:?}");
    };
    reason.clone()
}

#[test]
fn a_constant_names_a_ground_term_of_a_sort() {
    let constant = ConstantItem::parse_source("pub const IF: Int = 0xFF0F;").unwrap();
    assert_eq!(constant.name(), "IF");
    assert_eq!(constant.sort().sort_token_text(), "Int");
    let roles = constant
        .provenance()
        .unwrap()
        .into_iter()
        .map(|anchor| (anchor.role(), anchor.ordinal()))
        .collect::<Vec<_>>();
    assert_eq!(
        roles,
        [
            (ProvenanceRole::ConstantDeclaration, 0),
            (ProvenanceRole::ConstantType, 0),
            (ProvenanceRole::ConstantValue, 0),
            (ProvenanceRole::RuleRightLiteral, 0),
        ]
    );
    for source in [
        "const START: Instr = Instruction::Jump(IF);",
        "const PAIR: Exp = Pair { left: 1, right: -0x10 };",
        "const ALIAS: Int = crate::io::LCDC;",
        "const NOP: Instr = Nop();",
        "const HALF: Float = 0.5;",
        "const NAME: String = \"main\";",
        "const ON: k::Term<Bool> = true;",
    ] {
        ConstantItem::parse_source(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn a_constant_value_applies_constructors_only() {
    for (source, offending) in [
        ("const X: Int = 1.add::<Int>(2);", "a builtin operation"),
        ("const X: Bool = A && B;", "a builtin operation"),
        ("const X: Int = !1;", "a builtin operation"),
        ("const X: Exp = Choose::<Int>(1);", "turbofish"),
        ("const X: Exp = k::k![1];", "this expression"),
        ("const X: Exp = { 1 };", "this expression"),
    ] {
        let reason = invalid_constant(source);
        assert!(reason.contains(offending), "{source}: {reason}");
    }
}

#[test]
fn a_constant_is_a_non_generic_const_item_of_a_sort() {
    assert!(invalid_constant("static IF: Int = 1;").contains("`const`, not `static`"));
    assert!(invalid_constant("fn f() {}").contains("applies to a `const` item"));
    assert!(invalid_constant("const IF: &str = \"a\";").contains("is a KRS sort"));
}

#[test]
fn a_bare_name_spelled_as_a_constant_binds_nothing() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Exp;
        use Op::*;

        port:  Load(IF, n)        => n;
        word:  Store(WORD_SIZE)   => P2;
        alias: Wrap(v @ Load(IF)) => v;
        ",
    )
    .unwrap();
    let bindings = |index: usize| {
        block.clauses()[index]
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    };
    assert_eq!(bindings(0), ["n"]);
    assert!(bindings(1).is_empty());
    assert_eq!(bindings(2), ["v"]);
    // A lowercase name, misspelled or not, is a binder, as in Rust.
    let block =
        krs_syntax::RuleBlock::parse_source("for Exp; use Op::*; port: Load(iff) => 1;").unwrap();
    assert_eq!(block.clauses()[0].bindings(), ["iff"]);
}

#[test]
fn a_constant_name_in_a_machine_record_and_a_table_row_binds_nothing() {
    let block = krs_syntax::RuleBlock::parse_source(
        r"
        for Machine;
        use Op::*;

        step: { k: [Load(n), ..], pc: PC_START } => { k: [..], pc: n };
        ",
    )
    .unwrap();
    assert_eq!(block.clauses()[0].bindings(), ["n"]);
    let table = krs_syntax::EquationTable::parse_source(
        r"
        for Port;
        port_if: IF => 1;
        port_ie: (IE) => 2;
        #[k::equation(owise)]
        port_other: n => 0;
        ",
    )
    .unwrap();
    let bindings = table
        .rows()
        .iter()
        .map(|row| row.rule().parameter().pattern.bindings().len())
        .collect::<Vec<_>>();
    assert_eq!(bindings, [0, 0, 1]);
}
