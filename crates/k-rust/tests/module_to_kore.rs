use indoc::indoc;
use k_rust::kompile::{
    declaration_modules, encode_kore_identifier, encode_kore_label, encode_kore_sort,
};
use k_rust::kore::parser::parse_module;
use k_rust::kore::printer::Printer;
use k_rust::{kast, outer};

fn lowered(source: &str, main_module: &str) -> k_rust::definition::Definition {
    let parsed = outer::parse("declarations.k", source).expect("definition should parse");
    outer::lower(&parsed, main_module).expect("definition should lower")
}

macro_rules! declaration_snapshot {
    ($name:ident, $source:expr, $module:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let declarations = declaration_modules(&lowered(source, $module), $module)
                .expect("declarations should emit");
            let printer = Printer::pretty(120);
            let semantics = printer.print_module(&declarations.semantics);
            let syntax = printer.print_module(&declarations.syntax);
            assert_eq!(
                parse_module(&semantics).expect("semantic declarations should reparse"),
                declarations.semantics,
            );
            assert_eq!(
                parse_module(&syntax).expect("syntax declarations should reparse"),
                declarations.syntax,
            );
            let emitted = format!("// semantics\n{semantics}\n\n// syntax\n{syntax}");
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(emitted);
            });
        }
    };
}

declaration_snapshot!(
    emits_sort_and_symbol_declarations,
    r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Exp
          syntax Bool

          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Exp "*" Exp [left, symbol(_*_)]
                       > Exp "+" Exp [left, symbol(_+_)]
                       | "box(" value:Int ")" [color(red), format(%1 %2 %3), symbol(box)]
          syntax Bool ::= Exp "==" Exp [function, hook(KEQUAL.eq), symbol(eq), total]
        endmodule
    "#,
    "MAIN"
);

declaration_snapshot!(
    emits_visible_imported_declarations_in_scala_order,
    r#"
        module BASE
          syntax Atom ::= "atom" [symbol(atom)]
        endmodule

        module MAIN
          imports BASE
          syntax Result ::= "wrap" Atom [symbol(wrap)]
          syntax Result ::= "done" [symbol(done)]
        endmodule
    "#,
    "MAIN"
);

declaration_snapshot!(
    emits_parametric_declarations,
    r#"
        module MAIN
          syntax {S} Box{S}
          syntax {S} Box{S} ::= "box(" S ")" [symbol(box)]
        endmodule
    "#,
    "MAIN"
);

declaration_snapshot!(
    derives_hooked_collection_sort_attributes,
    r#"
        module MAIN
          syntax Map [hook(MAP.Map)]
          syntax MapItem
          syntax Map ::= ".Map" [function, hook(MAP.unit), symbol(.Map), total]
          syntax Map ::= Map Map [element(MapItem), symbol(_Map_), unit(.Map)]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn encodes_java_kore_identifier_edge_cases() {
    assert_eq!(encode_kore_identifier("_+_"), "'UndsPlusUnds'");
    assert_eq!(
        encode_kore_identifier("<generatedTop>-fragment"),
        "'-LT-'generatedTop'-GT-'-fragment"
    );
    assert_eq!(encode_kore_identifier("_|->_"), "'UndsPipe'-'-GT-Unds'");
    assert_eq!(encode_kore_identifier("module"), "module'Kywd'");
    assert_eq!(encode_kore_identifier("éα"), "'00e903b1'");
    assert_eq!(encode_kore_identifier("😀"), "'d83dde00'");
    assert_eq!(encode_kore_identifier("\n"), "'000a'");
}

#[test]
fn encodes_labels_and_parametric_sorts() {
    assert_eq!(
        encode_kore_label(&kast::Label::new("inj")).to_string(),
        "inj{}"
    );
    let label = kast::Label::with_parameters("box(_)", vec![kast::Sort::new("S")]);
    assert_eq!(
        encode_kore_label(&label).to_string(),
        "Lblbox'LParUndsRPar'{SortS{}}"
    );
    let sort = kast::Sort::with_parameters(
        "Map",
        vec![kast::Sort::new("Key"), kast::Sort::new("Value")],
    );
    assert_eq!(
        encode_kore_sort(&sort).to_string(),
        "SortMap{SortKey{}, SortValue{}}"
    );
}
