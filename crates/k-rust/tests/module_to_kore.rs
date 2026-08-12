use indoc::indoc;
use k_rust::kompile::{
    declaration_modules, encode_kore_identifier, encode_kore_label, encode_kore_sort,
    module_to_kore,
};
use k_rust::kore::parser::{parse_module, parse_sentence};
use k_rust::kore::printer::Printer;
use k_rust::{kast, outer};

fn lowered(source: &str, main_module: &str) -> k_rust::definition::Definition {
    let parsed = outer::parse("declarations.k", source).expect("definition should parse");
    outer::lower(&parsed, main_module).expect("definition should lower")
}

fn rules(source: &str, main_module: &str) -> k_rust::definition::Definition {
    k_rust::inner::resolve_rule_bubbles(&lowered(source, main_module))
        .expect("rule bubbles should resolve")
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

macro_rules! module_snapshot {
    ($name:ident, $source:expr, $module:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let modules = module_to_kore(&rules(source, $module), $module)
                .expect("KORE modules should emit");
            let printer = Printer::pretty(100);
            let semantics = printer.print_module(&modules.semantics);
            let syntax = printer.print_module(&modules.syntax);
            let macros = modules
                .macros
                .iter()
                .map(|sentence| printer.print_sentence(sentence))
                .collect::<Vec<_>>()
                .join("\n\n");
            assert_eq!(
                parse_module(&semantics).expect("semantic module should reparse"),
                modules.semantics,
            );
            assert_eq!(
                parse_module(&syntax).expect("syntax module should reparse"),
                modules.syntax,
            );
            for (source, sentence) in macros.split("\n\n").zip(&modules.macros) {
                assert_eq!(
                    parse_sentence(source).expect("macro sentence should reparse"),
                    *sentence,
                );
            }
            let emitted = format!(
                "// semantics\n{semantics}\n\n// syntax\n{syntax}\n\n// macros\n{macros}"
            );
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

module_snapshot!(
    emits_ordinary_rewrite_rules_and_claims,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]
          syntax GeneratedTopCell ::= "<top>" Exp "</top>" [symbol(top)]

          rule <top> X:Exp + 0 </top> => <top> X:Exp </top>
            requires X:Exp == 0
            ensures X:Exp == 1
            [label(step), priority(42)]

          claim <top> X:Exp </top> => <top> ?Y:Exp </top>
            ensures ?Y:Exp == X:Exp
            [label(reachable)]

          claim <top> X:Exp </top>
            requires X:Exp == 0
            [label(invariant)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_function_anywhere_and_simplification_equations,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Exp ::= "inc(" Exp ")" [function, symbol(inc)]
          syntax Exp ::= "double(" Exp ")" [symbol(double)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]

          rule inc(X:Exp + 0) => X:Exp
            requires X:Exp == 1
            ensures X:Exp == 2
            [label(eval-inc)]

          rule X:Exp + 0 => X:Exp
            [simplification, label(plus-zero)]

          rule double(X:Exp + 0) => double(X:Exp)
            [anywhere, label(double-zero)]

          claim inc(X:Exp) => X:Exp
            [label(inc-claim)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_owise_equations_with_refreshed_competitors,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "choose(" Exp "," Exp ")" [function, symbol(choose)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]

          rule choose(0, Y:Exp) => Y:Exp
            [label(left-zero)]

          rule choose(X:Exp, 0) => X:Exp
            requires X:Exp == 1
            [label(right-zero)]

          rule choose(X:Exp, Y:Exp) => X:Exp
            requires X:Exp == Y:Exp
            [label(equal-arguments)]

          rule choose(1, Z:Exp) => Z:Exp
            [non-executable, label(ignored-non-executable)]

          rule choose(A:Exp, B:Exp) => A:Exp
            [simplification, label(ignored-simplification)]

          rule choose(_Gen0:Exp, Y:Exp) => Y:Exp
            requires _Gen0:Exp == Y:Exp
            [owise, label(otherwise)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    routes_macro_and_alias_axioms_to_the_standalone_sentence_list,
    r#"
        module MAIN
          syntax Exp ::= "done(" Exp ")" [symbol(done)]
          syntax Exp ::= "plain(" Exp ")" [symbol(plain)]
          syntax Exp ::= "macro(" Exp ")" [macro, symbol(macro)]
          syntax Exp ::= "macroRec(" Exp ")" [macro-rec, symbol(macroRec)]
          syntax Exp ::= "alias(" Exp ")" [alias, symbol(alias)]
          syntax Exp ::= "aliasRec(" Exp ")" [alias-rec, symbol(aliasRec)]
          syntax Exp ::= "functionMacro(" Exp ")" [function, macro, symbol(functionMacro)]

          rule macro(X:Exp) => done(X:Exp)
          rule macroRec(X:Exp) => done(X:Exp)
          rule alias(X:Exp) => done(X:Exp)
          rule aliasRec(X:Exp) => done(X:Exp)
          rule functionMacro(X:Exp) => done(X:Exp)
          rule plain(X:Exp) => done(X:Exp) [macro, priority(17)]
          rule macro(done(X:Exp)) => X:Exp [simplification]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_one_path_and_all_path_reachability_claims,
    r#"
        module MAIN [all-path]
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]
          syntax GeneratedTopCell ::= "<top>" Exp "</top>" [symbol(top)]

          claim <top> X:Exp </top> => <top> ?Y:Exp </top>
            requires X:Exp == 0
            ensures ?Y:Exp == X:Exp
            [one-path, label(one-step)]

          claim <top> X:Exp </top> => <top> X:Exp </top>
            [all-path, label(all-step)]

          claim <top> X:Exp </top> => <top> X:Exp </top>
            [label(module-default)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    propagates_impurity_through_function_dependencies,
    r#"
        module MAIN
          syntax Exp ::= "done" [symbol(done)]
          syntax Exp ::= "source" [function, impure, symbol(source)]
          syntax Exp ::= "middle" [function, symbol(middle)]
          syntax Exp ::= "top" [function, symbol(top)]
          syntax Exp ::= "clean" [function, symbol(clean)]
          syntax Exp ::= "guarded" [function, symbol(guarded)]
          syntax Bool ::= "isDone(" Exp ")" [function, symbol(isDone)]
          syntax Exp ::= "impureAnywhere(" Exp ")" [impure, symbol(impureAnywhere)]
          syntax Exp ::= "usesAnywhere" [function, symbol(usesAnywhere)]
          syntax Exp ::= "macroAnywhere(" Exp ")" [impure, symbol(macroAnywhere)]
          syntax Exp ::= "usesMacroAnywhere" [function, symbol(usesMacroAnywhere)]

          rule source => done
          rule middle => source
          rule top => middle
          rule clean => done
          rule guarded => done requires isDone(source)
          rule impureAnywhere(X:Exp) => X:Exp [anywhere]
          rule usesAnywhere => impureAnywhere(done)
          rule macroAnywhere(X:Exp) => X:Exp [anywhere, macro]
          rule usesMacroAnywhere => macroAnywhere(done)
        endmodule
    "#,
    "MAIN"
);

#[test]
fn rejects_non_top_cell_semantic_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          rule 0 => 1
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "ordinary semantic rules must rewrite GeneratedTopCell, found Int"
    );
}

#[test]
fn rejects_existential_variables_in_equations() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "inc(" Exp ")" [function, symbol(inc)]
          rule inc(X:Exp) => ?Y:Exp
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot encode equations with existential variables: ?Y"
    );
}

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
