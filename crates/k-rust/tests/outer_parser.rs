use indoc::indoc;
use k_rust::outer::{check_brackets, check_list_declarations, lower, parse};
use proptest::prelude::*;

macro_rules! assert_outer_value_snapshot {
    ($source:expr, $value:expr) => {{
        let source = $source;
        let value = $value;
        insta::with_settings!({
            description => format!("K source:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(value);
        });
    }};
}

macro_rules! outer_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = $source;
            let parsed = parse(concat!(stringify!($name), ".k"), source).unwrap();
            assert_outer_value_snapshot!(source, parsed);
        }
    };
}

outer_snapshot!(
    modules_and_imports,
    indoc! {r#"
    requires "domains.md"

    module COLLECTIONS [main]
      imports public BOOL
      imports private MAP
      syntax Exp
    endmodule
"#}
);

outer_snapshot!(
    syntax_declarations,
    indoc! {r#"
    module SYNTAX
      syntax {S} List{S}
      syntax NonEmpty = List
      syntax Id ::= r"[a-zA-Z][a-zA-Z0-9]*" [token]
      syntax Exps ::= List{Exp, ","} [klabel(exps)]
      syntax Exp ::= left: Exp "+" Exp [left, klabel(_+_)]
                   | name:Id
                   > "(" Exp ")" [bracket]
      syntax priority _*_ > _+_ _-_
      syntax left _+_ _-_
      syntax lexical Identifier = r"[a-z]+" [prec(1)]
    endmodule
"#}
);

outer_snapshot!(
    bubbles,
    indoc! {r#"
    module RULES
      rule [identity]: X + 0 => X [simplification]
      claim <k> P => Q </k> requires true [trusted]
      context HOLE + X
      context alias HERE [X] = HOLE
      configuration <k> $PGM:Exp </k>
    endmodule
"#}
);

#[test]
fn list_declaration_checks_match_the_frontend_categories() {
    let source = indoc! {r#"
        module LISTS
          syntax K ::= List{Exp, ","}
          syntax Loop ::= List{Loop, ","}
          syntax Exps ::= "[" List{Exp, ","} "]"
          syntax Good ::= NeList{Exp, ","}
        endmodule
    "#};
    let parsed = parse("lists.k", source).unwrap();

    assert_outer_value_snapshot!(source, check_list_declarations(&parsed));
}

#[test]
fn comments_and_escaped_literals_are_lexed_without_losing_spans() {
    let source = indoc! {r#"
        // file comment
        module TRIVIA /* module comment */
          syntax Text ::= "line\n\"quoted\"" // sentence comment
          rule X /* inside the bubble */ => X
        endmodule
    "#};
    let parsed = parse("trivia.k", source).unwrap();

    assert_outer_value_snapshot!(source, parsed);
}

#[test]
fn pinned_outer_corpus_families_parse_and_lower() {
    let source = include_str!("fixtures/outer/record-and-list.k");
    let parsed = parse("record-and-list.k", source).unwrap();

    insta::with_settings!({
        description => format!("K source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!("pinned_outer_corpus", parsed);
    });
    insta::with_settings!({
        description => format!("K source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(
            "pinned_outer_lowering",
            lower(&parsed, "OUTER-CORPUS").unwrap()
        );
    });
}

#[test]
fn bracket_checks_run_before_lowering() {
    let source = indoc! {r#"
        module BRACKETS
          syntax Exp ::= "(" Int ")" [bracket]
                     | "[" Exp Exp "]" [bracket]
                     | "{" Exp "}" [bracket]
        endmodule
    "#};
    let parsed = parse("brackets.k", source).unwrap();

    let diagnostics = check_brackets(&parsed);
    assert_outer_value_snapshot!(source, diagnostics);
    assert!(lower(&parsed, "BRACKETS").is_err());
}

proptest! {
    #[test]
    fn arbitrary_source_never_panics(source in any::<String>()) {
        if let Ok(parsed) = parse("fuzz.k", &source) {
            let _ = lower(&parsed, "FUZZ");
        }
    }
}
