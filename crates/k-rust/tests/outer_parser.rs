use indoc::indoc;
use k_rust::outer::{check_brackets, check_list_declarations, lower, parse};
use proptest::prelude::*;

macro_rules! outer_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let parsed = parse(concat!(stringify!($name), ".k"), $source).unwrap();
            insta::assert_debug_snapshot!(parsed);
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
    let parsed = parse(
        "lists.k",
        indoc! {r#"
        module LISTS
          syntax K ::= List{Exp, ","}
          syntax Loop ::= List{Loop, ","}
          syntax Exps ::= "[" List{Exp, ","} "]"
          syntax Good ::= NeList{Exp, ","}
        endmodule
    "#},
    )
    .unwrap();

    insta::assert_debug_snapshot!(check_list_declarations(&parsed));
}

#[test]
fn comments_and_escaped_literals_are_lexed_without_losing_spans() {
    let parsed = parse(
        "trivia.k",
        indoc! {r#"
        // file comment
        module TRIVIA /* module comment */
          syntax Text ::= "line\n\"quoted\"" // sentence comment
          rule X /* inside the bubble */ => X
        endmodule
    "#},
    )
    .unwrap();

    insta::assert_debug_snapshot!(parsed);
}

#[test]
fn pinned_outer_corpus_families_parse_and_lower() {
    let source = include_str!("fixtures/outer/record-and-list.k");
    let parsed = parse("record-and-list.k", source).unwrap();

    insta::assert_debug_snapshot!("pinned_outer_corpus", parsed);
    insta::assert_debug_snapshot!(
        "pinned_outer_lowering",
        lower(&parsed, "OUTER-CORPUS").unwrap()
    );
}

#[test]
fn bracket_checks_run_before_lowering() {
    let parsed = parse(
        "brackets.k",
        indoc! {r#"
            module BRACKETS
              syntax Exp ::= "(" Int ")" [bracket]
                         | "[" Exp Exp "]" [bracket]
                         | "{" Exp "}" [bracket]
            endmodule
        "#},
    )
    .unwrap();

    let diagnostics = check_brackets(&parsed);
    insta::assert_debug_snapshot!(diagnostics);
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
