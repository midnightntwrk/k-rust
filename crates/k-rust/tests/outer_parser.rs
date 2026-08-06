use indoc::indoc;
use k_rust::outer::{check_list_declarations, parse};
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

proptest! {
    #[test]
    fn arbitrary_source_never_panics(source in any::<String>()) {
        let _ = parse("fuzz.k", &source);
    }
}
