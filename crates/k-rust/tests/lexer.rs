// Ported from pyk's BSD-3-Clause-licensed KORE lexer tests.

use kore_rs::lexer::{TokenKind, lex};

fn kinds(input: &str) -> Vec<TokenKind> {
    lex(input)
        .unwrap_or_else(|error| panic!("failed to lex {input:?}: {error}"))
        .into_iter()
        .map(|token| token.kind)
        .collect()
}

#[test]
fn lexes_trivia_and_identifiers() {
    let cases = [
        ("", vec![]),
        (" ", vec![]),
        ("//", vec![]),
        ("/**/", vec![]),
        ("/*///***/", vec![]),
        ("/* comment */", vec![]),
        ("xyz", vec![TokenKind::Id]),
        ("x-y'z", vec![TokenKind::Id]),
        ("   xyz\n", vec![TokenKind::Id]),
        ("\\xyz", vec![TokenKind::SymbolId]),
        ("@xyz", vec![TokenKind::SetVarId]),
        ("module", vec![TokenKind::Module]),
        ("a b c", vec![TokenKind::Id, TokenKind::Id, TokenKind::Id]),
        (
            "sort Map{K, V} []",
            vec![
                TokenKind::Sort,
                TokenKind::Id,
                TokenKind::LBrace,
                TokenKind::Id,
                TokenKind::Comma,
                TokenKind::Id,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
            ],
        ),
    ];

    for (input, expected) in cases {
        assert_eq!(kinds(input), expected, "input: {input:?}");
    }
}

#[test]
fn rejects_invalid_or_truncated_tokens() {
    for input in ["-a", "'a", "*", "/*", "\\", "@", "\\@"] {
        assert!(lex(input).is_err(), "expected {input:?} to fail");
    }
}

#[test]
fn recognizes_all_keywords_and_ml_symbols() {
    let input = "endmodule import hooked-sort symbol hooked-symbol axiom claim alias where \\top \\bottom \\not \\and \\or \\implies \\iff \\exists \\forall \\mu \\nu \\ceil \\floor \\equals \\in \\next \\rewrites \\dv \\left-assoc \\right-assoc";
    let expected = [
        TokenKind::EndModule,
        TokenKind::Import,
        TokenKind::HookedSort,
        TokenKind::Symbol,
        TokenKind::HookedSymbol,
        TokenKind::Axiom,
        TokenKind::Claim,
        TokenKind::Alias,
        TokenKind::Where,
        TokenKind::MlTop,
        TokenKind::MlBottom,
        TokenKind::MlNot,
        TokenKind::MlAnd,
        TokenKind::MlOr,
        TokenKind::MlImplies,
        TokenKind::MlIff,
        TokenKind::MlExists,
        TokenKind::MlForall,
        TokenKind::MlMu,
        TokenKind::MlNu,
        TokenKind::MlCeil,
        TokenKind::MlFloor,
        TokenKind::MlEquals,
        TokenKind::MlIn,
        TokenKind::MlNext,
        TokenKind::MlRewrites,
        TokenKind::MlDv,
        TokenKind::MlLeftAssoc,
        TokenKind::MlRightAssoc,
    ];
    assert_eq!(kinds(input), expected);
}

#[test]
fn preserves_text_and_byte_offsets() {
    let tokens = lex("  module α").expect_err("non-ASCII identifiers are not KORE identifiers");
    assert_eq!(tokens.offset, 9);

    let tokens = lex("  module X").unwrap();
    assert_eq!(tokens[0].text, "module");
    assert_eq!(tokens[0].offset, 2);
    assert_eq!(tokens[1].text, "X");
    assert_eq!(tokens[1].offset, 9);
}
