//! Quoted hooks and `k::raw_k!` (KF-037): the escapes from A4.

use krs_ir::RawSentenceKind;
use krs_syntax::{FunctionHook, KrsSyntax, ProvenanceRole, RawKItem, SyntaxErrorKind};

#[test]
fn function_hook_is_a_catalog_path_or_a_quoted_name() {
    let catalog = krs_syntax::FunctionAttribute::parse_source(
        r##"total, sort = Bytes, syntax = "#sha256({value})", hook = krypto::sha256_raw"##,
    )
    .unwrap();
    assert!(matches!(catalog.hook(), Some(FunctionHook::Catalog(_))));
    let quoted = krs_syntax::FunctionAttribute::parse_source(
        r##"total, sort = String, syntax = "#keccak({value})", hook = "KRYPTO.keccak256""##,
    )
    .unwrap();
    let Some(FunctionHook::Quoted(literal)) = quoted.hook() else {
        panic!("a string hook is quoted");
    };
    assert_eq!(literal.value(), "KRYPTO.keccak256");
    assert!(
        quoted
            .provenance()
            .unwrap()
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::FunctionHook)
    );
}

#[test]
fn raw_k_accepts_one_rule_claim_or_context() {
    for (text, kind) in [
        (
            "rule <k> double(I:Int) => I +Int I ... </k> [label(raw-double)]",
            RawSentenceKind::Rule,
        ),
        ("  claim <k> f(1) => 2 ... </k>\n", RawSentenceKind::Claim),
        ("context foo(HOLE, _)", RawSentenceKind::Context),
        ("rule [named]: a => b requires true", RawSentenceKind::Rule),
    ] {
        let item = RawKItem::parse_tokens(format!("{text:?}").parse().unwrap()).unwrap();
        assert_eq!(item.kind(), kind, "{text}");
        assert_eq!(item.text(), text.trim());
        assert_eq!(
            item.provenance().unwrap()[0].role(),
            ProvenanceRole::RawKDeclaration
        );
    }
}

#[test]
fn raw_k_rejects_anything_but_one_sentence() {
    for (text, reason) in [
        ("", "`raw_k!` needs one K sentence; the text is empty"),
        (
            "syntax Foo ::= \"foo\"",
            "`raw_k!` text must start with `rule`, `claim` or `context`, not `syntax`",
        ),
        (
            "module M rule a => b endmodule",
            "`raw_k!` text must start with `rule`, `claim` or `context`, not `module`",
        ),
        (
            "rule a => b rule b => c",
            "`raw_k!` holds exactly one sentence, with no `module`, `endmodule` or `imports`; `rule` starts another",
        ),
        (
            "rule a => b endmodule",
            "`raw_k!` holds exactly one sentence, with no `module`, `endmodule` or `imports`; `endmodule` starts another",
        ),
        (
            "rule a => b imports INT",
            "`raw_k!` holds exactly one sentence, with no `module`, `endmodule` or `imports`; `imports` starts another",
        ),
    ] {
        let error = RawKItem::parse_tokens(format!("{text:?}").parse().unwrap()).unwrap_err();
        assert!(
            matches!(error.kind(), SyntaxErrorKind::RawKShape { reason: actual } if actual == reason),
            "{text}: {error}"
        );
    }
    let error = RawKItem::parse_tokens("rule".parse().unwrap()).unwrap_err();
    assert!(matches!(error.kind(), SyntaxErrorKind::RawKShape { .. }));
}
