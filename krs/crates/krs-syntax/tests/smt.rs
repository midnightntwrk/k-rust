//! SMT translations of functions (KF-044): `smtlib = "sym"` and the checked
//! `smt_hook = "tmpl"` SMT-LIB template of `#[k::function]`.

use krs_syntax::{FunctionSmt, KrsSyntax, ProvenanceRole, SmtTemplateFragment, SyntaxErrorKind};
use syn::Ident;

fn function(source: &str) -> krs_syntax::FunctionAttribute {
    krs_syntax::FunctionAttribute::parse_source(source).unwrap()
}

fn smt_reason(source: &str) -> String {
    let error = krs_syntax::FunctionAttribute::parse_source(source).unwrap_err();
    match error.kind() {
        SyntaxErrorKind::InvalidSmtMetadata { reason } => reason.clone(),
        other => panic!("{source}: expected invalid SMT metadata, got {other:?}"),
    }
}

fn fields(names: &[&str]) -> Vec<Ident> {
    names
        .iter()
        .map(|name| Ident::new(name, proc_macro2::Span::call_site()))
        .collect()
}

fn field_reason(source: &str, names: &[&str]) -> String {
    let error = function(source)
        .validate_smt_fields(&fields(names))
        .unwrap_err();
    match error.kind() {
        SyntaxErrorKind::InvalidSmtMetadata { reason } => reason.clone(),
        other => panic!("{source}: expected invalid SMT metadata, got {other:?}"),
    }
}

#[test]
fn smtlib_keeps_its_symbol_and_provenance() {
    let parsed = function(r#"total, sort = Int, syntax = "h({value})", smtlib = "probeH""#);
    let Some(FunctionSmt::Smtlib(symbol)) = parsed.smt() else {
        panic!("expected smtlib");
    };
    assert_eq!(symbol.value(), "probeH");
    let roles = parsed
        .provenance()
        .unwrap()
        .iter()
        .map(krs_syntax::ProvenanceAnchor::role)
        .collect::<Vec<_>>();
    assert!(roles.contains(&ProvenanceRole::FunctionSmtlib));
    // `smtlib` may be combined with a typed hook (KEVM style).
    let hooked = function(
        r#"total, sort = Int, syntax = "h({value})", hook = krypto::keccak256_raw, smtlib = "keccak""#,
    );
    assert!(hooked.hook().is_some() && hooked.smt().is_some());
}

#[test]
fn smt_hook_splits_text_and_repeated_placeholders() {
    let parsed = function(
        r#"total, sort = Int, syntax = "myAbs({value})", smt_hook = "(ite (< {value} 0) (- 0 {value}) {value})""#,
    );
    let Some(FunctionSmt::Hook(template)) = parsed.smt() else {
        panic!("expected smt_hook");
    };
    assert_eq!(
        template.fragments(),
        &[
            SmtTemplateFragment::Text("(ite (< ".to_owned()),
            SmtTemplateFragment::Field("value".to_owned()),
            SmtTemplateFragment::Text(" 0) (- 0 ".to_owned()),
            SmtTemplateFragment::Field("value".to_owned()),
            SmtTemplateFragment::Text(") ".to_owned()),
            SmtTemplateFragment::Field("value".to_owned()),
            SmtTemplateFragment::Text(")".to_owned()),
        ]
    );
    parsed.validate_smt_fields(&fields(&["value"])).unwrap();
    let placeholders = parsed
        .provenance()
        .unwrap()
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::SmtHookPlaceholder)
        .map(krs_syntax::ProvenanceAnchor::ordinal)
        .collect::<Vec<_>>();
    assert_eq!(placeholders, [0, 1, 2]);
    // std `format!` escaping spells literal braces.
    let escaped = function(r#"total, sort = Int, syntax = "f({x})", smt_hook = "(g {{x}} {x})""#);
    let Some(FunctionSmt::Hook(template)) = escaped.smt() else {
        panic!("expected smt_hook");
    };
    assert_eq!(
        template.fragments()[0],
        SmtTemplateFragment::Text("(g {x} ".to_owned())
    );
}

#[test]
fn smt_keys_are_exclusive_string_literals() {
    assert!(
        smt_reason(r#"total, sort = Int, syntax = "h({x})", smtlib = "h", smt_hook = "(+ {x} 1)""#)
            .contains("mutually exclusive")
    );
    assert!(
        smt_reason(r#"total, sort = Int, syntax = "h({x})", smt_hook = "(+ {x} 1)", smtlib = "h""#)
            .contains("mutually exclusive")
    );
    let duplicate = krs_syntax::FunctionAttribute::parse_source(
        r#"total, sort = Int, syntax = "h({x})", smtlib = "h", smtlib = "g""#,
    )
    .unwrap_err();
    assert_eq!(
        duplicate.kind(),
        &SyntaxErrorKind::DuplicateArgument { name: "smtlib" }
    );
    let value = krs_syntax::FunctionAttribute::parse_source(
        r#"total, sort = Int, syntax = "h({x})", smtlib = probeH"#,
    )
    .unwrap_err();
    assert_eq!(
        value.kind(),
        &SyntaxErrorKind::InvalidArgumentValue {
            name: "smtlib",
            expected: "a string literal",
        }
    );
}

#[test]
fn smtlib_is_a_nonempty_simple_symbol() {
    assert!(
        smt_reason(r#"total, sort = Int, syntax = "h({x})", smtlib = """#)
            .contains("must not be empty")
    );
    for symbol in ["1h", "probe h", "(h)", "h|x"] {
        let reason = smt_reason(&format!(
            r#"total, sort = Int, syntax = "h({{x}})", smtlib = "{symbol}""#
        ));
        assert!(
            reason.contains("is not an SMT-LIB simple symbol"),
            "{symbol}: {reason}"
        );
    }
    for symbol in ["probeH", "list-size", "~x.y?", "a1"] {
        function(&format!(
            r#"total, sort = Int, syntax = "h({{x}})", smtlib = "{symbol}""#
        ));
    }
}

#[test]
fn smt_hook_templates_are_balanced_and_unquoted() {
    let cases = [
        (r#"smt_hook = """#, "must not be empty"),
        (r#"smt_hook = "(+ {x} 1""#, "unclosed `(`"),
        (r#"smt_hook = "(+ {x} 1))""#, "unmatched `)`"),
        (r#"smt_hook = "(str.++ {x} \"a\")""#, "cannot contain `\"`"),
        (r#"smt_hook = "(+ {x 1)""#, "no closing `}`"),
        (r#"smt_hook = "(+ {} 1)""#, "one Rust field identifier"),
    ];
    for (key, expected) in cases {
        let reason = smt_reason(&format!(r#"total, sort = Int, syntax = "h({{x}})", {key}"#));
        assert!(reason.contains(expected), "{key}: {reason}");
    }
}

#[test]
fn smt_hook_placeholders_name_fields() {
    let unknown = field_reason(
        r#"total, sort = Int, syntax = "myAbs({value})", smt_hook = "(ite (< {valeu} 0) 0 1)""#,
        &["value"],
    );
    assert!(
        unknown.contains("`{valeu}` names no field") && unknown.contains("did you mean `{value}`?"),
        "{unknown}"
    );
    let positional = field_reason(
        r#"total, sort = Int, syntax = "sub({low}, {high})", smt_hook = "(- #2 {low})""#,
        &["low", "high"],
    );
    assert!(
        positional.contains("`#2` is K's positional placeholder")
            && positional.contains("did you mean `{high}`?"),
        "{positional}"
    );
    // A field need not occur: the template is a meaning, not concrete syntax.
    function(r#"total, sort = Int, syntax = "k({x}, {y})", smt_hook = "{x}""#)
        .validate_smt_fields(&fields(&["x", "y"]))
        .unwrap();
}
