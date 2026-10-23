//! Every KRS list, and every macro or attribute argument list, accepts one
//! trailing comma: a comma adds no element, so each form parses to the same
//! value with and without it. A record's `..`/`..base` takes none, as in Rust.

use std::fmt::Debug;

use krs_syntax::KrsSyntax;
use krs_syntax::parse::tokens_from_source;
use krs_syntax::{SyntaxError, TermExpression};

/// The parse result's `Debug` modulo commas: the values keep their authored
/// syn trees, whose token streams and punctuated lists still hold the comma,
/// so comma tokens, `Comma` separators, and token spacing are dropped, and
/// every number (byte offsets after the comma move) is erased. What remains
/// is the structure: every element, binder, node, and range must agree.
fn shape<T: Debug>(value: &T) -> String {
    let text = format!("{value:#?}");
    let lines: Vec<&str> = text.lines().collect();
    let mut kept = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let line = lines[index].trim();
        if line == "Punct {" && lines.get(index + 1).map(|next| next.trim()) == Some("char: ',',") {
            while lines[index].trim() != "}," {
                index += 1;
            }
        } else if line != "Comma," && !line.starts_with("spacing:") {
            kept.push(line);
        }
        index += 1;
    }
    let mut shape = String::with_capacity(text.len());
    let mut digits = false;
    for ch in kept.join("\n").chars() {
        if ch.is_ascii_digit() {
            if !digits {
                shape.push('#');
            }
            digits = true;
        } else {
            digits = false;
            shape.push(ch);
        }
    }
    shape
}

fn same<T: Debug>(parse: impl Fn(&str) -> Result<T, SyntaxError>, without: &str, with: &str) {
    let plain = parse(without).unwrap_or_else(|error| panic!("{without}: {error}"));
    let comma = parse(with).unwrap_or_else(|error| panic!("{with}: {error}"));
    let (plain, comma) = (shape(&plain), shape(&comma));
    if plain != comma {
        let first = plain
            .lines()
            .zip(comma.lines())
            .position(|(a, b)| a != b)
            .unwrap_or(0);
        let context = |text: &str| {
            text.lines()
                .skip(first.saturating_sub(12))
                .take(20)
                .collect::<Vec<_>>()
                .join("\n")
        };
        panic!(
            "{without} vs {with}\n--- without\n{}\n--- with\n{}",
            context(&plain),
            context(&comma)
        );
    }
}

fn rejected<T: Debug>(parse: impl Fn(&str) -> Result<T, SyntaxError>, source: &str) {
    assert!(parse(source).is_err(), "{source} must stay an error");
}

fn term(source: &str) -> Result<TermExpression, SyntaxError> {
    TermExpression::parse_source(source)
}

fn pattern(source: &str) -> Result<TermExpression, SyntaxError> {
    TermExpression::parse_pattern_tokens(tokens_from_source(source)?)
}

fn tokens<T>(
    parse: fn(proc_macro2::TokenStream) -> Result<T, SyntaxError>,
) -> impl Fn(&str) -> Result<T, SyntaxError> {
    move |source| parse(tokens_from_source(source)?)
}

#[test]
fn macro_argument_lists_accept_a_trailing_comma() {
    for (without, with) in [
        ("k::matches!(t, Pair(_, _))", "k::matches!(t, Pair(_, _),)"),
        (r#"k::bytes!(b"\x60\x02")"#, r#"k::bytes!(b"\x60\x02",)"#),
        (r#"k::id!("$x")"#, r#"k::id!("$x",)"#),
        (r#"k::lexeme!(Name, "t")"#, r#"k::lexeme!(Name, "t",)"#),
        (
            r#"k::anonymous!(Int, "_X")"#,
            r#"k::anonymous!(Int, "_X",)"#,
        ),
        ("k::is!(Int, t)", "k::is!(Int, t,)"),
        ("k::project!(Int, t)", "k::project!(Int, t,)"),
        (
            "k::fragment![Frame { pc: p, depth: d }]",
            "k::fragment![Frame { pc: p, depth: d },]",
        ),
        ("Pair(a, b)", "Pair(a, b,)"),
        ("int::add(a, b)", "int::add(a, b,)"),
        ("k::or_bool!(a, b)", "k::or_bool!(a, b,)"),
    ] {
        same(term, without, with);
    }
}

#[test]
fn a_local_rewrite_accepts_a_trailing_comma() {
    same(
        pattern,
        "Wrap(k::rewrite!(a => b))",
        "Wrap(k::rewrite!(a => b,))",
    );
    same(
        pattern,
        "k::fragment![Frame { pc, .. }]",
        "k::fragment![Frame { pc, .. },]",
    );
}

#[test]
fn rule_conditions_and_term_payloads_accept_a_trailing_comma() {
    same(
        krs_syntax::RuleItem::parse_source,
        "#[k::requires(int::gt(value, 0))] fn guarded(Guarded { value }: Term<Expr>) -> Term<Expr> { Done }",
        "#[k::requires(int::gt(value, 0),)] fn guarded(Guarded { value }: Term<Expr>) -> Term<Expr> { Done }",
    );
    same(
        krs_syntax::RuleItem::parse_source,
        "#[k::exists(x: Int)] #[k::ensures(int::lt(x, 5))] fn foo(k::term![Foo()]: k::Term<Exp>) -> k::Term<Exp> { x }",
        "#[k::exists(x: Int)] #[k::ensures(int::lt(x, 5),)] fn foo(k::term![Foo(),]: k::Term<Exp>) -> k::Term<Exp> { x }",
    );
}

#[test]
fn claim_ensures_and_sequences_accept_a_trailing_comma() {
    let claim = |ensures: &str, k: &str, rest: &str| {
        format!(
            r"
            #[k::exists(n: Int)]
            #[k::ensures({ensures})]
            fn readable(
                body: Stmt,
                cells! {{ k: KCell(body, {k}), state @ ..{rest} }}: Machine,
            ) -> Machine {{
                cells! {{ k: KCell(n, ..tail{rest}), ..state{rest} }}
            }}
            "
        )
    };
    same(
        krs_syntax::StateClaimItem::parse_source,
        &claim("int::gt(n, 0)", "tail @ ..", ""),
        &claim("int::gt(n, 0),", "tail @ ..,", ","),
    );
}

#[test]
fn state_macros_accept_a_trailing_comma() {
    for (without, with) in [
        ("a, b", "a, b,"),
        ("a ~> b", "a ~> b,"),
        ("a, ..tail", "a, ..tail,"),
        (".K", ".K,"),
    ] {
        same(
            tokens(krs_syntax::parse_k_sequence_expression),
            without,
            with,
        );
    }
    for (without, with) in [("x, tail @ ..", "x, tail @ ..,"), ("x, ..", "x, ..,")] {
        same(tokens(krs_syntax::parse_k_sequence_pattern), without, with);
    }
    for (without, with) in [
        ("k -> v, ..", "k -> v, ..,"),
        ("k -> v, rest @ ..", "k -> v, rest @ ..,"),
    ] {
        same(tokens(krs_syntax::parse_map_pattern), without, with);
    }
    same(
        tokens(krs_syntax::parse_map_expression),
        "a -> 1, b -> 2",
        "a -> 1, b -> 2,",
    );
    for (without, with) in [
        (
            "k: KCell(x, tail @ ..), state @ ..",
            "k: KCell(x, tail @ ..,), state @ ..,",
        ),
        ("k: KCell(x, ..), ..", "k: KCell(x, ..,), ..,"),
        ("env: Cell(e), ..", "env: Cell(e,), ..,"),
    ] {
        same(tokens(krs_syntax::parse_cells_pattern), without, with);
    }
    same(
        tokens(krs_syntax::parse_cells_expression),
        "k: KCell(x, ..tail), ..state",
        "k: KCell(x, ..tail,), ..state,",
    );
}

#[test]
fn lists_ended_by_a_semicolon_accept_a_trailing_comma() {
    same(
        krs_syntax::RuleBlock::parse_source,
        "for Expr; eq: Eq { lhs, rhs } => int::eq(lhs, rhs) where lhs: Int, rhs: Int;",
        "for Expr; eq: Eq { lhs, rhs } => int::eq(lhs, rhs) where lhs: Int, rhs: Int,;",
    );
    same(
        krs_syntax::SortsDeclaration::parse_source,
        "impl Value for Int, Bool;",
        "impl Value for Int, Bool,;",
    );
}

#[test]
fn attribute_payloads_accept_a_trailing_comma() {
    same(
        krs_syntax::BracketAttribute::parse_source,
        r#""[", "]""#,
        r#""[", "]","#,
    );
    same(
        krs_syntax::SymbolAttribute::parse_source,
        r#""api::Probe""#,
        r#""api::Probe","#,
    );
    same(
        krs_syntax::DesugarAttribute::parse_source,
        "unbound_variables = [n]",
        "unbound_variables = [n],",
    );
    for mode in [
        krs_syntax::StaticMode::Alias,
        krs_syntax::StaticMode::Desugar,
    ] {
        same(
            |source| {
                krs_syntax::StaticProductionAttribute::parse_marker(
                    mode,
                    tokens_from_source(source)?,
                )
            },
            "recursive",
            "recursive,",
        );
    }
    same(
        krs_syntax::EnumConstructorDeclaration::parse_source,
        r#"#[k::constructors(sort = Stmt, result = KResult)]
        #[k::precedence((Block))]
        pub enum Family {
            #[k::syntax("{{{body}}}")]
            #[k::format("{{%i%n{body}%d%n}}")]
            Block { body: Stmt },
        }"#,
        r#"#[k::constructors(sort = Stmt, result = KResult)]
        #[k::precedence((Block))]
        pub enum Family {
            #[k::syntax("{{{body}}}")]
            #[k::format("{{%i%n{body}%d%n}}",)]
            Block { body: Stmt },
        }"#,
    );
    same(
        |source| {
            krs_syntax::FunctionShorthand::lower(
                tokens_from_source("total, internal")?,
                krs_syntax::ShorthandItem::from_item(&syn::parse_str(source)?)
                    .expect("a shorthand item"),
            )
        },
        "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { 0 => 1, #[k::label(rest)] _ => 2 } }",
        "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { 0 => 1, #[k::label(rest,)] _ => 2 } }",
    );
    same(
        |source| krs_syntax::RawKItem::parse_tokens(tokens_from_source(source)?),
        r#""rule <k> a => b </k>""#,
        r#""rule <k> a => b </k>","#,
    );
}

#[test]
fn a_record_rest_and_malformed_commas_stay_errors() {
    for source in [
        "Ctor { a, .., }",
        "Ctor { f: e, ..t, }",
        "k::bytes!(,)",
        "f(a,,)",
        "k::matches!(t,)",
        r#"k::id!("$x",,)"#,
    ] {
        rejected(term, source);
    }
    rejected(pattern, "Ctor { a, .., }");
    rejected(
        krs_syntax::SortsDeclaration::parse_source,
        "impl Value for Int,,;",
    );
    rejected(
        krs_syntax::PrecedenceDeclaration::parse_source,
        "(A) > (B),",
    );
    rejected(
        |source| krs_syntax::parse_k_sequence_expression(tokens_from_source(source)?),
        ",",
    );
}
