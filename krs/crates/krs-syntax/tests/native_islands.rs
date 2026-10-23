//! One pattern grammar: a pattern outside `k::term![..]` reads every
//! compiler-owned island the wrapper's payload reads (`k::fragment!`,
//! `k::bytes!`, `k::id!`, `k::anonymous!`, `k::lexeme!`, `k::or_bool!`, and
//! `k::rewrite!` in a single-body rule's subject), at any depth, and a fn
//! subject's record may end in `..`. The wrapper changes the parser, not what
//! the pattern denotes, so each native subject builds the tree, nodes,
//! bindings, provenance, and reference candidates of its wrapped twin.

use std::fmt::Write as _;

use krs_syntax::{KrsSyntax, ProvenanceRole, RuleBlock, RuleItem, SyntaxErrorKind, TermTree};

/// The wrapped twin of a fn whose subject is `subject`: the native source is
/// padded where the wrapper stands, so both spell every token at the same
/// byte offset and their spans compare equal.
fn twins(template: &str, subject: &str) -> (String, String) {
    (
        template.replace("SUBJECT", &format!("         {subject} ")),
        template.replace("SUBJECT", &format!("k::term![{subject}]")),
    )
}

/// Rewrites every `bytes(a..b)` span of `text` relative to `base`: each
/// parse places its source at its own offset of one shared source map.
fn relative_spans(text: &str, base: usize) -> String {
    let mut output = String::new();
    let mut rest = text;
    while let Some(start) = rest.find("bytes(") {
        output.push_str(&rest[..start + "bytes(".len()]);
        rest = &rest[start + "bytes(".len()..];
        let end = rest.find(')').unwrap();
        let (low, high) = rest[..end].split_once("..").unwrap();
        let shift = |offset: &str| offset.parse::<usize>().unwrap() - base;
        write!(output, "{}..{}", shift(low), shift(high)).unwrap();
        rest = &rest[end..];
    }
    output.push_str(rest);
    output
}

/// Everything a rule item derives from its subject, except the whole
/// subject's own range (which includes the wrapper), with spans relative to
/// the item's name.
fn observed(rule: &RuleItem) -> Vec<String> {
    let pattern = &rule.parameter().pattern;
    let anchors = rule.full_provenance().unwrap();
    let declaration = format!("{:?}", anchors[0]);
    assert!(declaration.contains("RuleDeclaration"), "{declaration}");
    let base = declaration
        .split_once("bytes(")
        .and_then(|(_, tail)| tail.split_once(".."))
        .map(|(offset, _)| offset.parse::<usize>().unwrap())
        .unwrap();
    let anchors = anchors
        .into_iter()
        .filter(|anchor| anchor.role() != ProvenanceRole::RulePattern)
        .map(|anchor| format!("{anchor:?}"))
        .collect::<Vec<_>>();
    [
        format!("{:?}", rule.subject_tree()),
        format!("{:?}", pattern.nodes()),
        format!("{:?}", pattern.bindings()),
        format!("{anchors:?}"),
        format!("{:?}", rule.reference_candidates().unwrap()),
        format!("{:?}", rule.term_reference_candidates().unwrap()),
    ]
    .iter()
    .map(|text| relative_spans(text, base))
    .collect()
}

#[test]
fn nested_islands_build_the_tree_of_their_wrapped_twin() {
    const EQUATION: &str = "#[k::equation] fn f(SUBJECT: Term<E>) -> Term<E> { G() }";
    for subject in [
        // A fragment as a constructor argument, with `..`, a negative literal
        // inside it and one after it: the literals keep their order.
        "F(k::fragment![Frame { pc: -1, gas: g, .. }], -2)",
        // Every child named, no `..`.
        "F(k::fragment![Frame { pc, gas: 3 }])",
        // An alias naming a fragment.
        "F(f @ k::fragment![Frame { pc: p, .. }], p)",
        // A fragment in a record field, and a record rest in a fn subject.
        "R { a: k::fragment![Frame { pc: p, .. }], .. }",
        "R { a: p, .. }",
        // A fragment nested in a fragment's child.
        "F(k::fragment![Outer { inner: k::fragment![Frame { pc: p, .. }], .. }])",
        // The literal islands.
        "F(k::bytes!(b\"x\"), k::id!(\"$a\"), k::lexeme!(Name, \"x\"))",
        "F(k::anonymous!(Int, \"_N\"), n)",
        // A `|` alternative of islands.
        "F(k::bytes!(b\"x\") | k::bytes!(b\"y\"))",
        // `k::or_bool!` parses as the term grammar parses it; sort analysis
        // rejects it in a pattern.
        "F(k::or_bool!(a, b))",
        // A list element.
        "F(list::concat(list::item(k::fragment![Frame { pc: p, .. }]), s))",
    ] {
        let (native, wrapped) = twins(EQUATION, subject);
        let native = RuleItem::parse_equation_source(&native)
            .unwrap_or_else(|error| panic!("{subject}: {error}"));
        let wrapped = RuleItem::parse_equation_source(&wrapped).unwrap();
        assert_eq!(observed(&native), observed(&wrapped), "{subject}");
    }
}

#[test]
fn a_native_rewrite_in_a_single_body_rule_is_its_wrapped_twin() {
    const RULE: &str = "#[k::rule] fn unmark(SUBJECT: Term<Exp>) {}";
    for subject in [
        "Pair(k::rewrite!(Marked(v) => v), _)",
        "Cmd::Held { saved: k::rewrite!(x => Cmd::Bump()) }",
        "Pair(k::rewrite!(Marked(-1) => Done()), -2)",
    ] {
        let (native, wrapped) = twins(RULE, subject);
        let native =
            RuleItem::parse_source(&native).unwrap_or_else(|error| panic!("{subject}: {error}"));
        let wrapped = RuleItem::parse_source(&wrapped).unwrap();
        assert!(native.result().is_none(), "{subject}");
        assert_eq!(observed(&native), observed(&wrapped), "{subject}");
    }
    // A rewrite still belongs to a single-body rule: one with a result gets
    // that reason, as its wrapped twin does.
    let error = RuleItem::parse_source(
        "#[k::rule] fn f(Pair(k::rewrite!(a => b), c): Term<Exp>) -> Term<Exp> { c }",
    )
    .unwrap_err();
    assert!(
        matches!(error.kind(), SyntaxErrorKind::InvalidLocalRewrite { reason } if reason.contains("a rule with a result")),
        "{error}"
    );
}

#[test]
fn a_readable_value_reads_islands_at_its_root_and_below() {
    let block = RuleBlock::parse_source(
        "for Machine;
         restore: {
             k: [Restore(), ..],
             stack: list::concat(list::item(f @ k::fragment![Frame { pc: p, .. }]), s),
             frame: k::fragment![Frame { pc: q, gas: g }],
             tag: k::bytes!(b\"y\"),
         } => {
             k: [..],
             stack: s,
             frame: Frame { pc: int::add(p, q), ..f },
         };
         held: {
             k: [Held { saved: k::fragment![Frame { pc: p, .. }] }, ..],
         } => {
             k: [p, ..],
         };",
    )
    .unwrap();
    assert_eq!(block.clauses().len(), 2);
}

#[test]
fn islands_that_are_not_patterns_keep_their_reasons() {
    let message = |source: &str| match RuleBlock::parse_source(source) {
        Ok(_) => panic!("{source} parsed"),
        Err(error) => error.to_string(),
    };
    for (value, expected) in [
        ("Wrap(k::matches!(x, Foo()))", "Bool test"),
        ("Wrap(matches!(x, Foo()))", "did you mean `k::matches!`?"),
        ("Wrap(k::is!(Int, x))", "cannot be matched"),
        ("Wrap(k::project!(Int, x))", "cannot be matched"),
        ("k::bits!(\"0000 00xx\")", "`k::bits!` is a pattern"),
        ("Wrap(k::rewrite!(a => b))", "reference-only"),
        ("Wrap(other![x])", "macros are not terms unless"),
    ] {
        let source =
            format!("for Machine; r: {{ k: [Go(), ..], pc: {value} }} => {{ k: [..], pc: 0 }};");
        let error = message(&source);
        assert!(
            error.contains(expected),
            "{value}: expected {expected:?}, got {error}"
        );
    }
    // A fn subject's root is the matched constructor or function, never an
    // island.
    let error = RuleItem::parse_equation_source(
        "#[k::equation] fn f(k::fragment![Frame { pc: p, .. }]: Term<E>) -> Term<E> { G() }",
    )
    .unwrap_err();
    assert!(
        matches!(error.kind(), SyntaxErrorKind::UnexpectedMacro { .. }),
        "{error}"
    );
}

#[test]
fn a_fragment_names_a_child_or_ends_in_rest() {
    let error = RuleItem::parse_equation_source(
        "#[k::equation] fn f(F(k::fragment![Frame {}]): Term<E>) -> Term<E> { G() }",
    )
    .unwrap_err();
    assert!(
        error.to_string().contains("at least one child field"),
        "{error}"
    );
    let rule = RuleItem::parse_equation_source(
        "#[k::equation] fn f(F(k::fragment![Frame { .. }]): Term<E>) -> Term<E> { G() }",
    )
    .unwrap();
    let TermTree::Application(application) = rule.subject_tree() else {
        panic!("the subject is `F(..)`");
    };
    assert!(matches!(
        &application.arguments().positional().unwrap()[0],
        TermTree::Cell(cell) if cell.is_open()
    ));
}
