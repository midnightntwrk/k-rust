//! `k::patterns!` (FB-49): each step and each `unless` is the readable claim whose subject is
//! the part's set of states; the clause's conditions go to the earliest step that binds what
//! they read; and the block refuses what a pattern cannot mean.

use krs_syntax::{KrsSyntax as _, PatternBlock};

const E1: &str = r"
for Machine;
use Step::*;

/// dispatch-request: VBlank arrives inside a timer dispatch.
#[k::cases(&quot;scheduled/dispatch-request&quot;)]
#[k::requires(before & 0x1F == 0x04)]
#[k::requires(after & 0x05 == 0x05)]
dispatch_request: {
    k: [Dispatch, ..],
    memory: { IF -> before, .. },
} => unless({ k: [Boundary, ..] }) {
    k: [SelectVector(_), ..],
    memory: { IF -> after, .. },
};
";

fn parse(source: &str) -> PatternBlock {
    PatternBlock::parse_source(&source.replace("&quot;", "\""))
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

fn refusal(clause: &str) -> String {
    let source = format!("for Machine; {clause}").replace("&quot;", "\"");
    let error = PatternBlock::parse_source(&source)
        .err()
        .unwrap_or_else(|| panic!("`{clause}` is refused"));
    format!("{} {error}", error.kind().code().as_str())
}

#[test]
fn every_part_is_a_claim_carrying_the_part_it_is() {
    let block = parse(E1);
    let [pattern] = block.patterns() else {
        panic!("one pattern");
    };
    assert_eq!(pattern.id(), "dispatch-request");
    let parts = pattern
        .parts()
        .iter()
        .map(|part| (part.step(), part.unless(), part.binders().to_vec()))
        .collect::<Vec<_>>();
    assert_eq!(
        parts,
        [
            (1, false, vec!["before".to_owned()]),
            (2, true, Vec::new()),
            (2, false, vec!["after".to_owned()]),
        ]
    );
    let clauses = block.clauses();
    assert_eq!(clauses.len(), 3);
    let names = clauses
        .iter()
        .map(|clause| clause.rule().item().sig.ident.to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            "dispatch_request",
            "dispatch_request__unless2",
            "dispatch_request__step2"
        ]
    );
    for clause in clauses {
        let pattern = clause.pattern().expect("each part carries its pattern");
        assert_eq!(pattern.id, "dispatch-request");
        assert_eq!(
            pattern.note.as_deref(),
            Some("dispatch-request: VBlank arrives inside a timer dispatch.")
        );
        assert_eq!(
            pattern.programs.as_deref(),
            Some(&["scheduled/dispatch-request".to_owned()][..])
        );
        assert!(clause.claim().is_some());
    }
    // Each condition is at the step that binds what it reads.
    assert!(clauses[0].rule().requires().is_some());
    assert!(clauses[1].rule().requires().is_none());
    assert!(clauses[2].rule().requires().is_some());
}

#[test]
fn a_condition_over_two_steps_is_placed_at_the_later_and_imports_the_earlier_binder() {
    let block = parse(
        "for Machine;
        #[k::requires(d2 == d + 1 && d > 0)]
        call: { depth: d } => unless({ k: [Store(_), ..] }, requires(d == 3)) { depth: d2 };",
    );
    let [pattern] = block.patterns() else {
        panic!("one pattern");
    };
    let parts = pattern
        .parts()
        .iter()
        .map(|part| (part.unless(), part.imports().to_vec()))
        .collect::<Vec<_>>();
    // `d > 0` reads step 1's binder only, `d2 == d + 1` both steps', and the `unless`'s own
    // condition reads step 1's `d`.
    assert_eq!(
        parts,
        [
            (false, Vec::new()),
            (true, vec!["d".to_owned()]),
            (false, vec!["d".to_owned()]),
        ]
    );
    let clauses = block.clauses();
    assert!(clauses[0].rule().requires().is_some());
    assert!(clauses[1].rule().requires().is_some());
    assert!(clauses[2].rule().requires().is_some());
    assert!(
        clauses[2].bindings().iter().any(|binding| binding == "d"),
        "step 2 declares the import"
    );
}

#[test]
fn a_shared_binder_is_one_name_in_every_step() {
    let block = parse(
        "for Machine;
        #[k::cases(&quot;cases/halt-bug-rst&quot;)]
        halt_bug_rst: { k: [Fetch, ..], halt_bug: true, pc: p } => { k: [Fetch, ..], halt_bug: false, pc: p };",
    );
    let [pattern] = block.patterns() else {
        panic!("one pattern");
    };
    assert!(
        pattern
            .parts()
            .iter()
            .all(|part| part.binders() == ["p".to_owned()])
    );
}

#[test]
fn a_record_s_anonymous_rest_is_the_cells_it_does_not_name() {
    let with = parse("for Machine; p: { k: [Go, ..], .. };");
    let without = parse("for Machine; p: { k: [Go, ..] };");
    assert_eq!(
        with.clauses()[0].bindings(),
        without.clauses()[0].bindings()
    );
    assert_eq!(
        with.clauses()[0].extras().len(),
        without.clauses()[0].extras().len()
    );
}

#[test]
fn a_pattern_refuses_what_it_cannot_mean() {
    for (clause, expected) in [
        (
            "p: unless({ k: [Go, ..] }) { k: [Go, ..] };",
            "krs::syntax::invalid-pattern step 1 has no arrow before it",
        ),
        (
            "#[k::cases(&quot;a&quot;)] #[k::cases(&quot;b&quot;)] p: { k: [Go, ..] };",
            "krs::syntax::invalid-pattern a pattern carries one `#[k::cases(..)]`",
        ),
        (
            "#[k::cases()] p: { k: [Go, ..] };",
            "krs::syntax::invalid-pattern `#[k::cases()]` names no program",
        ),
        (
            "#[k::cases(&quot;a&quot;, &quot;a&quot;)] p: { k: [Go, ..] };",
            "names the program `a` twice",
        ),
        (
            "#[k::cases(&quot;&quot;)] p: { k: [Go, ..] };",
            "a program id is a nonempty string",
        ),
        ("#[k::cases(a)] p: { k: [Go, ..] };", "each a string"),
        (
            "#[k::expect(no)] #[k::expect(no)] p: { k: [Go, ..] };",
            "one `#[k::expect(..)]`",
        ),
        (
            "#[k::expect(yes)] p: { k: [Go, ..] };",
            "so `no` is its one value",
        ),
        (
            "#[k::cases(&quot;a&quot;)] #[k::expect(no)] p: { k: [Go, ..] };",
            "contradicts `#[k::expect(no)]`",
        ),
        (
            "#[k::claim(one_path)] p: { k: [Go, ..] };",
            "a pattern is no claim",
        ),
        (
            "#[k::rule(owise)] p: { k: [Go, ..] };",
            "a pattern is no rule",
        ),
        (
            "#[k::exists(x: Int)] p: { k: [Go, ..] };",
            "nothing exists in it",
        ),
        (
            "#[k::ensures(true)] p: { k: [Go, ..] };",
            "nothing is ensured",
        ),
        (
            "#[k::fresh(n: Int)] p: { k: [Go, ..] };",
            "draws no fresh value",
        ),
        (
            "#[k::priority(3)] p: { k: [Go, ..] };",
            "a pattern clause takes `#[k::cases(..)]`",
        ),
        (
            "p: { k: [Go, ..], rest @ .. };",
            "krs::syntax::invalid-pattern `rest @ ..` names a record's rest",
        ),
        (
            "p: { k: [Go, ..] } => unless({ pc: x }) { pc: x };",
            "krs::syntax::invalid-pattern `x` is named by this `unless` and by another part",
        ),
        (
            "p: { k: [Go, ..] } => unless({ pc: x }) { k: [Go, ..] } => unless({ pc: x }) { k: [Go, ..] };",
            "`x` is named by this `unless` and by another part",
        ),
        (
            "p: { k: [Go, ..] } => unless({ k: [Go, ..] }, ensures(true)) { k: [Go, ..] };",
            "an `unless` is `unless(record)` or `unless(record, requires(condition))`",
        ),
        ("p: { bus: [.., ..] };", "`[.., ..]` names no element"),
        ("p: Go();", "a pattern's step is a cell record"),
        (
            "p: { k: [Go, ..] }; p: { k: [Go, ..] };",
            "duplicate readable rule clause `p`",
        ),
        (
            "#[k::requires(k::matches!(x, Go()))] p: { pc: x };",
            "krs::analysis::pattern-helper a pattern may call only the specification's functions",
        ),
        (
            "p: { pc: { let y = 1; y } };",
            "krs::analysis::pattern-helper",
        ),
        (
            "p: { pc: x } => unless({ pc: y }, requires(k::matches!(y, Go()))) { pc: x };",
            "krs::analysis::pattern-helper",
        ),
    ] {
        let error = refusal(clause);
        assert!(error.contains(expected), "{clause}: {error}");
    }
}

#[test]
fn an_empty_block_is_refused_as_every_empty_readable_block_is() {
    let error = PatternBlock::parse_source("for Machine;").unwrap_err();
    assert!(
        error
            .to_string()
            .contains("a readable rule block requires at least one clause"),
        "{error}"
    );
}

#[test]
fn an_unless_binder_shared_with_an_earlier_step_is_that_step_s_value() {
    let block = parse("for Machine; p: { pc: x } => unless({ pc: x }) { k: [Go, ..] };");
    let [pattern] = block.patterns() else {
        panic!("one pattern");
    };
    assert_eq!(pattern.parts()[1].binders(), ["x".to_owned()]);
}

#[test]
fn a_step_s_list_holds_several_rests_and_every_other_sentence_one() {
    // A step's list with several rests reads, at the cell and nested in a value.
    let block = parse(
        "for Machine;
        p: { bus: [.., Write(1, v), l @ .., Read(1, v), ..] } => unless({ bus: [.., x, ..] }) { stack: [Pair { items: [.., v, ..] }, ..] };",
    );
    let [pattern] = block.patterns() else {
        panic!("one pattern");
    };
    assert_eq!(
        pattern.parts()[0].binders(),
        ["v".to_owned(), "l".to_owned()]
    );
    // An equation table keeps one rest, before and after a patterns block (a rule and a claim
    // carry the refusal to the collector, which the krs-cli witnesses show).
    for _ in 0..2 {
        let equation = krs_syntax::EquationTable::parse_source("for Last; last: [.., x, ..] => x;")
            .unwrap_err();
        assert_eq!(
            equation.kind().code().as_str(),
            "krs::syntax::invalid-list-notation",
            "{equation}"
        );
        assert!(
            equation
                .to_string()
                .contains("a list holds at most one rest"),
            "{equation}"
        );
        let _ = parse("for Machine; p: { bus: [.., x, ..] };");
    }
}

/// The authored text `anchor` spans in `source`, which is one line.
fn spanned(source: &str, anchor: &krs_syntax::ProvenanceAnchor) -> String {
    let range = anchor.range();
    let (start, end) = (range.first().start(), range.last().end());
    assert_eq!((start.line, end.line), (1, 1), "a one-line source");
    source
        .chars()
        .skip(start.column)
        .take(end.column - start.column)
        .collect()
}

/// The text of each `requires` path anchor of each part of the one-clause block `clause`, and
/// how many parts carry a condition.
fn requires_paths(clause: &str) -> (Vec<Vec<String>>, usize) {
    let source = format!("for Machine; {clause}");
    let block = parse(&source);
    let mut conditioned = 0;
    let paths = block
        .clauses()
        .iter()
        .map(|part| {
            conditioned += usize::from(part.rule().requires().is_some());
            part.descriptor_provenance()
                .unwrap()
                .iter()
                .filter(|anchor| anchor.role() == krs_syntax::ProvenanceRole::RuleRequiresPath)
                .map(|anchor| spanned(&source, anchor))
                .collect()
        })
        .collect();
    (paths, conditioned)
}

#[test]
fn a_part_s_conjuncts_are_one_requires_joined_at_authored_tokens() {
    // A part's conditions are one conjunction: each conjunct after the first is joined by an
    // `&&` anchored at one authored token, the `&&` it was split at or the `requires` that
    // wrote it, so the anchor is the same tokens whichever host parses the clause.
    for (clause, expected) in [
        (
            "#[k::requires(z >= 0x80)] #[k::requires(z < 0x100)] p: { k: [Go, ..], z };",
            vec![vec!["requires", ">=", "z", "<", "z"]],
        ),
        (
            "#[k::requires(z >= 0x80 && z < 0x100)] p: { k: [Go, ..], z };",
            vec![vec!["&&", ">=", "z", "<", "z"]],
        ),
        (
            "#[k::requires(z >= 0x80 && z < 0x100)] #[k::requires(z != 0x90)] p: { k: [Go, ..], z };",
            vec![vec!["requires", "&&", ">=", "z", "<", "z", "!=", "z"]],
        ),
    ] {
        let (paths, conditioned) = requires_paths(clause);
        assert_eq!(conditioned, 1, "{clause}");
        assert_eq!(paths, expected, "{clause}");
    }
}
