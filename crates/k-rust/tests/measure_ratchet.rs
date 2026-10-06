//! Work-counter ratchets for the kompile and parser families of `k_rust_kore::measure`.
//!
//! Each family pins a bound on a checked-in input and a growth shape on a parameterised one.
//! Bounds are measured values with headroom, recorded next to the assertion; a bound that trips
//! after a deliberate algorithm change is re-pinned with the new value and the reason. Every
//! test measures a `Snapshot::delta` around the call under test, so no test depends on the
//! counters being zero when it starts. The pinned counters, Z3 checks among them, were measured
//! with native sort inference, so the whole file follows that feature.

#![cfg(feature = "z3-inference")]

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use std::{fs, path::PathBuf};

use k_rust::{
    builtin::embedded,
    definition::{Attributes, Definition, ResolvedDefinition, Sentence},
    inner::{ParsedProgram, ProgramParser, parse_rule_content, resolve_rule_bubbles},
    kast::{Label, Sort, Term},
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition, expand_macros,
        expand_macros_in_term, propagate_macro_attributes, resolve_semantic_casts,
    },
    outer::{LoadOptions, ResolvedSource, load, load_with_options},
};
use k_rust_kore::measure::{Counter, Snapshot, snapshot};

/// The snapshots pin one engine's work, while checked inference runs both engines.
fn checked_inference() -> bool {
    std::env::var("KRUST_TYPE_INFERENCE_MODE").as_deref() == Ok("checked")
}

/// The counters a run touched, for the measurement line a ratchet prints.
fn nonzero(snapshot: &Snapshot) -> Vec<(&'static str, u64)> {
    snapshot.iter().filter(|(_, value)| *value > 0).collect()
}

fn report(snapshot: &Snapshot) -> String {
    snapshot
        .iter()
        .filter(|(_, value)| *value > 0)
        .map(|(name, value)| format!("{name} = {value}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn snapshot_report(name: &str, snapshot: &Snapshot, description: &'static str) {
    insta::with_settings!({
        description => description,
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(name, report(snapshot));
    });
}

fn measured<T>(work: impl FnOnce() -> T) -> (T, Snapshot) {
    let before = snapshot();
    let result = work();
    (result, snapshot().delta(&before))
}

fn example(name: &str) -> (String, String) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    (name.to_owned(), fs::read_to_string(path).unwrap())
}

/// Compile a definition the way `krust kcompile --backend rust` does, prelude included.
fn compile(file_name: &str, source: &str, main_module: &str) -> Snapshot {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let (artifacts, delta) = measured(|| {
        let loaded = load_with_options(
            ResolvedSource::new(file_name, source),
            main_module,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![prelude],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .expect("definition should load");
        compile_loaded_definition(&loaded, CompileOptions::default())
            .expect("definition should compile")
    });
    assert!(!artifacts.definition_kore.is_empty());
    delta
}

// ---------- kompile ----------

#[test]
fn rewrite_example_compile_stays_within_the_pinned_kompile_work() {
    if checked_inference() {
        return;
    }
    let (name, source) = example("rewrite.k");
    let delta = compile(&name, &source, "REWRITE");
    eprintln!("kompile of examples/rewrite.k: {:?}", nonzero(&delta));
    snapshot_report(
        "rewrite_example_kompile_counters",
        &delta,
        "kompile of examples/rewrite.k",
    );
    assert_eq!(
        delta.get(Counter::KompileRuleBubblesParsed),
        RULE_BUBBLES_REWRITE
    );
    assert!(delta.get(Counter::KompileSentencesTransformed) <= SENTENCES_REWRITE);
    // Prediction analyses are built per grammar, never per bubble.
    assert!(
        delta.get(Counter::ParserPredictionAnalysisBuilds)
            < delta.get(Counter::KompileRuleBubblesParsed)
    );
    assert_eq!(
        delta.get(Counter::ParserGrammarBuilds),
        delta.get(Counter::ParserPredictionAnalysisBuilds),
        "every grammar built parses: no grammar is built only to seed another's scanner"
    );
}

/// The module chain of `kompile_memory.rs`: module `n` imports module `n - 1`, and every
/// generating pass adds one sentence per visible sort per module.
fn chain_definition(modules: usize) -> String {
    const SORTS_PER_MODULE: usize = 4;
    const RULES_PER_MODULE: usize = 6;
    let mut text = String::new();
    for module in 0..modules {
        text.push_str(&format!("module CHAIN-{module}\n"));
        if module == 0 {
            text.push_str("  imports INT\n");
            text.push_str("  syntax Pgm ::= \"start\"\n");
            text.push_str("  configuration <k> $PGM:Pgm </k> <n> 0 </n>\n");
        } else {
            text.push_str(&format!("  imports CHAIN-{}\n", module - 1));
        }
        for sort in 0..SORTS_PER_MODULE {
            text.push_str(&format!(
                "  syntax S{module}x{sort} ::= \"c{module}x{sort}\" | f{module}x{sort}(S{module}x{sort}, Int) [function]\n"
            ));
        }
        for rule in 0..RULES_PER_MODULE {
            let sort = rule % SORTS_PER_MODULE;
            text.push_str(&format!(
                "  rule f{module}x{sort}(c{module}x{sort}, N:Int) => c{module}x{sort} requires N ==Int {rule}\n"
            ));
        }
        text.push_str("endmodule\n\n");
    }
    text
}

#[test]
fn module_chain_compile_resolves_per_pass_and_grows_sentences_linearly() {
    if checked_inference() {
        return;
    }
    let at_5 = compile("chain.k", &chain_definition(5), "CHAIN-4");
    let at_10 = compile("chain.k", &chain_definition(10), "CHAIN-9");
    eprintln!("kompile of the 5-module chain: {:?}", nonzero(&at_5));
    eprintln!("kompile of the 10-module chain: {:?}", nonzero(&at_10));
    snapshot_report(
        "module_chain_5_kompile_counters",
        &at_5,
        "kompile of the 5-module chain",
    );
    snapshot_report(
        "module_chain_10_kompile_counters",
        &at_10,
        "kompile of the 10-module chain",
    );
    assert!(
        at_10.get(Counter::KompileProductionCatalogsBuilt)
            <= 2 * at_5.get(Counter::KompileProductionCatalogsBuilt),
        "{} catalogs at 10 modules versus {} at 5",
        at_10.get(Counter::KompileProductionCatalogsBuilt),
        at_5.get(Counter::KompileProductionCatalogsBuilt)
    );
    assert!(
        at_10.get(Counter::KompileSentenceEquivalenceChecks)
            <= 2 * at_5.get(Counter::KompileSentenceEquivalenceChecks),
        "{} equivalence checks at 10 modules versus {} at 5",
        at_10.get(Counter::KompileSentenceEquivalenceChecks),
        at_5.get(Counter::KompileSentenceEquivalenceChecks)
    );
    assert_eq!(
        at_10.get(Counter::KompileRuleBubblesParsed),
        at_5.get(Counter::KompileRuleBubblesParsed) + 5 * 6
    );
    // Generated sentences are per visible sort per module, so the chain is quadratic in modules
    // in principle; at this size the linear prelude share keeps the ratio near two.
    assert!(
        at_10.get(Counter::KompileSentencesTransformed)
            <= at_5.get(Counter::KompileSentencesTransformed) * 22 / 10,
        "{} sentences at 10 modules versus {} at 5",
        at_10.get(Counter::KompileSentencesTransformed),
        at_5.get(Counter::KompileSentencesTransformed)
    );
}

// ---------- macro expansion ----------

/// A `macro-rec` reversal of cons lists; the rule for `c` is replaced by one whose right side
/// reverses a list (`reversal_definition`).
const REVERSAL_SOURCE: &str = r#"
module MAIN
  syntax Elem ::= "a" [symbol(a)]
  syntax List ::= "nil" [symbol(nil)] | cons(Elem, List) [symbol(cons)]
                | rev(List, List) [macro-rec, symbol(rev)]
  syntax Foo ::= "c" [symbol(c)] | wrap(List) [symbol(wrap)]
  rule rev(cons(X, L), A) => rev(L, cons(X, A))
  rule rev(nil, A) => A
  rule c => wrap(nil)
endmodule
"#;

fn application(label: &str, arguments: Vec<Term>) -> Term {
    Term::Apply {
        label: Label::new(label),
        arguments,
    }
}

/// `rev(cons(a, ... cons(a, nil)), nil)` over `length` elements.
fn reversal(length: usize) -> Term {
    let mut list = application("nil", Vec::new());
    for _ in 0..length {
        list = application("cons", vec![application("a", Vec::new()), list]);
    }
    application("rev", vec![list, application("nil", Vec::new())])
}

/// `REVERSAL_SOURCE`, prepared for macro expansion as compilation prepares it, with the rule
/// `c => wrap(nil)` replaced by `c => wrap(reversal(length))`.
fn reversal_definition(length: usize) -> Definition {
    definition_wrapping(REVERSAL_SOURCE, reversal(length))
}

/// `source`, prepared for macro expansion as compilation prepares it, with the rule
/// `c => wrap(nil)` replaced by `c => wrap(right)`.
fn definition_wrapping(source: &str, right: Term) -> Definition {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let loaded = load(
        ResolvedSource::new("reversal.k", source),
        "MAIN",
        &mut resolver,
    )
    .expect("the reversal definition should load")
    .into_definition();
    let resolved = resolve_semantic_casts(&loaded).unwrap();
    let mut definition = propagate_macro_attributes(&resolved).unwrap();
    let mut right = Some(right);
    for sentence in definition
        .modules
        .iter_mut()
        .flat_map(|module| &mut module.local_sentences)
    {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = sentence.as_ref()
        else {
            continue;
        };
        let Term::Rewrite { left, .. } = body.unannotated() else {
            continue;
        };
        if !matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "c") {
            continue;
        }
        *sentence = std::sync::Arc::new(Sentence::Rule {
            body: Term::Rewrite {
                left: left.clone(),
                right: Box::new(application(
                    "wrap",
                    vec![right.take().expect("one rule for c")],
                )),
            },
            requires: requires.clone(),
            ensures: ensures.clone(),
            attributes: attributes.clone(),
        });
    }
    assert!(right.is_none(), "the rule for c should be replaced");
    definition
}

/// The work of expanding the reversal of `length` elements in a rule and in a program.
fn expand_reversal(length: usize) -> (Snapshot, Snapshot) {
    let definition = reversal_definition(length);
    let (expanded, in_rule) = measured(|| expand_macros(&definition));
    expanded.expect("the reversal in a rule should expand");
    let (expanded, in_program) = measured(|| {
        expand_macros_in_term(
            &definition,
            "MAIN",
            ParsedProgram::from_term(reversal(length)),
            &Sort::new("List"),
        )
    });
    let _expanded = expanded.expect("the reversal in a program should expand");
    (in_rule, in_program)
}

/// A `macro-rec` rule that carries its arguments along rewrites n times over a list of n
/// elements; each result is the right side around the two bindings, which were expanded with
/// the subject and hold no macro application, so the terms expansion visits grow linearly in
/// n. Re-expanding the bindings of every result makes them grow with n squared.
#[test]
fn recursive_macro_expansion_visits_grow_linearly() {
    let (rule_at_100, program_at_100) = expand_reversal(100);
    let (rule_at_200, program_at_200) = expand_reversal(200);
    eprintln!("reversal of 100 in a rule: {:?}", nonzero(&rule_at_100));
    eprintln!("reversal of 200 in a rule: {:?}", nonzero(&rule_at_200));
    eprintln!(
        "reversal of 100 in a program: {:?}",
        nonzero(&program_at_100)
    );
    eprintln!(
        "reversal of 200 in a program: {:?}",
        nonzero(&program_at_200)
    );
    for (length, rule, program) in [
        (100, &rule_at_100, &program_at_100),
        (200, &rule_at_200, &program_at_200),
    ] {
        // n rewrites by the recursive rule and one by the base rule.
        assert_eq!(rule.get(Counter::KompileMacroApplications), length + 1);
        assert_eq!(program.get(Counter::KompileMacroApplications), length + 1);
        // Measured 4n + 8 in the rule (the definition's other rules included) and 4n + 3 in
        // the program.
        for delta in [rule, program] {
            assert!(
                delta.get(Counter::KompileMacroExpansionVisits) <= 5 * length + 16,
                "{} expansion visits for {length} elements",
                delta.get(Counter::KompileMacroExpansionVisits)
            );
        }
    }
    for (at_100, at_200) in [
        (&rule_at_100, &rule_at_200),
        (&program_at_100, &program_at_200),
    ] {
        assert!(
            at_200.get(Counter::KompileMacroExpansionVisits)
                <= 2 * at_100.get(Counter::KompileMacroExpansionVisits) + 16,
            "{} expansion visits at 200 elements versus {} at 100",
            at_200.get(Counter::KompileMacroExpansionVisits),
            at_100.get(Counter::KompileMacroExpansionVisits)
        );
    }
}

/// Two `macro-rec` recursions over cons lists that carry a list of n elements along: `rev`
/// reverses it into an accumulator (the subject's depth falls and then rises), and `drop` counts
/// a numeral down beside it (every subject is as deep as the list). `{parametric}` stands for an
/// optional parametric macro, whose presence makes expansion type each sentence and expand it in
/// place.
const CARRYING_SOURCE: &str = r#"
module MAIN
  syntax Elem ::= "a" [symbol(a)]
  syntax List ::= "nil" [symbol(nil)] | cons(Elem, List) [symbol(cons)]
                | rev(List, List) [macro-rec, symbol(rev)]
                | drop(List, Nat) [macro-rec, symbol(drop)]
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Foo ::= "c" [symbol(c)] | wrap(List) [symbol(wrap)]
  {parametric}
  rule rev(cons(X, L), A) => rev(L, cons(X, A))
  rule rev(nil, A) => A
  rule drop(L, s(N)) => drop(L, N)
  rule drop(L, z) => L
  rule c => wrap(nil)
endmodule
"#;

/// `drop(cons(a, ... cons(a, nil)), s(... s(z)))` over `length` elements and `length / 2`
/// successors.
fn countdown(length: usize) -> Term {
    let Term::Apply { mut arguments, .. } = reversal(length) else {
        unreachable!("a reversal is an application")
    };
    let mut numeral = application("z", Vec::new());
    for _ in 0..length / 2 {
        numeral = application("s", vec![numeral]);
    }
    arguments[1] = numeral;
    application("drop", arguments)
}

/// The work of expanding `input` in a rule and as a program of `CARRYING_SOURCE`, with a
/// parametric macro in the module when `typed`.
fn expand_carrying(input: &Term, typed: bool) -> (Snapshot, Snapshot) {
    let parametric = if typed {
        "syntax {S} S ::= idm(S) [macro, symbol(idm)]\n  rule idm(X) => X"
    } else {
        ""
    };
    let source = CARRYING_SOURCE.replace("{parametric}", parametric);
    let definition = definition_wrapping(&source, input.clone());
    let (expanded, in_rule) = measured(|| expand_macros(&definition));
    expanded.expect("the recursion in a rule should expand");
    let (expanded, in_program) = measured(|| {
        expand_macros_in_term(
            &definition,
            "MAIN",
            ParsedProgram::from_term(input.clone()),
            &Sort::new("List"),
        )
    });
    let _expanded = expanded.expect("the recursion in a program should expand");
    (in_rule, in_program)
}

/// The work counters of `expand_carrying` for both recursions at `length` elements, with
/// their names and the number of rewrites each makes.
fn carrying_work(length: usize, typed: bool) -> Vec<(String, usize, Snapshot)> {
    let mut work = Vec::new();
    for (name, input, rewrites) in [
        ("rev", reversal(length), length + 1),
        ("drop", countdown(length), length / 2 + 1),
    ] {
        let (in_rule, in_program) = expand_carrying(&input, typed);
        work.push((format!("{name} of {length} in a rule"), rewrites, in_rule));
        work.push((
            format!("{name} of {length} in a program"),
            rewrites,
            in_program,
        ));
    }
    work
}

/// Asserts that every counter of `counters` grows at most linearly from 100 to 200 elements in
/// each of `carrying_work`'s expansions, and stays within `per_element` per element plus
/// `slack`; the subject walks, copies of a chain's checkpoint at its powers of two and
/// comparisons with them, stay within twice the binary logarithm of the rewrites plus `slack`.
fn assert_carrying_work_is_linear(typed: bool, counters: &[(Counter, usize)], slack: usize) {
    let at_100 = carrying_work(100, typed);
    let at_200 = carrying_work(200, typed);
    for (name, rewrites, delta) in at_100.iter().chain(&at_200) {
        eprintln!("{name}: {:?}", nonzero(delta));
        assert_eq!(
            delta.get(Counter::KompileMacroApplications),
            *rewrites as u64,
            "{name}"
        );
        let length = if name.contains(" of 100 ") { 100 } else { 200 };
        for (counter, per_element) in counters {
            assert!(
                delta.get(*counter) <= (per_element * length + slack) as u64,
                "{name}: {} = {}",
                counter.name(),
                delta.get(*counter)
            );
        }
        let logarithm = usize::BITS - rewrites.leading_zeros();
        assert!(
            delta.get(Counter::KompileMacroSubjectWalks) <= u64::from(2 * logarithm) + 4,
            "{name}: {} subject walks",
            delta.get(Counter::KompileMacroSubjectWalks)
        );
    }
    for ((name, _, at_100), (_, _, at_200)) in at_100.iter().zip(&at_200) {
        for (counter, _) in counters {
            assert!(
                at_200.get(*counter) <= 2 * at_100.get(*counter) + slack as u64,
                "{name}: {} = {} at 200 elements",
                counter.name(),
                at_200.get(*counter)
            );
        }
    }
}

/// A `macro-rec` rewrite reads the depths of its subject, result and bindings from what the
/// expansion that built them recorded, and compares a subject with the chain's checkpoint only
/// when their recorded fingerprints agree, so the nodes walked to measure terms grow linearly in
/// n and the subject walks logarithmically. Measuring the bindings of every rewrite makes the
/// measured nodes grow with n squared, and comparing every equally deep subject makes the
/// countdown walk its subject on every rewrite.
#[test]
fn recursive_macro_rewrites_measure_and_compare_linearly() {
    // Measured 6n + 61 nodes (rev) and 7.5n + 61 (drop) in a rule and 10 fewer in a program:
    // three depth measurements of the input, for the stack the expansion is given and for its
    // growth allowance. Subject walks: 5 to 7, the checkpoints and no comparison.
    assert_carrying_work_is_linear(false, &[(Counter::KompileMacroMeasuredNodes, 8)], 64);
}

/// The in-place expansion of a sentence with a parametric macro head keeps the settled parts of
/// its input and of each rewrite's result as they are, so it visits only what lies above a
/// macro application, and it records depths and fingerprints as the expansion without a
/// parametric head does; so the terms it visits and the nodes it walks to measure terms grow
/// linearly in n, and it copies no subject but at the chain's checkpoints. Re-expanding the
/// bindings of every rewrite makes the visits grow with n squared, and copying each visited
/// term to try its rules makes a subject walk of every visit.
#[test]
fn typed_recursive_macro_expansion_work_grows_linearly() {
    // Measured n + 3 visits (rev; 3 for drop, whose results hold only settled bindings), and
    // 8n + 75 (rev) and 10n + 75 (drop) measured nodes: the untyped path's measurements plus
    // the walk that finds the settled parts of each sentence or program. Subject walks: 5 to
    // 7, as without a parametric head.
    assert_carrying_work_is_linear(
        true,
        &[
            (Counter::KompileMacroExpansionVisits, 2),
            (Counter::KompileMacroMeasuredNodes, 11),
        ],
        64,
    );
}

// ---------- parser ----------

/// Parse the casted left-associative chain `x:S + x:S + ... + x:S => x` as a rule.
fn parse_casted_chain(operands: usize) -> Snapshot {
    let parsed = k_rust::outer::parse(
        "chain.k",
        r#"
        module MAIN
          syntax S ::= "x" [symbol(x)]
          syntax S ::= S "+" S [left, symbol(plus)]
        endmodule
        "#,
    )
    .unwrap();
    let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let chain = std::iter::repeat_n("x:S", operands)
        .collect::<Vec<_>>()
        .join("+");
    let (sentence, delta) = measured(|| {
        parse_rule_content(
            &resolved,
            "MAIN",
            &format!("{chain} => x"),
            Attributes::default(),
        )
    });
    sentence.expect("casted chain should parse");
    delta
}

/// Parse the plain left-associative chain `x + x + ... + x` as a program of the same grammar.
fn parse_program_chain(operands: usize) -> Snapshot {
    let parsed = k_rust::outer::parse(
        "chain.k",
        r#"
        module MAIN
          syntax S ::= "x" [symbol(x)]
          syntax S ::= S "+" S [left, symbol(plus)]
        endmodule
        "#,
    )
    .unwrap();
    let definition = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let parser = ProgramParser::new(&definition, "MAIN").unwrap();
    let chain = std::iter::repeat_n("x", operands)
        .collect::<Vec<_>>()
        .join("+");
    let (term, delta) = measured(|| parser.parse(&Sort::new("S"), &chain));
    let _ = term.expect("program chain should parse");
    delta
}

#[test]
fn program_chain_parse_work_grows_at_most_quadratically() {
    let at_15 = parse_program_chain(15);
    let at_30 = parse_program_chain(30);
    eprintln!("program chain of 15: {:?}", nonzero(&at_15));
    eprintln!("program chain of 30: {:?}", nonzero(&at_30));
    assert_eq!(at_15.get(Counter::ParserParseAttempts), 1);
    assert!(at_30.get(Counter::ParserChartCompletionCandidates) <= 2 * 30 * 30);
    // The quadratic contract of the inline casted-chain test with slack 1.25.
    for counter in [
        Counter::ParserChartCompletionCandidates,
        Counter::ParserChartAgendaPops,
        Counter::ParserChartDerivationsRead,
        Counter::ParserChartAddCalls,
    ] {
        assert!(
            at_30.get(counter) <= 5 * at_15.get(counter),
            "{}: {} at 30 operands versus {} at 15",
            counter.name(),
            at_30.get(counter),
            at_15.get(counter)
        );
    }
}

#[test]
fn scanner_winner_work_is_bounded_by_input_positions() {
    let operands = 15;
    let delta = parse_program_chain(operands);
    let input_bytes = 2 * operands - 1;
    assert!(
        delta.get(Counter::ParserScannerWinnerComputations) <= input_bytes as u64 + 1,
        "{} winner computations for {input_bytes} input bytes",
        delta.get(Counter::ParserScannerWinnerComputations)
    );
}

/// A standalone rule is parsed with its module's rule grammar alone, built once.
#[test]
fn casted_rule_chain_builds_its_rule_grammar_once() {
    let delta = parse_casted_chain(15);
    assert_eq!(delta.get(Counter::ParserGrammarBuilds), 1);
}

#[test]
fn indexed_prediction_preserves_the_casted_chain_counts() {
    if checked_inference() {
        return;
    }
    let delta = parse_casted_chain(15);
    snapshot_report(
        "casted_chain_15_parser_counters",
        &delta,
        "casted rule chain parser counters",
    );
}

#[test]
fn casted_rule_chain_parse_stays_within_the_pinned_chart_work() {
    let operands = 15;
    let delta = parse_casted_chain(operands);
    eprintln!("casted chain of {operands}: {:?}", nonzero(&delta));
    assert_eq!(delta.get(Counter::ParserParseAttempts), 1);
    assert!(delta.get(Counter::ParserChartCompletionCandidates) <= COMPLETION_CANDIDATES_CHAIN_15);
    assert!(delta.get(Counter::ParserChartAgendaPops) <= AGENDA_POPS_CHAIN_15);
    assert!(
        delta.get(Counter::ParserChartRevisitPops) <= delta.get(Counter::ParserChartAgendaPops)
    );
    assert!(delta.get(Counter::ParserChartStateChanges) <= delta.get(Counter::ParserChartAddCalls));
    assert!(delta.get(Counter::ParserUnpackedNodes) <= UNPACKED_NODES_CHAIN_15);
}

#[test]
fn casted_rule_chain_priority_work_is_bounded_by_completion_candidates() {
    let delta = parse_casted_chain(15);
    assert!(
        delta.get(Counter::ParserPackedPriorityComputations)
            <= 2 * delta.get(Counter::ParserChartCompletionCandidates),
        "{} priority computations for {} completion candidates",
        delta.get(Counter::ParserPackedPriorityComputations),
        delta.get(Counter::ParserChartCompletionCandidates)
    );
}

#[test]
fn casted_rule_chain_parse_work_grows_at_most_cubically() {
    let at_15 = parse_casted_chain(15);
    let at_30 = parse_casted_chain(30);
    // Under the full rule grammar (casts, K sequences, the sort lattice) the chain is no longer
    // quadratic: 1553 to 10293 completion candidates measured, a factor 6.6; Earley's cubic
    // bound is the contract here.
    for counter in [
        Counter::ParserChartCompletionCandidates,
        Counter::ParserChartAgendaPops,
        Counter::ParserChartDerivationsRead,
        Counter::ParserChartAddCalls,
    ] {
        assert!(
            at_30.get(counter) <= 8 * at_15.get(counter),
            "{}: {} at 30 operands versus {} at 15",
            counter.name(),
            at_30.get(counter),
            at_15.get(counter)
        );
    }
}

/// A definition whose `bubbles` rules each parse `1 + 2 * 3` without priorities: the forest is
/// ambiguous, so sort inference runs through Z3 before `avoid` selects the parse.
fn ambiguous_definition(bubbles: usize) -> k_rust::definition::Definition {
    let rules = "rule 1 + 2 * 3 => 1\n".repeat(bubbles);
    let parsed = k_rust::outer::parse(
        "ambiguous.k",
        &format!(
            r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Exp ::= Int
              syntax Exp ::= Exp "+" Exp [symbol(plus), avoid]
              syntax Exp ::= Exp "*" Exp [symbol(times)]
              {rules}
            endmodule
            "#
        ),
    )
    .unwrap();
    k_rust::outer::lower(&parsed, "MAIN").unwrap()
}

fn resolve_ambiguous_bubbles(bubbles: usize) -> Snapshot {
    let definition = ambiguous_definition(bubbles);
    let (resolved, delta) = measured(|| resolve_rule_bubbles(&definition));
    resolved.expect("ambiguous rules should resolve");
    assert_eq!(delta.get(Counter::KompileRuleBubblesParsed), bubbles as u64);
    delta
}

#[test]
fn ambiguous_bubble_stays_within_the_pinned_z3_checks() {
    let delta = resolve_ambiguous_bubbles(1);
    eprintln!("one ambiguous bubble: {:?}", nonzero(&delta));
    assert!(delta.get(Counter::ParserZ3Checks) >= 1);
    assert!(delta.get(Counter::ParserZ3Checks) <= Z3_CHECKS_AMBIGUOUS_BUBBLE);
}

#[test]
fn z3_checks_are_paid_once_per_bubble() {
    let one = resolve_ambiguous_bubbles(1);
    let four = resolve_ambiguous_bubbles(4);
    assert_eq!(
        four.get(Counter::ParserZ3Checks),
        4 * one.get(Counter::ParserZ3Checks)
    );
    // The prediction analysis is built per grammar, not per bubble.
    assert_eq!(
        four.get(Counter::ParserPredictionAnalysisBuilds),
        one.get(Counter::ParserPredictionAnalysisBuilds)
    );
    assert!(four.get(Counter::ParserZ3EncodingBuilds) <= 1);
}

// ---------- pinned values ----------
// Measured at the commit that added this file, then rounded up by about 10 %. The measured
// values are in that commit's message; re-pin in a commit that says why the value moved.

/// `examples/rewrite.k`: its one rule plus the prelude bubbles reachable from REWRITE.
const RULE_BUBBLES_REWRITE: u64 = 198;
/// `examples/rewrite.k`: 2091 sentences after transformation.
const SENTENCES_REWRITE: u64 = 2300;
/// Casted rule chain of 15 operands: 1553 completion candidates.
const COMPLETION_CANDIDATES_CHAIN_15: u64 = 1710;
/// Casted rule chain of 15 operands: 2990 agenda pops.
const AGENDA_POPS_CHAIN_15: u64 = 3290;
/// Casted rule chain of 15 operands: 47 unpacked nodes.
const UNPACKED_NODES_CHAIN_15: u64 = 52;
/// One ambiguous `1 + 2 * 3` bubble: 10 Z3 checks (8 before the admissible parameter vectors
/// were chosen per inclusion-maximal set of live ambiguity readings, which costs a check
/// that no larger live set exists and one that no other maximal set does).
const Z3_CHECKS_AMBIGUOUS_BUBBLE: u64 = 11;
