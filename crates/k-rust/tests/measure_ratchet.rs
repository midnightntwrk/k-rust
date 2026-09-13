//! Work-counter ratchets for the kompile and parser families of `k_rust_kore::measure`.
//!
//! Each family pins a bound on a checked-in input and a growth shape on a parameterised one.
//! Bounds are measured values with headroom, recorded next to the assertion; a bound that trips
//! after a deliberate algorithm change is re-pinned with the new value and the reason. Every
//! test measures a `Snapshot::delta` around the call under test, so no test depends on the
//! counters being zero when it starts. The standard prelude needs native Z3 inference, so the
//! whole file follows that feature.

#![cfg(feature = "z3-inference")]

// The counters only count in `measure` builds; the crate's own dev-dependency enables it.
const _: () = assert!(cfg!(feature = "measure"));

use std::{fs, path::PathBuf};

use k_rust::{
    builtin::embedded,
    definition::{Attributes, ResolvedDefinition},
    inner::{ProgramParser, parse_rule_content, resolve_rule_bubbles},
    kast::Sort,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_kore::measure::{Counter, Snapshot, snapshot};

/// The counters a run touched, for the measurement line a ratchet prints.
fn nonzero(snapshot: &Snapshot) -> Vec<(&'static str, u64)> {
    snapshot.iter().filter(|(_, value)| *value > 0).collect()
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
    let (name, source) = example("rewrite.k");
    let delta = compile(&name, &source, "REWRITE");
    eprintln!("kompile of examples/rewrite.k: {:?}", nonzero(&delta));
    assert!(delta.get(Counter::KompileResolveCalls) <= RESOLVE_CALLS_REWRITE);
    assert!(delta.get(Counter::KompileRebaseCalls) <= REBASE_CALLS_REWRITE);
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
    let at_5 = compile("chain.k", &chain_definition(5), "CHAIN-4");
    let at_10 = compile("chain.k", &chain_definition(10), "CHAIN-9");
    eprintln!("kompile of the 5-module chain: {:?}", nonzero(&at_5));
    eprintln!("kompile of the 10-module chain: {:?}", nonzero(&at_10));
    // Resolutions and rebases happen per pass, not per module.
    assert_eq!(
        at_10.get(Counter::KompileResolveCalls),
        at_5.get(Counter::KompileResolveCalls)
    );
    assert_eq!(
        at_10.get(Counter::KompileRebaseCalls),
        at_5.get(Counter::KompileRebaseCalls)
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
    term.expect("program chain should parse");
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
}

// ---------- pinned values ----------
// Measured at the commit that added this file, then rounded up by about 10 %. The measured
// values are in that commit's message; re-pin in a commit that says why the value moved.

/// `examples/rewrite.k`: 69 resolutions (one per pass, the same for every input).
const RESOLVE_CALLS_REWRITE: u64 = 76;
/// `examples/rewrite.k`: 11 rebases.
const REBASE_CALLS_REWRITE: u64 = 12;
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
/// One ambiguous `1 + 2 * 3` bubble: 8 Z3 checks.
const Z3_CHECKS_AMBIGUOUS_BUBBLE: u64 = 9;
